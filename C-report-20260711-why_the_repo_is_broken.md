# Why VirasoroProject no longer builds

Date: 2026-07-11

## TL;DR

The initial hypothesis — that `lakefile.toml` doesn't declare the Mathlib
dependency — is **not correct**. `lakefile.toml` does list Mathlib:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

and `lake-manifest.json` correctly locks it to a real, buildable commit
(`b9b7d0bade32b0868be794eb6a7bf9821f6c00d9`), which checks out and compiles
fine.

The actual break is unrelated to Mathlib. `lake build` fails while
fetching a *transitive* dependency, `UnicodeBasic` (pulled in via
`doc-gen4`), because the exact commit pinned in `lake-manifest.json` was
**erased from its upstream repository's history** (silently rewritten by a
force-push) after the manifest was generated. This is reproducible from a
completely fresh clone — it is not a stale-cache or local-environment
problem — and it blocks `lake build` before a single Mathlib/project file
is even compiled.

## Reproduction

```
$ lake build
info: UnicodeBasic: checking out revision 'cff8377dbe50aae42cbd04213d5b3dacf742c3ba'
error: external command 'git' exited with code 128
```

Running the equivalent `git` command by hand inside
`.lake/packages/UnicodeBasic` shows the real error Lake swallows:

```
$ git checkout cff8377dbe50aae42cbd04213d5b3dacf742c3ba
fatal: reference is not a tree: cff8377dbe50aae42cbd04213d5b3dacf742c3ba
```

## Root cause

`lakefile.toml` requires `doc-gen4` (tracking `rev = "main"`), which in
turn depends on `fgdorais/lean4-unicode-basic`. `lake-manifest.json` (both
VirasoroProject's own copy and the one baked into the `doc-gen4` commit it
locked to, `05bb841`) pins `UnicodeBasic` to commit
`cff8377dbe50aae42cbd04213d5b3dacf742c3ba` ("chore: bump toolchain to
v4.27.0-rc1 (#110)", dated 2025-12-14).

That commit is **no longer reachable from any branch** on
`github.com/fgdorais/lean4-unicode-basic`:

```
$ git merge-base --is-ancestor cff8377dbe50aae42cbd04213d5b3dacf742c3ba origin/main
# → not an ancestor
```

The upstream repo's `main` branch was rewritten at some point after
Dec 2025 (history was rebased/amended, not just fast-forwarded — the
commit's *content* survives, its *hash* doesn't). Proof: there is a
current commit, `256e9993b028465b3e183f6da5f2ab02b7236725` (same commit
message, "chore: bump toolchain to v4.27.0-rc1 (#110)"), with an
**identical tree hash** (`db9eaa85cea65b8b16c6d1ece74a58303866a61e`) to the
orphaned one, and it *is* an ancestor of current `main`. So the same
change was re-committed under a new SHA, orphaning the original.

Lake's dependency-fetch step does a plain `git fetch` (which only follows
branch refs) and then `git checkout <pinned-sha>`. A plain fetch never
retrieves a commit that isn't reachable from any ref, so the checkout of
the orphaned SHA fails outright — even though the object itself is still
individually fetchable by exact SHA from GitHub today (`git fetch origin
<sha>` succeeds; ordinary `git fetch` does not pull it in). This is a
narrow window: GitHub does not guarantee to serve unreachable objects
indefinitely, so this pin could stop resolving entirely (rather than just
resolving unreliably) at any time.

This is entirely an upstream (`lean4-unicode-basic`) history-rewrite
problem manifesting through a transitive dependency
(`doc-gen4 → UnicodeBasic`); nothing in VirasoroProject's own Lean source
or `lakefile.toml` is at fault. It also affects CI
(`.github/workflows/blueprint.yml`), since that workflow's very first
substantive step (`lake exe cache get` / `lake build VirasoroProject`)
hits the same resolution failure before anything else runs.

### Why does a docs/lint dependency block building the math library?

`doc-gen4` (API docs) and `checkdecls` (used by CI to verify blueprint
declarations exist) are real requirements — `blueprint.yml` invokes both
— so they shouldn't simply be dropped. But `lake build` resolves *all*
declared dependencies up front regardless of which target you're building,
so a break anywhere in `doc-gen4`'s dependency graph blocks building the
core `VirasoroProject` library too, even though `VirasoroProject`'s own
sources never import `doc-gen4` or `UnicodeBasic`.

## Verification of the fix

To confirm this is really the *only* blocker, I:

1. Checked reachability of every pinned revision in `lake-manifest.json`
   by fetching each one directly by SHA from its upstream remote.
   `UnicodeBasic` was the only one that required this workaround (i.e.
   the only one that isn't reachable via a normal `git fetch`); all other
   pins (including Mathlib itself) check out normally through Lake's usual
   path.
2. Manually fetched the orphaned commit into the local
   `.lake/packages/UnicodeBasic` checkout (`git fetch origin
   cff8377... && git checkout --detach cff8377...`) — this only touches
   the gitignored `.lake/` cache, no tracked files were changed.
3. Re-ran `lake build`. It then proceeded to clone every remaining
   dependency (`BibtexQuery`, `MD4Lean`, `plausible`, `LeanSearchClient`,
   `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`) without
   incident and began compiling Mathlib and (transitively) the project
   normally — hundreds of files built successfully with no further
   dependency-resolution errors.

This confirms the orphaned `UnicodeBasic` commit is the sole cause of the
build breakage.

Note: as part of this verification a `lake build` was left running in the
background to populate the local `.lake/build` cache; it is compiling
Mathlib from source (no `lake exe cache get` was used) and may still be
in progress. No repository files were modified.

## Proposed fixes

Pick one, roughly in order of robustness:

1. **Bump the `doc-gen4` pin** (best long-term fix). Currently
   `lakefile.toml` tracks `doc-gen4` at `rev = "main"`, a floating target,
   with the *lock* frozen at commit `05bb841`. The very next `doc-gen4`
   commit, `01e1433` ("chore: bump toolchain to v4.27.0 (#349)"), updates
   its own manifest to reference `UnicodeBasic` at a currently-reachable
   commit, while only moving the toolchain from `v4.27.0-rc1` to the final
   `v4.27.0` (a trivial, almost certainly compatible bump — a dependency's
   own `lean-toolchain` file doesn't need to match the root project's
   exactly). Concretely:
   ```toml
   [[require]]
   name = "«doc-gen4»"
   git = "https://github.com/leanprover/doc-gen4"
   rev = "01e1433..."   # or a later commit, deliberately chosen
   ```
   then run `lake update doc-gen4` to regenerate the manifest, and commit
   the result. Pinning to an explicit commit (instead of `"main"`) also
   prevents this kind of drift from surprising a future `lake update`.

2. **Hand-patch just the broken pin** (quick, less durable). Edit the
   `UnicodeBasic` entry in `lake-manifest.json` to point at the
   content-identical replacement commit
   `256e9993b028465b3e183f6da5f2ab02b7236725` instead of the orphaned
   `cff8377dbe50aae42cbd04213d5b3dacf742c3ba`. This unblocks `lake build`
   immediately without touching `lakefile.toml`, but it's a manual edit of
   a normally lake-managed file, and any future `lake update` that
   re-resolves `doc-gen4` could reintroduce a similarly stale pin.

3. **Local-only workaround** (what was used above to verify): manually
   `git fetch origin <sha> && git checkout --detach <sha>` inside
   `.lake/packages/UnicodeBasic` after a failed `lake build`. This gets
   one machine unstuck but does nothing for CI or other clones, and
   depends on GitHub continuing to serve an unreachable object.

Recommended: apply fix (1), verify `lake build` succeeds from a clean
`.lake` directory, and commit the regenerated `lake-manifest.json`.
