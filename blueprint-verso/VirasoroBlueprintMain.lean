import VersoManual
import VersoBlueprint.PreviewManifest
import VirasoroBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc VirasoroBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
