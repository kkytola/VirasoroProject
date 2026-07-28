import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VirasoroBlueprint.Chapters.Introduction
import VirasoroBlueprint.Chapters.LieAlgebraCohomology
import VirasoroBlueprint.Chapters.CentralExtension
import VirasoroBlueprint.Chapters.WittCohomology
import VirasoroBlueprint.Chapters.VirasoroAlgebra
import VirasoroBlueprint.Chapters.HeisenbergAlgebra
import VirasoroBlueprint.Chapters.Verma
import VirasoroBlueprint.Chapters.Sugawara

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "VirasoroProject" =>

This is the blueprint of the _VirasoroProject_, a Lean 4 formalization of
topics related to the Virasoro algebra, by Kalle Kytölä.

{include 0 VirasoroBlueprint.Chapters.Introduction}
{include 0 VirasoroBlueprint.Chapters.LieAlgebraCohomology}
{include 0 VirasoroBlueprint.Chapters.CentralExtension}
{include 0 VirasoroBlueprint.Chapters.WittCohomology}
{include 0 VirasoroBlueprint.Chapters.VirasoroAlgebra}
{include 0 VirasoroBlueprint.Chapters.HeisenbergAlgebra}
{include 0 VirasoroBlueprint.Chapters.Verma}
{include 0 VirasoroBlueprint.Chapters.Sugawara}

{blueprint_graph}
{blueprint_summary}
