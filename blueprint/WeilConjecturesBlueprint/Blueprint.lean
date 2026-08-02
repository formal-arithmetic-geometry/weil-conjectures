import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import WeilConjecturesBlueprint.Chapters.Overview
import WeilConjecturesBlueprint.Chapters.ElementaryFoundations
import WeilConjecturesBlueprint.Chapters.FrobeniusLinearAlgebra
import WeilConjecturesBlueprint.Chapters.ZetaFunctions
import WeilConjecturesBlueprint.Chapters.TraceFormula
import WeilConjecturesBlueprint.Chapters.Duality
import WeilConjecturesBlueprint.Chapters.AbstractCohomology
import WeilConjecturesBlueprint.Chapters.Weights
import WeilConjecturesBlueprint.Chapters.Purity
import WeilConjecturesBlueprint.Chapters.EtaleCohomology
import WeilConjecturesBlueprint.Chapters.SixOperations
import WeilConjecturesBlueprint.Chapters.GeometricInputs
import WeilConjecturesBlueprint.Chapters.FinalAssembly

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Weil Conjectures" =>

This blueprint tracks the formalization of the *Weil conjectures* in Lean 4:
rationality, the functional equation, and the Riemann hypothesis for the zeta
function of a smooth, proper, geometrically integral variety over a finite
field, following the Laumon–Deligne route to Weil II. The final statements
are purely arithmetic — integer polynomials constrained by their complex
roots — and the proof is organized as an elementary Frobenius-module theorem
(Version I), an abstract cohomology interface (Version II), and its étale
realization (Version III).

{include 0 WeilConjecturesBlueprint.Chapters.Overview}

{include 0 WeilConjecturesBlueprint.Chapters.ElementaryFoundations}

{include 0 WeilConjecturesBlueprint.Chapters.FrobeniusLinearAlgebra}

{include 0 WeilConjecturesBlueprint.Chapters.ZetaFunctions}

{include 0 WeilConjecturesBlueprint.Chapters.TraceFormula}

{include 0 WeilConjecturesBlueprint.Chapters.Duality}

{include 0 WeilConjecturesBlueprint.Chapters.AbstractCohomology}

{include 0 WeilConjecturesBlueprint.Chapters.Weights}

{include 0 WeilConjecturesBlueprint.Chapters.Purity}

{include 0 WeilConjecturesBlueprint.Chapters.EtaleCohomology}

{include 0 WeilConjecturesBlueprint.Chapters.SixOperations}

{include 0 WeilConjecturesBlueprint.Chapters.GeometricInputs}

{include 0 WeilConjecturesBlueprint.Chapters.FinalAssembly}

{blueprint_graph}
{blueprint_summary}
