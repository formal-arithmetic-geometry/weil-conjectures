/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Statement
import Blueprint.Rationality
import Blueprint.RiemannHypothesis

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "The Weil Conjectures" =>

This Blueprint tracks the formalization of the Weil conjectures in Lean 4, building on
Mathlib. At this stage it only records the *statement* of the conjectures: the zeta
function of a scheme over a finite field, and the rationality, functional equation and
Riemann hypothesis for smooth, proper, geometrically integral schemes. The proof
blueprint will grow from here.

{include 0 Blueprint.Statement}
{include 0 Blueprint.Rationality}
{include 0 Blueprint.RiemannHypothesis}

{blueprint_graph}
{blueprint_summary}
