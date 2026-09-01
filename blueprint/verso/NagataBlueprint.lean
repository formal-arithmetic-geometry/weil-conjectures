import NagataBlueprint.Prelude
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

import NagataBlueprint.Chapters.Compactifications
import NagataBlueprint.Chapters.ProjectiveSpace
import NagataBlueprint.Chapters.IdealSheaves
import NagataBlueprint.Chapters.Blowups
import NagataBlueprint.Chapters.StrictTransforms
import NagataBlueprint.Chapters.Conrad
import NagataBlueprint.Chapters.Modifications
import NagataBlueprint.Chapters.TwoOpen
import NagataBlueprint.Chapters.Noetherian
import NagataBlueprint.Chapters.Approximation
import NagataBlueprint.Chapters.Nagata

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Compactification of separated morphisms of finite type" =>

This blueprint records the route to *Nagata's compactification theorem*: a separated,
quasi-compact morphism locally of finite type over a quasi-compact quasi-separated base
factors as an open immersion followed by a proper morphism.

The chapters are in dependency order. We first develop the formal calculus of
compactifications of morphisms and its three stability constructions (immersions, closed
subschemes, base change). We then treat the base case, in which the source is quasi-affine,
by embedding it into a relative affine space and closing it up inside a relative projective
space. The bulk of the material is the geometry needed to glue two compactifications: the
theory of finite-type quasi-coherent ideal sheaves and their extension across quasi-compact
opens; the construction of the blow-up of a quasi-coherent ideal sheaf; admissible blow-up
centres, their composition, extension, and density properties; the identification of the
strict transform with the blow-up of a pulled-back centre; elimination of indeterminacy for
partial sections, proved along the route of Deligne and Conrad through Zariski's Main
Theorem, and the elimination of indeterminacy for separated finite-type morphisms deduced
from it; the resulting modification theorems (common modifications, graph extensions,
isomorphism near a boundary closure); and finally the two-open compactification theorem.
Induction over a finite affine open cover with dense total intersection gives the theorem
over a Noetherian base, absolute Noetherian approximation removes the Noetherian hypothesis
for morphisms of finite presentation, and the separated finite-presentation envelope of a
morphism of finite type completes the proof.

Every node carries the names of the declarations of this development which realise it, so
that the progress summary and the dependency graph below report on the state of the
formalization itself. The node labels are those of the companion survey
`blueprint/progress/current-progress.tex`, so the two documents can be read side by side.

{include 0 NagataBlueprint.Chapters.Compactifications}
{include 0 NagataBlueprint.Chapters.ProjectiveSpace}
{include 0 NagataBlueprint.Chapters.IdealSheaves}
{include 0 NagataBlueprint.Chapters.Blowups}
{include 0 NagataBlueprint.Chapters.StrictTransforms}
{include 0 NagataBlueprint.Chapters.Conrad}
{include 0 NagataBlueprint.Chapters.Modifications}
{include 0 NagataBlueprint.Chapters.TwoOpen}
{include 0 NagataBlueprint.Chapters.Noetherian}
{include 0 NagataBlueprint.Chapters.Approximation}
{include 0 NagataBlueprint.Chapters.Nagata}

{blueprint_graph}
{blueprint_summary}
