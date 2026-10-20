/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! # Construction of open operation models -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Construct the ordinary and derived operation comparisons from the supplied tensor
models and the sectionwise direct-image square.

Proof: identify the open pro-etale site with the localization at the open object.
Construct extension by zero as the direct-sum presheaf followed by module
sheafification. The unique summand over an object of the open identifies the unit
with an isomorphism. This extension is additive and exact; do this for both opens.
For the vertical diagram site use the sheaf of open objects, whose category of
elements is the product of the index category with the localized ordinary site.
The same direct-sum construction and sheafification commute with all coefficient
transitions, so no flatness of these transitions is required.
When an API uses equal object and morphism universes, lift the site's hom types
to the object universe, transport the topology and ring sheaves along that
category equivalence, apply the API, and transport back. These exact sectionwise
equivalences preserve flatness, K-flatness and the representative equations.
Construct the two module pullbacks as inverse image followed by scalar extension,
with their adjunctions to the specified sectionwise direct images. Flat-term
K-flat resolutions construct their total left derived functors and their model
comparisons. Localizing the morphism of ringed sites identifies the ordinary
pullback square; transposing the supplied direct-image square specifies its mate.
Restriction preserves flat-term K-flat complexes, and descending this ordinary
square on those representatives gives theta and its displayed model equation.
Restriction commutes with sheafification and sectionwise tensor, giving the pure
tensor equation. The canonical tensor-pullback theorem, applied to restriction
and to the supplied tensor models, gives the derived tensor comparison and its
representative equation. Use exactly the supplied four tensor models and the
supplied direct-image square in the resulting record. Every argument applies to
the vertical site itself, hence includes arbitrary semilinear transitions.

Source: Stacks, sites-modules.tex, Tags 03DI, 03DJ, 0F6Z, 04J0 and 03EL;
sites-cohomology.tex, Tags 06YS, 06YY, 0G7E and 07A4.
(blueprint: lem-sf-open-operation-models). -/
theorem normalizedOperations_exists {m : Mode} (d : Input.{u} m) (t : SiteSquare d)
    (tx : TensorModel d.R) (tu : TensorModel (restrictRing m d.j d.R))
    (tx' : TensorModel d.S) (tu' : TensorModel (restrictRing m d.j' d.S))
    (s : direct m d.g d.R d.S d.coefficient ⋙ restrict m d.j d.R ≅
      restrict m d.j' d.S ⋙ direct m d.gU _ _ (cornerCoefficient t))
    (hs : ∀ (N : Mod d.S) (W : (Site m d.U)ᵒᵖ)
      (x : N.val.obj ((openInclusion m d.j ⋙ baseChange m d.g).op.obj W)),
      (s.hom.app N).val.app W x = N.val.map (t.iso.inv.app W.unop).op x) :
    ∃ o : Operations d t, o.tensorX = tx ∧ o.tensorU = tu ∧
      o.tensorX' = tx' ∧ o.tensorU' = tu' ∧ o.rightSquare = s := by
  sorry

end SheafOfModules.OpenTensorNormalization
