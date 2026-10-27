/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore

/-! # The comparison morphism for finite quotient origin transport

Source: Stacks Project, Tag 09C6.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/--
The comparison construction in finite quotient origin transport gives a morphism
from the transported constant model to the pulled-back complex which is both
monic and epic.  The morphism is kept as a separate intermediate statement so
that the final transport theorem only has to apply the balanced-category
criterion.  The construction restricts the core comparison to `Z`, composes it
with `hE`, and then applies the comparison-pullback and scalar-comparison
coherences on `W`; the local finite models in `C.refinementLisse` show that the
resulting morphism is epi and mono after every covering restriction, hence in
the sheaf category.  This is the morphism-and-detection part of Tag 09C6.

Source: Stacks Project, proetale.tex, Tag 09C6
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map).
-/
theorem lisse_finite_quotient_etale_origin_transport_map
    {X Y : Scheme.{u}} {g : Y ⟶ X}
    {A : Type (u + 1)} [CommRing A] {d : AdicCoefficientDatum A} {n : ℕ}
    {K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    {V : Y.Etale}
    (C : LisseFiniteQuotientEtaleOriginCore X Y g d n K V)
    (Z : V.left.Etale)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (hE : Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj
        C.level ≅ (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj E))
    (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))) :
    ∃ f : (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ⟶
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj K,
      Mono f ∧ Epi f := by
  sorry

end AlgebraicGeometry.Scheme
