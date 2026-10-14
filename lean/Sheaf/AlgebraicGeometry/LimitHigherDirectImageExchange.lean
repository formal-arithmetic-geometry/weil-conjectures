/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! # Degreewise continuity of relative exchange under affine inverse limits

Source: Stacks Project, Tag 0EZT, second assertion, and Tag 0EYM.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- In nonnegative degree, canonical exchange passes from the stages to an affine
inverse limit. This assertion concerns a single cohomology sheaf, with arbitrary
abelian coefficients; it has no smoothness, torsion, or injectivity assumption.
Source: Stacks Project, Lemma 59.86.3, Tag 0EZT, second assertion, and
Lemma 59.51.8, Tag 0EYM.
(blueprint: lem-sc-limit-higher-direct-image-exchange)

Proof: Replace I by a cofinal directed inverse system. Pull f back to every D_i;
the resulting sources have affine transition morphisms and limit the pullback of f
to c.pt. The original source and base are constant systems. The coefficient system
is constant F; its colimit is F because I is nonempty and connected. Apply Tag 0EYM
to these systems, including after base change to each descended affine etale object.
Every affine etale object of c.pt descends to a stage. Tag 0EZT identifies the limit
higher-direct-image exchange on that object with the filtered colimit of the
stage exchanges. The given stage maps are isomorphisms, and hence so is their
filtered colimit. These affine etale objects form a basis, so the resulting map
of sheaves is an isomorphism. The exact-inverse-image homology comparison and the
single-complex/right-derived comparison identify this map with the displayed
homology of derivedBaseChangeMapPlus. Compatibility of these comparisons with
transition maps follows from their naturality and the resolution formula for
canonical exchange. The proof works for q = 0, the zero sheaf, and empty X. -/
theorem isIso_limit_homology_derivedBaseChangeMapPlus
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ)
    (hstage : ∀ i, IsIso
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f c.pt.hom).toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
