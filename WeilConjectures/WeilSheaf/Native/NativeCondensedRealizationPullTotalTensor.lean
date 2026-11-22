/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar

/-!
# The pullback comparison of the condensed realization on complexes

Let `g : Z ⟶ Y` be a morphism of `k₀`-schemes, `ḡ` its base change to the geometric fibres, and
`u : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` the isomorphism of
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`. We extend `u` degreewise
to cochain complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarComplexIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The isomorphism `u : N_Y ⋙ ḡ^* ≅ g^* ⋙ N_Z` on cochain complexes, degreewise. -/
noncomputable def condensedRealizationUpperStarComplexIso :
    (condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ) ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ) ≅
      (upperStar k₀ l g).mapHomologicalComplex (.up ℤ) ⋙
        (condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) _ ≪≫
    NatIso.mapHomologicalComplex (condensedRealizationUpperStarIso k₀ l g) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
