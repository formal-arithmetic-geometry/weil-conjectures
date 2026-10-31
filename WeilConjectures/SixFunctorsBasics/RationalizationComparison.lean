/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ScalarLocalization
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHomComparisons

/-! # Inverting ell in bounded constructible complexes

Source: Bhatt--Scholze, Proposition 6.8.14(2), and the current blueprint
(blueprint: sk-thm-sfb-rationalization-comparison).

The source is the raw scalar localization of the category with finite constant local models.
Its objects are integral objects and its morphisms are tensor products. The algebra
isomorphism identifies the localized scalar ring with E, and the comparison with the ambient
derived extension fixes the functor on every pure tensor. No idempotent completion is taken.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- Derived scalar extension kills precisely the complexes killed by one power of ell,
and identifies the raw tensor-Hom localization with the rational constructible category.
The scalar action is the existing action transported through continuous coefficient modules.

Source: Bhatt--Scholze, Proposition 6.8.14(2), and the blueprint's sole proof paragraph
(blueprint: sk-thm-sfb-rationalization-comparison).

Proof: First identify finite constant local models with stratified local finite presentations
for integral and field coefficients on the topologically Noetherian scheme. Use the integral
local-model comparison and, for fields, finite local freeness on each Noetherian stratum.
The existing bounded constructible scalar extension is a localization at maps with cones
killed by a power of ell. Scalar fractions show that every rational map has an integral
numerator and an ell-power denominator, and two integral maps agree rationally exactly when
some ell-power kills their difference. Apply this to identity and zero to obtain the first
clause; conversely an invertible scalar cannot kill a nonzero rational object. Constant
scalars act centrally on integral module sheaves and on their derived category, giving the
normalized linear structure. Since the valuation ring is a DVR and ell is a unit times a
power of a uniformizer, its localization at ell is E. The fraction description gives full
faithfulness of the raw tensor-Hom comparison, with the stated pure-tensor formula. The
localization theorem gives essential surjectivity. The resulting equivalence factors the
specified derived extension via the natural comparison c. This includes zero objects and
the empty scheme, and requires only Noetherianity of the underlying space.

The upstream `AlgebraicGeometry.ProEtale.rationalizationComparison` is a distinct sheaf-level
natural transformation (the colimit/direct-sum formula), so this category-level comparison
keeps a distinct name.
-/
theorem sfbRationalizationComparison (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X,
      IsZero ((RationalLocalizedHom.extend X ell E).obj K.obj) ↔
        ∃ n : ℕ, (ell : ℤ) ^ n • 𝟙 K.obj = 0) ∧
    ∃ lin : Linear (PadicAlgCl.integers ell E.1)
        (ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X),
      (fun [linInst : Linear (PadicAlgCl.integers ell E.1)
          (ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X)] ↦
        (∀ (K L : ConstantModelBoundedConstructible
            (Profinite.padicIntegersRingObj ell E.1) X)
          (a : PadicAlgCl.integers ell E.1) (f : K ⟶ L),
          (a • f).hom = @SMul.smul
            (PadicAlgCl.integers ell E.1) (K.obj ⟶ L.obj)
            (RationalLocalizedHom.integralHomModule X ell E K.obj L.obj).toSMul a f.hom) ∧
        ∃ eE : Localization.Away (ell : PadicAlgCl.integers ell E.1) ≃ₐ[
            PadicAlgCl.integers ell E.1] E.1,
        ∃ e : ScalarLocalization (PadicAlgCl.integers ell E.1)
              (ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X)
              (ell : PadicAlgCl.integers ell E.1) ≌
            ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X,
        ∃ c : ScalarLocalization.localization (PadicAlgCl.integers ell E.1)
              (ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X)
              (ell : PadicAlgCl.integers ell E.1) ⋙ e.functor ⋙
                (constantModelBoundedConstructible
                  (Profinite.continuousMapRingObj E.1) X).ι ≅
            (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X).ι ⋙
              RationalLocalizedHom.extend X ell E,
        ∀ (K L : ConstantModelBoundedConstructible
            (Profinite.padicIntegersRingObj ell E.1) X)
          (a : Localization.Away (ell : PadicAlgCl.integers ell E.1)) (f : K ⟶ L),
          c.inv.app K ≫ (e.functor.map (a ⊗ₜ f)).hom ≫ c.hom.app L =
            @SMul.smul E.1
              (((RationalLocalizedHom.extend X ell E).obj K.obj) ⟶
                ((RationalLocalizedHom.extend X ell E).obj L.obj))
              (RationalLocalizedHom.rationalHomModule X ell E
                ((RationalLocalizedHom.extend X ell E).obj K.obj)
                ((RationalLocalizedHom.extend X ell E).obj L.obj)).toSMul
              (eE a) ((RationalLocalizedHom.extend X ell E).map f.hom)) (linInst := lin) := by
  sorry

end AlgebraicGeometry.ProEtale
