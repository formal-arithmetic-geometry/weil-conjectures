/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.Paper.CondensedPointBasis
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections

/-!
# Coefficients on the pro-etale geometric point

Source: main-20261015 blueprint, sec-proetale-coefficients,
sk-prop-pe-condensed-point/sk-prop-pe-condensed-point-coefficients.md
(blueprint: det-pe-condensed-point-coefficients).

The test objects are the canonical `profiniteToProEtOf` objects. The natural identification
with `Spec LC(S,Ω)` is `condensed_point_basis`. Ring comparisons live in monoid objects of
abelian presheaves or sheaves, so they retain multiplication and unit as well as addition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Restriction of an internal ring sheaf to the canonical profinite test objects, retaining
its actual ring operations. Source: the coefficient lemma, first paragraph
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointRingRestriction (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⥤
      Mon (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon ⋙
    ((Functor.whiskeringLeft Profinite.{u}ᵒᵖ X.ProEtᵒᵖ Ab.{u + 1}).obj
      (profiniteToProEtOf X).op).mapMon

/-- The existing constant ring sheaf, regarded as an internal ring in abelian sheaves.
Source: the coefficient lemma, clause (2), and `def-weil-pbc-constant-sheaf`
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointConstantRing {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J RingCat.{u + 1}]
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    (A : Type u) [Ring A] : Mon (Sheaf J Ab.{u + 1}) :=
  Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} A))))

/-- The finite-quotient diagram `A^{S_i}`, with transition maps given by precomposition.
Source: the coefficient lemma, clause (2), finite-quotient formula
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointFiniteFunctionDiagram (A : Type u) [Ring A]
    (S : Profinite.{u}) : (DiscreteQuotient S)ᵒᵖ ⥤ RingCat.{u + 1} where
  obj q := RingCat.of (ULift.{u + 1} (q.unop → A))
  map {q r} f := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((RingHom.pi (fun x : r.unop ↦ Pi.evalRingHom (fun _ : q.unop ↦ A)
      (DiscreteQuotient.ofLE f.unop.le x))).comp ULift.ringEquiv.toRingHom))
  map_id q := by
    ext a x
    refine Quotient.inductionOn x ?_
    intro s
    rfl
  map_comp f g := by
    ext a x
    refine Quotient.inductionOn x ?_
    intro s
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cocone from finite-quotient functions to locally constant functions:
its leg at a quotient q sends a to a composed with the quotient projection.
Source: the coefficient lemma, clause (2), finite-quotient formula
(blueprint: det-pe-condensed-point-coefficients). -/
noncomputable def condensedPointFiniteFunctionCocone (A : Type u) [Ring A]
    (S : Profinite.{u}) : Cocone (condensedPointFiniteFunctionDiagram A S) where
  pt := RingCat.of (ULift.{u + 1} (LocallyConstant S A))
  ι :=
    { app := fun q ↦ RingCat.ofHom
        { toFun := fun (a : ULift.{u + 1} (q.unop → A)) ↦ ULift.up
            ((⟨a.down, IsLocallyConstant.of_discrete a.down⟩ : LocallyConstant q.unop A).comap
              ⟨q.unop.proj, q.unop.proj_isLocallyConstant.continuous⟩)
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality := by
        intro q r f
        ext a
        rfl }

/-- On a separably closed geometric point, the inverse image of a condensed set or ring
has its original sections on every profinite test object. Continuous ring coefficients give
continuous functions; discrete coefficients give locally constant functions, their canonical
finite-quotient colimit, the comparison pullback of the etale constant ring, and the classical
pro-etale constant ring.

Source: main-20261015 blueprint, coefficient lemma, both paragraphs and clauses (1)--(2)
(blueprint: det-pe-condensed-point-coefficients).

Proof plan, following the node's six steps:
1. `det-pe-condensed-point-basis` identifies affine ind-etale objects with profinite sets.
   `lem-weil-pbc-locally-constant-prime-spectrum` identifies their spaces and arrows by
   evaluation kernels. `lem-weil-pbc-ind-etale-stability` gives weak etaleness. The covering
   definition `def-weil-pbc-proetale-site` then gives exactly finite joint surjectivity.
2. `lem-weil-pbc-ind-etale-basis` gives the dense affine basis. Apply
   `lem-pc-fppf-dense-sheaf-equivalence` to restriction to that basis, with sets and abelian
   groups, using the larger coefficient universe of `def-weil-size-convention`.
3. The adjunction in `sk-def-sfb-pullback-from-point`, and its set version in
   `lem-weil-pbc-profinite-point-pullback`, have this restriction as right adjoint. Since
   restriction is an equivalence, the unit is invertible. Its inverse gives the natural
   evaluation comparison. Naturality at each operation identifies the internal ring
   structure of `sk-def-sfb-pulled-back-coefficients`, including noncommutative rings.
4. `sk-def-sfb-condensed-ring` gives C(S,T). For discrete A, continuity is local constancy.
   Compactness makes the image finite, giving a finite clopen quotient through which every
   function factors. Common refinements identify equal representatives. These are exactly
   the legs of `condensedPointFiniteFunctionCocone`, and they preserve ring operations.
   At the empty space use the empty quotient and the one-element zero ring.
5. The test object is the limit of finite disjoint unions of Spec Ω. The finite-stage
   constant etale ring has sections A^{S_i}, by
   `lem-galois-constant-sheaf-sets-representable`, with pointwise operations from
   `def-weil-pbc-constant-sheaf`; restrictions are precomposition.
6. `lem-weil-pbc-comparison-sections` identifies its comparison inverse image with this
   same colimit. The basis uniqueness in `lem-weil-pbc-ind-etale-basis` extends the ring
   isomorphism to the full site. Finally LC(-,A) has the constant-sheaf universal property:
   pull each constant to its clopen fibre and glue over the finite partition. Refinement
   gives naturality and uniqueness. Transport across the basis equivalence gives exactly
   the classical constant ring sheaf, preserving its specified constant coefficients. -/
theorem condensed_point_coefficients (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∀ F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)),
      Nonempty ((profiniteToProEtOf (Spec (.of Ω))).op ⋙
        ((profinitePointSetSchemeInverseImage (Spec (.of Ω))).obj F).obj ≅ F.obj)) ∧
    (∀ F : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) F) ≅
          (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon.obj F)) ∧
    (∀ (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T],
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) (Mon.mk (Profinite.continuousCoefficientRingObj T))) ≅
          (Profinite.continuousCoefficientRingPresheaf T).toMonAb)) ∧
    (∀ (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A],
      (∀ S : Profinite.{u},
        (∃ e : LocallyConstant S A ≃+* C(S, A), ∀ f : LocallyConstant S A,
          (e f : S → A) = f) ∧
        Nonempty (IsColimit (condensedPointFiniteFunctionCocone A S))) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            (condensedPointConstantRing (Spec (.of Ω)).smallEtaleTopology A)) ∧
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          condensedPointConstantRing (Scheme.ProEt.topology (Spec (.of Ω))) A)) := by
  sorry

end AlgebraicGeometry.ProEtale
