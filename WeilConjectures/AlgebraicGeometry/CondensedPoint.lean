/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPointBasis
public import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Condensed.Equivalence
public import WeilConjectures.Topology.ProfiniteCondensedRing
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# The pro-etale geometric point

Source: latest blueprint, sec-proetale-coefficients,
`sk-prop-pe-condensed-point/_section.md` and its proof
(blueprint: sk-prop-pe-condensed-point).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/--
The affine pro-etale geometric point is controlled by profinite test objects.  Its
basis equivalence, induced dense topology, and coefficient evaluations give the
condensed-set topos and the usual continuous or discrete coefficient descriptions.
Source: blueprint `sk-prop-pe-condensed-point`, node statement and proof clauses
(blueprint: sk-prop-pe-condensed-point).

Proof: (1) A finitely presented etale algebra over Ω is a finite power of Ω.
Filtered colimits therefore give locally constant algebras on profinite sets.
The classification and Hom bijection in `condensed_point_basis` give the displayed
basis equivalence with the specified spectrum functor.
(2) `geometricFieldProfiniteDenseSubsite` identifies the induced topology with the
coherent topology and gives cover density. A covering sieve contains a finite
jointly surjective family, by the effective-epimorphic-family characterization in
Profinite. This includes the empty family over the empty profinite set.
(3) Dense-subsite comparison gives an equivalence from small pro-etale sheaves to
coherent profinite sheaves; compose with `Condensed.ProfiniteCompHaus.equivalence`.
(4) `condensed_point_coefficients` evaluates continuous ring coefficients as the
presheaf of continuous functions, naturally on test objects. Apply it to every
locally profinite ring (compact profinite rings are included).
(5) For a discrete ring, the same dependency identifies the coefficient ring with
both the comparison pullback of the constant etale ring and the constant pro-etale
ring. Continuous functions are locally constant in this case.
-/
theorem condensed_point (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∃ E : Profinite.{u} ≌ ObjectProperty.FullSubcategory
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom),
      Nonempty (E.functor ⋙ ObjectProperty.ι
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom) ≅
          condensedPointSchemeFunctor Ω)) ∧
    (profiniteToProEtOf (Spec (.of Ω))).IsDenseSubsite
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of Ω))) ∧
    (∀ (S : Profinite.{u}) (R : Sieve S),
      R ∈ coherentTopology Profinite.{u} S ↔
        ∃ (n : ℕ) (T : Fin n → Profinite.{u}) (f : ∀ i : Fin n, T i ⟶ S),
          (∀ i : Fin n, R (f i)) ∧ ∀ s : S, ∃ (i : Fin n) (t : T i), f i t = s) ∧
    Nonempty (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) (Type (u + 1)) ≌
      Condensed.{u} (Type (u + 1))) ∧
    (∀ (T : Type u) [TopologicalSpace T] [Ring T] [IsTopologicalRing T],
      Nonempty ((condensedPointRingRestriction (Spec (.of Ω))).obj
        (coefficientRing (Spec (.of Ω)) (Mon.mk (Profinite.continuousCoefficientRingObj T))) ≅
          (Profinite.continuousCoefficientRingPresheaf T).toMonAb)) ∧
    (∀ (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A],
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          (comparisonUpperStar Ab.{u + 1} (Spec (.of Ω))).mapMon.obj
            (condensedPointConstantRing (Spec (.of Ω)).smallEtaleTopology A))) ∧
    (∀ (A : Type u) [Ring A] [TopologicalSpace A] [DiscreteTopology A],
      Nonempty (coefficientRing (Spec (.of Ω))
        (Mon.mk (Profinite.continuousCoefficientRingObj A)) ≅
          condensedPointConstantRing (Scheme.ProEt.topology (Spec (.of Ω))) A)) := by
  classical
  have hd := geometricFieldProfiniteDenseSubsite Ω
  have hc := condensed_point_coefficients Ω
  refine ⟨(condensed_point_basis Ω).2.2.2.2.1, hd, ?_, ?_, hc.2.2.1, ?_, ?_⟩
  · intro S R
    constructor
    · intro hR
      obtain ⟨I, hI, T, f, hf, hmem⟩ :=
        (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mp hR
      let := hI
      let := Fintype.ofFinite I
      let e := Fintype.equivFin I
      have hsurj := ((Profinite.effectiveEpiFamily_tfae T f).out 0 2).mp hf
      refine ⟨Fintype.card I, fun i ↦ T (e.symm i), fun i ↦ f (e.symm i),
        fun i ↦ hmem (e.symm i), ?_⟩
      intro s
      obtain ⟨i, t, ht⟩ := hsurj s
      refine ⟨e i, ?_⟩
      change ∃ t : T (e.symm (e i)), f (e.symm (e i)) t = s
      rw [e.symm_apply_apply]
      exact ⟨t, ht⟩
    · rintro ⟨n, T, f, hmem, hsurj⟩
      exact (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily R).mpr
        ⟨Fin n, inferInstance, T, f,
          Profinite.effectiveEpiFamily_of_jointly_surjective T f hsurj, hmem⟩
  · exact ⟨(Functor.IsDenseSubsite.sheafEquiv
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of Ω)))
        (profiniteToProEtOf (Spec (.of Ω))) (Type (u + 1))).symm.trans
      (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1)))⟩
  · intro A _ _ _
    exact (hc.2.2.2 A).2.1
  · intro A _ _ _
    exact (hc.2.2.2 A).2.2

end AlgebraicGeometry.ProEtale
