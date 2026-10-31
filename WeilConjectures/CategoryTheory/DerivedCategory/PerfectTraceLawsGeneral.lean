/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.Algebra.Homology.TwoStepFilteredTotal
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.FilteredProjectiveModel
import WeilConjectures.Algebra.Homology.FieldComplexCohomologySplitting
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat

/-!
# Trace laws over an arbitrary commutative ring

Source: current Weil blueprint, `sec-trace-formula/sk-p-trace/_section.md`
and `sk-p-trace.proof.md` (blueprint: sk-p-trace).

The six conjuncts give linearity, conjugacy, arbitrary derived scalar extension,
the finite-projective chain formula, coherent filtered additivity, and the field
cohomology formula. The projective-module trace is written using finite dual frames;
`LinearMap.trace` is used only over a field, since its general-ring implementation
requires a finite basis. All trace values use the recorded categorical construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace DerivedCategory

/-- The full trace laws for perfect complexes over any commutative ring.
Source: current blueprint, `sk-p-trace/_section.md` and `sk-p-trace.proof.md`
(blueprint: sk-p-trace).

Proof: choose a bounded finite-projective representative and lift the derived
endomorphism to a chain map, uniquely up to homotopy. Finite dual frames give
evaluation and coevaluation; the Koszul symmetry in degree `i` contributes
`(-1)^i`. The resulting supertrace is independent of the frame and homotopy:
cyclicity cancels the contributions of `dh + hd` after shifting the index.
This proves the chain formula for every representative and every finite splitting.
Linearity follows by distributing the frame functionals through `a*v + b*w`.
Transporting the duality across an isomorphism proves conjugacy invariance.
For every ring map, the bounded projective representative is K-flat, so the
universal derived-extension counit identifies its image, naturally on maps, with
termwise tensor extension. Tensoring the finite splitting preserves its retraction
identity, hence finite projectivity, and extends its dual frame. Applying the ring
map to the signed frame sum therefore computes the extended categorical trace;
no flatness of the target is needed. For a coherent filtered endomorphism, the
filtered-projective-model lemma supplies a bounded model with degreewise split
filtration. Its map is block triangular; dual frames on the two diagonal summands
show that the total trace is their sum. This uses the given filtered endomorphism,
not merely commuting maps of a Verdier triangle. Finally, over a field split cycles
and boundaries to replace the perfect object by its bounded zero-differential
cohomology complex. The cohomology Hom bijection identifies the transported map
with `H^i(v)`. Conjugacy and the chain formula give the last finitely supported sum.
-/
theorem perfectCategoricalTrace_general_laws
    (A : Type u) [CommRing A] [HasDerivedCategory.{u} (ModuleCat.{u} A)] :
    (∀ (P : DerivedCategory (ModuleCat.{u} A)) (hP : IsPerfectRingComplex P)
      (v w : P ⟶ P) (a b : A),
      perfectCategoricalTrace P hP (a • v + b • w) =
        a * perfectCategoricalTrace P hP v + b * perfectCategoricalTrace P hP w) ∧
    (∀ (P T : DerivedCategory (ModuleCat.{u} A))
      (hP : IsPerfectRingComplex P) (hT : IsPerfectRingComplex T)
      (v : P ⟶ P) (w : T ⟶ T) (e : P ≅ T),
      v ≫ e.hom = e.hom ≫ w →
        perfectCategoricalTrace P hP v = perfectCategoricalTrace T hT w) ∧
    (∀ (B : Type u) [CommRing B] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
      (ρ : A →+* B)
      (LF : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
      (ε : Qh ⋙ LF ⟶ (ModuleCat.extendScalars ρ).mapHomotopyCategory (.up ℤ) ⋙ Qh),
      LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)) →
      ∀ (P : DerivedCategory (ModuleCat.{u} A)) (hP : IsPerfectRingComplex P) (v : P ⟶ P),
        ∃ hB : IsPerfectRingComplex (LF.obj P),
          ρ (perfectCategoricalTrace P hP v) =
            perfectCategoricalTrace (LF.obj P) hB (LF.map v)) ∧
    (∀ (C : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      C.IsStrictlyGE a → C.IsStrictlyLE b →
      (∀ i : ℤ, Module.Finite A (C.X i) ∧ Module.Projective A (C.X i)) →
      ∀ (s : ModuleCat.StrictPerfectCoefficientPackage C)
        (P : DerivedCategory (ModuleCat.{u} A)) (hP : IsPerfectRingComplex P)
        (v : P ⟶ P) (t : C ⟶ C) (e : P ≅ Q.obj C),
        v ≫ e.hom = e.hom ≫ Q.map t →
          perfectCategoricalTrace P hP v =
            ∑ i ∈ Finset.Icc a b, i.negOnePow •
              ∑ r : Fin (s.N i), perfectTraceFrameFunctional s i r
                ((t.f i).hom (perfectTraceFrameVector s i r))) ∧
    (∀ (F : TwoStepModuleDerived A) (v : F ⟶ F)
      (h : IsPerfectRingComplex ((twoStepTotal A).obj F))
      (h₁ : IsPerfectRingComplex ((twoStepGraded A true).obj F))
      (h₀ : IsPerfectRingComplex ((twoStepGraded A false).obj F)),
      perfectCategoricalTrace _ h ((twoStepTotal A).map v) =
        perfectCategoricalTrace _ h₁ ((twoStepGraded A true).map v) +
          perfectCategoricalTrace _ h₀ ((twoStepGraded A false).map v)) ∧
    (∀ (L : Type u) [Field L] [HasDerivedCategory.{u} (ModuleCat.{u} L)]
      (P : DerivedCategory (ModuleCat.{u} L)) (hP : IsPerfectRingComplex P) (v : P ⟶ P),
      perfectCategoricalTrace P hP v = ∑ᶠ i : ℤ, i.negOnePow •
        LinearMap.trace L ((homologyFunctor (ModuleCat.{u} L) i).obj P)
          (((homologyFunctor (ModuleCat.{u} L) i).map v).hom)) := by
  sorry

end DerivedCategory
