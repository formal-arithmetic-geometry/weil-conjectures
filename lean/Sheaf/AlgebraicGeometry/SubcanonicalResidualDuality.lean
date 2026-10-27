/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.CategoryTheory.Subobject.Limits
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Residual duality for subcanonical clusters on nodal curves

Source: Franciosi--Tenni, On Clifford's theorem for singular curves,
Definition 2.10 and Remarks 2.11 and 2.13, pp.231--232
(blueprint: lem-sfb-subcanonical-residual-duality).

The evaluation map is constructed by the tensor--Hom adjunction. The theorem
identifies its image as an ideal twist, uniquely as an ideal sheaf, and records
the involution with the same ambient canonical section and all numerical identities.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of local homomorphisms at the restriction of the specified global section.
This is the tensor--Hom evaluation precomposed with `s ⊗ id`, not a chosen morphism.
Source: Franciosi--Tenni, Definition 2.10 and Remark 2.11, pp.231--232
(blueprint: lem-sfb-subcanonical-residual-duality). -/
noncomputable def subcanonicalEvaluation {X : Scheme.{u}} (F ω : X.Modules)
    (s : Γ(F, ⊤)) : homObj F ω ⟶ ω :=
  (λ_ (homObj F ω)).inv ≫ homOfGlobalSection F s ▷ (homObj F ω) ≫
    (SheafOfModules.tensorHomEquiv F (homObj F ω) ω).symm (𝟙 (homObj F ω))

/-- Residual duality, involution and numerical identities for a subcanonical cluster.
Source: Franciosi--Tenni, Definition 2.10 and Remarks 2.11 and 2.13, pp.231--232
(blueprint: lem-sfb-subcanonical-residual-duality).

Proof plan, following the node's five steps:
1. Projectivity implies properness (`lem-kun-projective-implies-proper`), and finite type
   over the field implies Noetherianity (`lem-weil-pbc-finite-type-over-noetherian`).
   Proper coherent cohomology is finite (`lem-pc-euler-characteristic-well-defined`)
   and vanishes above dimension one (`lem-sc-noetherian-cohomology-above-dimension`).
   Global functions are k (`lem-sc-global-functions`), hence pa = h1(O).
   Nodal Serre duality (`lem-sfb-nodal-line-serre-riemann-roch`) identifies the chosen
   dualizing line with the reduced-curve dualizing module by uniqueness
   (`lem-sfb-reduced-curve-dualizing-module`); thus h0(ω) = pa and χ(ω) = pa - 1.
2. The coherent ideal twist F is generically rank one and has no punctual torsion.
   The kernel/cokernel lemma (`lem-weil-pbc-coherent-kernel-cokernel-locnoeth`) and
   torsion-free duality (`lem-sfb-reduced-curve-torsionfree-biduality`) make Hom(F,ω)
   coherent and generically detected. Since s is generically a basis, evaluation is
   injective. Its image untwisted by ω is a unique coherent ideal J, equal to O at
   every generic point; its closed subscheme is zero-dimensional. Evaluation of the
   original inclusion F → ω is s, so the same canonical section lies in Jω and is
   generically nonzero. No Cartier assumption on either cluster is used.
3. Canonical biduality (`lem-sfb-reduced-curve-torsionfree-biduality`) identifies
   f with the map φ ↦ φ(f). Evaluating this map at the section corresponding to the
   original inclusion gives i(f). Thus the second evaluation image is exactly I_S ω;
   equality of ideal sheaves gives the original closed subscheme including nilpotents.
4. For T = S and S*, the ideal sequence tensored by the invertible ω is exact.
   The zero-support Euler lemma (`lem-pc-chi-zero-dim-support`) identifies the quotient
   Euler characteristic with length(T). Euler additivity (`lem-pc-euler-additive`)
   yields χ(I_T ω) = pa - 1 - length(T). Coherent Serre duality and the bidual
   identification give h1(F_S) = h0(F_S*) and h1(F_S*) = h0(F_S).
5. Add these Euler identities for complementary lengths; the first is the section
   dimension difference. Substitution gives equality of Clifford indices. Both lengths
   are nonnegative finite dimensions, giving the bounds. Two-connectedness is retained
   although this residual-duality argument needs no such extra hypothesis.
-/
theorem subcanonical_residual_duality
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [Nonempty X] [ConnectedSpace X] [IsReduced X]
    (hTwoConnected : ∀ (A B : Scheme.{u}) (a : A ⟶ X) (b : B ⟶ X),
      IsClosedImmersion a → IsClosedImmersion b → IsReduced A → IsReduced B →
      Nonempty A → Nonempty B →
      (∃ P Q : Set (Set X), P ⊆ irreducibleComponents X ∧ Q ⊆ irreducibleComponents X ∧
        Disjoint P Q ∧ P ∪ Q = irreducibleComponents X ∧
        Set.range a = ⋃₀ P ∧ Set.range b = ⋃₀ Q) →
      2 ≤ Module.finrank k (scalarCohomology
        (CategoryTheory.Limits.pullback.fst a b ≫ a ≫ X ↘ Spec (.of k))
        (unit (CategoryTheory.Limits.pullback a b)) 0))
    (S : Scheme.{u}) (i : S ⟶ X) [IsClosedImmersion i]
    (D : SubcanonicalClusterData k X S i)
    (hSsub : IsSubcanonicalCluster i D.dualizing) :
    Function.Injective (fun z : Γ(subcanonicalModule i D.dualizing, ⊤) ↦
      (subcanonicalModuleInclusion i D.dualizing).val.app (op ⊤) z) ∧
    FiniteDimensional k (scalarCohomology (X ↘ Spec (.of k)) D.dualizing 0) ∧
    FiniteDimensional k (scalarCohomology (X ↘ Spec (.of k))
      (subcanonicalModule i D.dualizing) 0) ∧
    FiniteDimensional k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) ∧
    ((Module.finrank k (scalarCohomology (X ↘ Spec (.of k)) D.dualizing 0) : ℤ) =
      1 - eulerChar k (unit X)) ∧
    (0 ≤ (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) ∧
      (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) ≤
        2 * (1 - eulerChar k (unit X)) - 2) ∧
    ∀ s : Γ(subcanonicalModule i D.dualizing, ⊤),
      (∀ C : irreducibleComponents X,
        TopCat.Presheaf.germ (subcanonicalModule i D.dualizing).presheaf ⊤
          (genericPoints.ofComponent C).val (Set.mem_univ _) s ≠ 0) →
      Mono (subcanonicalEvaluation (subcanonicalModule i D.dualizing) D.dualizing s) ∧
      FiniteDimensional k (scalarCohomology (X ↘ Spec (.of k))
        (homObj (subcanonicalModule i D.dualizing) D.dualizing) 0) ∧
      ∃ J : X.IdealSheafData,
        topologicalKrullDim J.subscheme ≤ 0 ∧
        imageSubobject (subcanonicalEvaluation (subcanonicalModule i D.dualizing)
          D.dualizing s) =
          imageSubobject (subcanonicalModuleInclusion J.subschemeι D.dualizing) ∧
        (∀ K : X.IdealSheafData, topologicalKrullDim K.subscheme ≤ 0 →
          imageSubobject (subcanonicalEvaluation (subcanonicalModule i D.dualizing)
            D.dualizing s) =
            imageSubobject (subcanonicalModuleInclusion K.subschemeι D.dualizing) → K = J) ∧
        IsSubcanonicalCluster J.subschemeι D.dualizing ∧
        (∃ t : Γ(subcanonicalModule J.subschemeι D.dualizing, ⊤),
          (∀ C : irreducibleComponents X,
            TopCat.Presheaf.germ (subcanonicalModule J.subschemeι D.dualizing).presheaf ⊤
              (genericPoints.ofComponent C).val (Set.mem_univ _) t ≠ 0) ∧
          (subcanonicalModuleInclusion J.subschemeι D.dualizing).val.app (op ⊤) t =
            (subcanonicalModuleInclusion i D.dualizing).val.app (op ⊤) s ∧
          Mono (subcanonicalEvaluation (subcanonicalModule J.subschemeι D.dualizing)
            D.dualizing t) ∧
          imageSubobject (subcanonicalEvaluation (subcanonicalModule J.subschemeι D.dualizing)
            D.dualizing t) = imageSubobject (subcanonicalModuleInclusion i D.dualizing)) ∧
        FiniteDimensional k (scalarCohomology (J.subschemeι ≫ X ↘ Spec (.of k))
          (unit J.subscheme) 0) ∧
        FiniteDimensional k (scalarCohomology (X ↘ Spec (.of k))
          (subcanonicalModule J.subschemeι D.dualizing) 0) ∧
        ((Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) +
            Module.finrank k (scalarCohomology (J.subschemeι ≫ X ↘ Spec (.of k))
              (unit J.subscheme) 0) = 2 * (1 - eulerChar k (unit X)) - 2) ∧
        ((Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
            (subcanonicalModule i D.dualizing) 0) : ℤ) -
            Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
              (subcanonicalModule J.subschemeι D.dualizing) 0) =
          (1 - eulerChar k (unit X)) - 1 -
            Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0)) ∧
        (2 * (1 - eulerChar k (unit X)) -
            (Module.finrank k (scalarCohomology (J.subschemeι ≫ X ↘ Spec (.of k))
              (unit J.subscheme) 0) : ℤ) -
            2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
              (subcanonicalModule J.subschemeι D.dualizing) 0) : ℤ) =
          2 * (1 - eulerChar k (unit X)) -
            (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) -
            2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
              (subcanonicalModule i D.dualizing) 0) : ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
