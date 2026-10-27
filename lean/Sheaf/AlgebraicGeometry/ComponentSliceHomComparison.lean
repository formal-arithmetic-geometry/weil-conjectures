/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.ComponentSliceComparisonData
import Sheaf.AlgebraicGeometry.ComponentSliceOrdinaryMonoidal
import Sheaf.AlgebraicGeometry.ComponentSliceDerivedNormalization
import Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # Normalized component pullback on slices

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2).
(blueprint: lem-sfb-component-slice-hom-comparison-test).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- Existence of the component data is exactly the normalized evaluation theorem. -/
private theorem pullbackData_nonempty (W : Scheme.{u}) [IsAffine W]
    [IsWContractibleRing Γ(W, ⊤)] : Nonempty (PullbackData Λ W) := by
  obtain ⟨hc, hb, hl, ho, a, hf, he⟩ := component_pullback_unbounded_evaluation Λ W
  exact ⟨⟨hc, hb, hl, ho, a, hf, he⟩⟩

/-- A normalized component comparison is determined on the w-contractible basis. -/
private theorem ordinaryComparison_unique
    (W : Scheme.{u}) [IsAffine W] (U : W.ProEt) [IsAffine U.left]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U))
    (e e' : OrdinaryComparison Λ W U dW dU r) : e'.iso = e.iso := by
  have hb (M : Modules Λ (affineComponentSpace W))
      (V : U.left.ProEt) [IsAffine V.left] [IsWContractibleRing Γ(V.left, ⊤)] :
      (e'.iso.hom.app M).hom.hom.app (op V) =
        (e.iso.hom.app M).hom.hom.app (op V) := by
    apply AddCommGrpCat.ext
    intro y
    let x := (basisSections Λ dW (compositeTest W U V) M).symm
      (restrictionSections Λ W U (dW.modules.obj M) V y)
    have h := (e'.basis_formula V M x).trans (e.basis_formula V M x).symm
    simpa only [x, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] using eq_of_heq h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  obtain ⟨I, A, f, hcover, hA⟩ := (Scheme.ProEt.weaklyContractible_basis U.left).1 V.unop
  have hcover' : Sieve.ofArrows A f ∈ Scheme.ProEt.topology U.left V.unop :=
    Scheme.ProEt.mem_topology_iff.2 ⟨_, hcover, Sieve.le_generate _⟩
  apply (((r.modules ⋙ dU.modules).obj M).X.property).hom_ext_ofArrows f hcover'
  intro i
  obtain ⟨D, hD, ⟨a⟩⟩ := hA i
  let _ := hD
  have : IsAffine (A i).left := IsAffine.of_isIso a.inv
  let er := ((Scheme.Γ.mapIso a.op) ≪≫ Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv
  have : IsWContractibleRing Γ((A i).left, ⊤) :=
    RingHom.wContractible_of_ringEquiv er.symm
  rw [← (e'.iso.hom.app M).hom.hom.naturality (f i).op,
    ← (e.iso.hom.app M).hom.hom.naturality (f i).op, hb M (A i)]

/-- Restriction of component pullback is canonically component pullback on the slice;
its local derived-Hom comparison acts on every shifted Hom by the actual pullback.
The uniqueness clause fixes the comparison on the full basis, including all iterated
slice tests: two successive normalized restrictions therefore give the same map.

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), final sentence and (4.2);
Stacks Project, Tags 08JA, 08JB, 08J9, 07A4
(blueprint: lem-sfb-component-slice-hom-comparison-test).

Proof: Package the witnesses of component_pullback_unbounded_evaluation as dW and dU.
The ordinary component-slice lemma constructs r and the normalized tensor-compatible e;
the derived normalization lemma supplies the unbounded comparison for these same data.
For uniqueness, the prescribed basis formula identifies both maps on any section by
inverting basisSections and restrictionSections. Cover an arbitrary test by
w-contractible affines and use naturality and the sheaf separation condition. Equality
of the underlying sheaf maps then gives equality of module natural isomorphisms. This
argument works on every further slice test, including empty tests. -/
theorem component_slice_hom_comparison_test
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)] :
    ∃ dW : PullbackData Λ W,
      ∀ (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)],
        ∃ (dU : PullbackData Λ U.left) (r : RestrictionData Λ (componentMap W U))
          (m : (schemeRestriction Λ W U).Monoidal)
          (e : OrdinaryComparison Λ W U dW dU r),
          OrdinaryMonoidal Λ W U dW dU r m e ∧
          Nonempty (DerivedComparison Λ W U dW dU r m e) ∧
          ∀ e' : OrdinaryComparison Λ W U dW dU r, e'.iso = e.iso := by
  obtain ⟨dW⟩ := pullbackData_nonempty Λ W
  refine ⟨dW, ?_⟩
  intro U _ _
  obtain ⟨dU⟩ := pullbackData_nonempty Λ U.left
  obtain ⟨r, e, he⟩ := component_slice_ordinary_monoidal Λ W U dW dU
  refine ⟨dU, r, schemeCanonicalMonoidal Λ W U, e, he,
    component_slice_derived_normalization Λ W U dW dU r e he, ?_⟩
  exact ordinaryComparison_unique Λ W U dW dU r e

end AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice
