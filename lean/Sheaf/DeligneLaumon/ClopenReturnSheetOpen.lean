/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.RingTheory.ProEtale.IndEtaleDirectedUnion
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The distinguished geometric return sheet is open

Source: blueprint `sk-i-dl-general-real`, the geometric-socle/Frobenius orbit step.
(blueprint: lem-zl-clopen-return-sheet-open).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem indEtale_closure (k : Type u) [Field k] [Finite k] :
    Algebra.IndEtale k (AlgebraicClosure k) := by
  let 𝒜 : Set (Subalgebra k (AlgebraicClosure k)) :=
    {A | ∃ K : IntermediateField k (AlgebraicClosure k), Module.Finite k K ∧
      A = K.toSubalgebra}
  apply Algebra.IndEtale.of_directedOn 𝒜
  · rintro A ⟨K, hK, rfl⟩ B ⟨T, hT, rfl⟩
    have := hK
    have := hT
    exact ⟨(K ⊔ T).toSubalgebra, ⟨K ⊔ T, inferInstance, rfl⟩,
      (IntermediateField.toSubalgebra_le_toSubalgebra).2 le_sup_left,
      (IntermediateField.toSubalgebra_le_toSubalgebra).2 le_sup_right⟩
  · intro x
    have hfin : Module.Finite k (IntermediateField.adjoin k {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    exact ⟨(IntermediateField.adjoin k {x}).toSubalgebra,
      ⟨IntermediateField.adjoin k {x}, hfin, rfl⟩,
      IntermediateField.subset_adjoin k {x} (Set.mem_singleton x)⟩
  · rintro A ⟨K, hK, rfl⟩
    have := hK
    exact Algebra.Etale.of_finite_of_isSeparable (K := k) (L := K)

private theorem weaklyEtale_geometricFiberProj
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    WeaklyEtale f.geometricFiberProj := by
  have := indEtale_closure k
  have : WeaklyEtale (Scheme.specAlgebraicClosure k).hom := by
    change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    rw [WeaklyEtale.Spec_iff]
    change (algebraMap k (AlgebraicClosure k)).WeaklyEtale
    rw [RingHom.weaklyEtale_algebraMap_iff]
    infer_instance
  exact inferInstanceAs (WeaklyEtale (pullback.fst _ _))

/-- The two projection equations characterize an open immersion of the distinguished sheet.
Source: the first step of `lem-zl-clopen-return-subobject` in `sk-i-dl-general-real`.
Proof: the projections from geometric fibres are weakly etale, since an algebraic
closure of a finite field is the directed union of its finite etale subextensions.
The model projection equation and cancellation for weakly etale morphisms make `v`
weakly etale. The two projection equations, and monicity of `c` and the closure
isomorphism, make `v` monic. The closure projection equation makes `v` locally of
finite type over a locally Noetherian target, hence locally of finite presentation.
A flat monomorphism locally of finite presentation is an open immersion.
(blueprint: lem-zl-clopen-return-sheet-open). -/
theorem isOpenImmersion_clopen_return_sheet
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {X C : Scheme.{u}}
    [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom)) :
    IsOpenImmersion v := by
  have : IsIso (CommRingCat.ofHom
      (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom) :=
    (algebraicClosureAlgEquiv k₀ k₁).symm.toRingEquiv.toCommRingCatIso.isIso_hom
  have : IsLocallyNoetherian (X ↘ Spec (.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  have := weaklyEtale_geometricFiberProj (X ↘ Spec (.of k₀))
  have := weaklyEtale_geometricFiberProj (C ↘ Spec (.of k₁))
  have : WeaklyEtale (v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj) := by
    rw [hp]
    exact MorphismProperty.comp_mem @WeaklyEtale
      (C ↘ Spec (.of k₁)).geometricFiberProj c
      (weaklyEtale_geometricFiberProj _) inferInstance
  have : WeaklyEtale v := WeaklyEtale.of_comp v (X ↘ Spec (.of k₀)).geometricFiberProj
  have : Mono v := ⟨fun {T} a b hab ↦ by
    apply Scheme.Hom.geometricFiber_hom_ext
    · apply (cancel_mono c).1
      simpa only [Category.assoc, ← hp] using
        congrArg (fun f ↦ f ≫ (X ↘ Spec (.of k₀)).geometricFiberProj) hab
    · apply (cancel_mono
        (Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))).1
      simpa only [Category.assoc, ← hb] using
        congrArg (fun f ↦ f ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure) hab⟩
  have : LocallyOfFiniteType
      (v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure) := by
    rw [hb]
    infer_instance
  have : LocallyOfFiniteType v := locallyOfFiniteType_of_comp v
    (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  exact IsOpenImmersion.of_flat_of_mono v

/-- The distinguished sheet has closed range when the model inclusion does.
Source: the first step of `lem-zl-clopen-return-subobject` in `sk-i-dl-general-real`.
Proof: geometric-fibre projections are integral. Thus the model projection equation
makes the composite of `v` with the target projection integral. The latter projection
is separated, so cancellation makes `v` integral and hence closed. Combine this with
the proved open-immersion property.
(blueprint: lem-zl-clopen-return-sheet-open). -/
theorem isClosedImmersion_clopen_return_sheet
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {X C : Scheme.{u}}
    [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c] [IsClosedImmersion c]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom)) :
    IsClosedImmersion v := by
  have := isOpenImmersion_clopen_return_sheet c v hp hb
  have : IsIntegralHom (Scheme.specAlgebraicClosure k₁).hom := by
    change IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k₁ (AlgebraicClosure k₁))))
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  have : IsIntegralHom (C ↘ Spec (.of k₁)).geometricFiberProj :=
    inferInstanceAs (IsIntegralHom (pullback.fst _ _))
  have : IsIntegralHom (v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj) := by
    rw [hp]
    infer_instance
  have : IsIntegralHom v := IsIntegralHom.of_comp v (X ↘ Spec (.of k₀)).geometricFiberProj
  exact IsClosedImmersion.of_isPreimmersion v v.isClosedMap.isClosed_range

end AlgebraicGeometry
