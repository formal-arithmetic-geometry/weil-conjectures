/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Geometric reducedness from generic stalks

Source: Stacks Project, Varieties, Tags 04KS (3) and 035W
(blueprint: lem-pur-geometric-reducedness-from-generic-stalks).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem tensor_reduced_of_jointly_injective
    {k A L ι : Type u} [Field k] [CommRing A] [Algebra k A]
    [Field L] [Algebra k L] (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra k (B i)]
    (f : ∀ i, A →ₐ[k] B i)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0)
    (hB : ∀ i, _root_.IsReduced (B i ⊗[k] L)) :
    _root_.IsReduced (A ⊗[k] L) := by
  classical
  let b := Module.Free.chooseBasis k L
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have natural (i : ι) (z : A ⊗[k] L) (j : Module.Free.ChooseBasisIndex k L) :
      TensorProduct.equivFinsuppOfBasisRight b
          (Algebra.TensorProduct.map (f i) (AlgHom.id k L) z) j = f i (e z j) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [e]
    | tmul a l => simp [e]
    | add z w hz hw => simp [hz, hw]
  constructor
  intro z hz
  apply e.injective
  apply Finsupp.ext
  intro j
  simp only [map_zero, Finsupp.zero_apply]
  apply hf
  intro i
  have := hB i
  have hi : Algebra.TensorProduct.map (f i) (AlgHom.id k L) z = 0 :=
    (hz.map (Algebra.TensorProduct.map (f i) (AlgHom.id k L))).eq_zero
  rw [← natural i z j, hi]
  simp

private theorem closure_image_component
    {Y X : Type u} [TopologicalSpace Y] [TopologicalSpace X]
    {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    {C : Set Y} (hC : C ∈ irreducibleComponents Y) :
    closure (f '' C) ∈ irreducibleComponents X := by
  obtain ⟨D, hD, hCD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure (f '' C)) (hC.1.image f hf.continuous.continuousOn).closure
  have hsub : C ⊆ f ⁻¹' D := by
    intro y hy
    exact hCD (subset_closure ⟨y, hy, rfl⟩)
  have hne : (D ∩ Set.range f).Nonempty := by
    obtain ⟨y, hy⟩ := hC.1.1
    exact ⟨f y, hsub hy, y, rfl⟩
  have heq : f ⁻¹' D = C :=
    Set.Subset.antisymm (hC.2 (preimage_mem_irreducibleComponents hD hf hne).1 hsub) hsub
  have hclosure := closure_image_preimage_of_isPreirreducible f hf.isOpenMap D
    (by obtain ⟨y, hy⟩ := hC.1.1; exact ⟨y, hsub hy⟩) hD.1.2
    (isClosed_of_mem_irreducibleComponents _ hD)
  rw [heq] at hclosure
  rwa [hclosure]

private theorem tensor_reduced_of_minimal_stalks
    (k A L : Type u) [Field k] [CommRing A] [Algebra k A] [_root_.IsReduced A]
    [Field L] [Algebra k L]
    (h : ∀ (p : PrimeSpectrum A), p.asIdeal ∈ minimalPrimes A →
      ∀ [Algebra k ((Spec (.of A)).presheaf.stalk p)],
        algebraMap k ((Spec (.of A)).presheaf.stalk p) =
          (StructureSheaf.toStalk A p).hom.comp (algebraMap k A) →
        _root_.IsReduced (((Spec (.of A)).presheaf.stalk p) ⊗[k] L)) :
    _root_.IsReduced (A ⊗[k] L) := by
  let B (p : minimalPrimes A) : Type u :=
    (Spec (.of A)).presheaf.stalk (⟨p.1, p.2.1.1⟩ : PrimeSpectrum A)
  let (p : minimalPrimes A) : Algebra k (B p) :=
    ((StructureSheaf.toStalk A ⟨p.1, p.2.1.1⟩).hom.comp (algebraMap k A)).toAlgebra
  let f (p : minimalPrimes A) : A →ₐ[k] B p :=
    { (StructureSheaf.toStalk A ⟨p.1, p.2.1.1⟩).hom with commutes' := fun _ ↦ rfl }
  apply tensor_reduced_of_jointly_injective (L := L) B f
  · intro a ha
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro P hP
    let := hP
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
    apply hpP
    let : p.IsPrime := hp.1.1
    let q : PrimeSpectrum A := ⟨p, hp.1.1⟩
    let : Algebra A ((Spec (.of A)).presheaf.stalk q) :=
      StructureSheaf.stalkAlgebra A q
    have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q) p :=
      StructureSheaf.IsLocalization.to_stalk A q
    have hz : algebraMap A ((Spec (.of A)).presheaf.stalk q) a = 0 := ha ⟨p, hp⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      ((Spec (.of A)).presheaf.stalk q) p a).mp (hz ▸ Ideal.zero_mem _)
  · intro p
    exact h ⟨p.1, p.2.1.1⟩ p.2 rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reduced scheme over a field is geometrically reduced if every generic stalk of
an irreducible component remains reduced after every field extension.
Source: Stacks Project, Varieties, Tags 04KS (3) and 035W.
(blueprint: lem-pur-geometric-reducedness-from-generic-stalks)

Proof:
1. For an affine open Spec A, each minimal prime gives a generic point of a global
   irreducible component. The affine stalk-localization theorem identifies its stalk with
   A localized at that prime, as a k-algebra. Thus every such localization tensor L is reduced.
2. The maps from the reduced ring A to its minimal-prime localizations jointly detect zero:
   each kernel is its minimal prime, and the intersection of these primes is the nilradical.
3. After tensoring with L these maps still jointly detect zero. Express a tensor using finitely
   many linearly independent coefficients in L, extend them to a basis, and apply the coordinate
   functionals. Every coefficient vanishes in all minimal-prime localizations, hence is zero.
   A nilpotent tensor has zero image in each reduced localization tensor L, so it is zero.
4. The affine fibre-product theorem identifies the base change of Spec A with Spec (A tensor L).
   Open immersions are stable under base change, so these reduced affine charts cover the base
   change of X. Their localizations, hence all its stalks, are reduced. Thus the base change is
   reduced for every L, as required. The empty scheme causes no exception.

The algebra structure on a stalk is bound with its defining equality to the composite
k → O(Spec k, p(x)) → O(X, x), so that the tensor uses the given structure morphism. -/
theorem geometricallyReduced_of_generic_stalks
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsReduced X]
    (h : ∀ (Z : Set X), Z ∈ irreducibleComponents X →
      ∀ (ξ : X), IsGenericPoint ξ Z →
      ∀ (L : Type u) [Field L] [Algebra k L] [Algebra k (X.presheaf.stalk ξ)],
        algebraMap k (X.presheaf.stalk ξ) =
          (StructureSheaf.toStalk k ((X ↘ Spec (.of k)) ξ) ≫
            (X ↘ Spec (.of k)).stalkMap ξ).hom →
        _root_.IsReduced ((X.presheaf.stalk ξ) ⊗[k] L)) :
    GeometricallyReduced (X ↘ Spec (.of k)) := by
  classical
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ _
  let f := X ↘ Spec (.of k)
  let y := Spec.map (CommRingCat.ofHom (algebraMap k L))
  apply +allowSynthFailures @IsReduced.of_openCover _
    (X.affineOpenCover.openCover.pullback₁ (CategoryTheory.Limits.pullback.fst f y))
  intro i
  change IsReduced (CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.fst f y)
    (X.affineOpenCover.f i))
  refine @isReduced_of_isOpenImmersion _ _
    (CategoryTheory.Limits.pullbackSymmetry _ _).hom inferInstance ?_
  refine @isReduced_of_isOpenImmersion _ _
    (CategoryTheory.Limits.pullbackRightPullbackFstIso f y (X.affineOpenCover.f i)).hom
    inferInstance ?_
  let A := X.affineOpenCover.X i
  let e : Spec A ⟶ X := X.affineOpenCover.f i
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e ≫ f)
  let : Algebra k A := φ.hom.toAlgebra
  have : _root_.IsReduced A :=
    (affine_isReduced_iff A).mp (isReduced_of_isOpenImmersion e)
  have hAL : _root_.IsReduced (A ⊗[k] L) := by
    apply tensor_reduced_of_minimal_stalks k A L
    intro p hp aS haS
    have hpC : closure ({p} : Set (PrimeSpectrum A)) ∈
        irreducibleComponents (PrimeSpectrum A) := by
      rwa [← PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
        PrimeSpectrum.vanishingIdeal_singleton]
    have hC := closure_image_component e.isOpenEmbedding hpC
    have hg : IsGenericPoint (e p) (closure (e '' closure ({p} : Set (PrimeSpectrum A)))) :=
      (show IsGenericPoint p (closure ({p} : Set (PrimeSpectrum A))) from rfl).image
        e.continuous
    let aT : Algebra k (X.presheaf.stalk (e p)) :=
      (StructureSheaf.toStalk k (f (e p)) ≫ f.stalkMap (e p)).hom.toAlgebra
    have hT : _root_.IsReduced ((X.presheaf.stalk (e p)) ⊗[k] L) :=
      h _ hC (e p) hg L rfl
    let g : X.presheaf.stalk (e p) →ₐ[k] (Spec A).presheaf.stalk p :=
      { (e.stalkMap p).hom with
        commutes' := by
          intro c
          change (e.stalkMap p) ((StructureSheaf.toStalk k (f (e p)) ≫
            f.stalkMap (e p)) c) = algebraMap k ((Spec A).presheaf.stalk p) c
          rw [← CommRingCat.comp_apply, Category.assoc,
            ← Scheme.Hom.stalkMap_comp e f p]
          change (StructureSheaf.toStalk k ((e ≫ f) p) ≫ (e ≫ f).stalkMap p) c = _
          rw [← hφ]
          exact (stalkMap_toStalk_apply φ p c).trans
            (RingHom.congr_fun haS.symm c) }
    let eg := AlgEquiv.ofBijective g
      (asIso (e.stalkMap p)).commRingCatIsoToRingEquiv.bijective
    exact isReduced_of_injective
      (Algebra.TensorProduct.map eg.symm.toAlgHom (AlgHom.id k L))
      (by
        exact (Algebra.TensorProduct.congr eg.symm (AlgEquiv.refl : L ≃ₐ[k] L)).injective)
  have hspec : IsReduced (CategoryTheory.Limits.pullback (Spec.map φ) y) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k A L).hom
  exact isReduced_of_isOpenImmersion
    (CategoryTheory.Limits.pullback.congrHom (g₁ := y) hφ.symm rfl).hom

end AlgebraicGeometry
