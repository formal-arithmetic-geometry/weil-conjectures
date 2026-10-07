/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Perfect complexes over a commutative ring

Let `R` be a commutative ring. An object `C` of the derived category `D(R)` is *perfect* if it
is isomorphic to the image of a bounded complex of finitely generated projective `R`-modules.
In the Poincaré duality chapter `R` is the coefficient ring of the point `s = Spec k`, and the
perfect objects of `D(R)` are the *perfect point complexes*.

## Main definitions

- `DerivedCategory.IsPerfect`: `C` is quasi-isomorphic to a bounded complex of finitely
  generated projective `R`-modules.

## Main statements

- `DerivedCategory.isPerfect_iff` (`lem-pod-perfect-point-complex-field`): over a field, `C`
  is perfect if and only if it is bounded with finite-dimensional cohomology.
- `DerivedCategory.IsPerfect.nonempty_iso_ihom_ihom` (`prop-pod-biduality-at-the-point`):
  biduality `C ≅ C^∨∨` for a perfect `C`, where `C^∨ = RHom_R(C, R)`.
- `DerivedCategory.IsPerfect.isIso_ihomUnitTensorToIhom` (`prop-pod-biduality-at-the-point`):
  the canonical comparison `C^∨ ⊗ᴸ_R D ⟶ RHom_R(C, D)` is an isomorphism for a perfect `C` and
  any `D`.

## Implementation notes

The biduality statements are deduced from the dualizability of a perfect complex for the
derived tensor product (`DerivedCategory.IsPerfect.isDualizable`), by the formal arguments of a
rigid braided monoidal category. The tensor–internal-Hom comparison needs no braiding and is
the canonical map `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`. The canonical biduality
map `C ⟶ C^∨∨` needs a braiding, and `D(R)` only carries one up to `Nonempty`
(`DerivedCategory.nonempty_braidedCategory`), so biduality is stated as `Nonempty (_ ≅ _)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Blueprint `sk-def-perfect` (also `def-pod-perfect-point-complex`): perfect point complexes.

An object `C` of `D(R)` is *perfect* if it is isomorphic to the image of a bounded complex of
finitely generated projective `R`-modules. -/
def IsPerfect (C : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P)

section Field

variable {K : Type u} [Field K] [HasDerivedCategory.{u} (ModuleCat.{u} K)]

omit [HasDerivedCategory.{u} (ModuleCat.{u} K)] in
/-- A complex of vector spaces is quasi-isomorphic to the complex of its cohomology spaces with
zero differential: a choice of sections of the surjections `Z^i(L) ↠ H^i(L)` defines a
quasi-isomorphism from the latter to `L`. -/
private theorem exists_quasiIso_of_zero_differential (L : CochainComplex (ModuleCat.{u} K) ℤ) :
    ∃ (H : CochainComplex (ModuleCat.{u} K) ℤ) (φ : H ⟶ L), QuasiIso φ ∧
      ∀ i, Nonempty (H.X i ≅ L.homology i) := by
  have hs : ∀ i, ∃ s : L.homology i ⟶ L.cycles i, s ≫ L.homologyπ i = 𝟙 _ := fun i ↦ by
    have hπ : Function.Surjective (L.homologyπ i).hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    obtain ⟨g, hg⟩ := (L.homologyπ i).hom.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 hπ)
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  choose s hs using hs
  let H : CochainComplex (ModuleCat.{u} K) ℤ :=
    { X := fun i ↦ L.homology i
      d := fun _ _ ↦ 0 }
  let φ : H ⟶ L :=
    { f := fun i ↦ s i ≫ L.iCycles i }
  refine ⟨H, φ, ⟨fun i ↦ ?_⟩, fun i ↦ ⟨Iso.refl _⟩⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₁ := H.isIso_homologyπ (i - 1) i (by simp) rfl
  have h₂ := H.isIso_iCycles i (i + 1) (by simp) rfl
  have hc : HomologicalComplex.cyclesMap φ i = H.iCycles i ≫ s i := by
    rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i, Category.assoc]
  have : HomologicalComplex.homologyMap φ i = inv (H.homologyπ i) ≫ H.iCycles i := by
    rw [← cancel_epi (H.homologyπ i), HomologicalComplex.homologyπ_naturality, hc,
      Category.assoc, hs, Category.comp_id, IsIso.hom_inv_id_assoc]
  rw [this]
  infer_instance

/-- The cohomology of `Q.obj L` in degree `i` is that of the complex `L`. -/
private noncomputable def homologyQObjIso (L : CochainComplex (ModuleCat.{u} K) ℤ) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} K) i).obj (Q.obj L) ≅ L.homology i :=
  (homologyFunctorFactors _ i).app L

/-- Blueprint `lem-pod-perfect-point-complex-field`: perfect point complexes over a field.

Over a field `K`, an object `C` of `D(K)` is perfect if and only if it is bounded and all its
cohomology spaces `H^i(C)` are finite dimensional over `K`. -/
theorem isPerfect_iff (C : DerivedCategory (ModuleCat.{u} K)) :
    C.IsPerfect ↔ (∃ a b : ℤ, C.IsGE a ∧ C.IsLE b) ∧
      ∀ i, Module.Finite K ((homologyFunctor (ModuleCat.{u} K) i).obj C) := by
  constructor
  · rintro ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩
    let eH : ∀ i, (homologyFunctor (ModuleCat.{u} K) i).obj C ≅ P.homology i := fun i ↦
      (homologyFunctor (ModuleCat.{u} K) i).mapIso e ≪≫ homologyQObjIso P i
    refine ⟨⟨a, b, ?_, ?_⟩, fun i ↦ ?_⟩
    · rw [isGE_iff]
      intro i hi
      exact (P.exactAt_of_isGE a i hi).isZero_homology.of_iso (eH i)
    · rw [isLE_iff]
      intro i hi
      exact (P.exactAt_of_isLE b i hi).isZero_homology.of_iso (eH i)
    · have := (hP i).2
      have : Module.Finite K (P.cycles i) :=
        Module.Finite.of_injective (P.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      have : Module.Finite K (P.homology i) :=
        Module.Finite.of_surjective (P.homologyπ i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      exact Module.Finite.equiv (eH i).toLinearEquiv.symm
  · rintro ⟨⟨a, b, ha, hb⟩, hfin⟩
    let L := Q.objPreimage C
    let eL : Q.obj L ≅ C := Q.objObjPreimageIso C
    obtain ⟨H, φ, hφ, eH⟩ := exists_quasiIso_of_zero_differential L
    let e : ∀ i, (homologyFunctor (ModuleCat.{u} K) i).obj C ≅ H.X i := fun i ↦
      (homologyFunctor (ModuleCat.{u} K) i).mapIso eL.symm ≪≫ homologyQObjIso L i ≪≫
        (eH i).some.symm
    refine ⟨H, a, b, ?_, ?_, fun i ↦ ⟨?_, ?_⟩, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact (C.isZero_of_isGE a i hi).of_iso (e i).symm
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (C.isZero_of_isLE b i hi).of_iso (e i).symm
    · exact Module.Projective.of_free
    · exact Module.Finite.equiv (e i).toLinearEquiv
    · have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} K) φ).2 hφ
      exact ⟨eL.symm ≪≫ (asIso (Q.map φ)).symm⟩

end Field

section Biduality

/-- Blueprint `prop-pod-biduality-at-the-point` (Steps 1–3 of its proof): a perfect point
complex is dualizable for the derived tensor product of `D(R)`.

A single finitely generated projective module is dualizable, with dual `Hom_R(P, R)`; a bounded
complex of such modules is dualizable, with dual the termwise dual complex, by induction on the
length using the truncation triangles; and dualizability is invariant under isomorphism. -/
theorem IsPerfect.isDualizable {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    IsDualizable C :=
  sorry

/-- Blueprint `prop-pod-biduality-at-the-point`: biduality at the point.

For a perfect point complex `C`, there is an isomorphism `C ≅ C^∨∨` with the double derived dual,
where `C^∨ = RHom_R(C, R)`. This only asserts that some isomorphism exists, not that the
canonical biduality map is one: that map needs a braiding of `D(R)`, which is only known to
exist (`DerivedCategory.nonempty_braidedCategory`). -/
theorem IsPerfect.nonempty_iso_ihom_ihom {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) :
    Nonempty (C ≅ (ihom ((ihom C).obj (𝟙_ _))).obj (𝟙_ _)) := by
  obtain ⟨_⟩ := hC.isDualizable
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let := BraidedCategory.exactPairing_swap C Cᘁ
  let e : (ihom C).obj (𝟙_ _) ≅ Cᘁ := MonoidalClosed.ihomObjUnitIso Cᘁ C
  let := exactPairingCongrRight (X := C) e
  exact ⟨(MonoidalClosed.ihomObjUnitIso C ((ihom C).obj (𝟙_ _))).symm⟩

/-- Blueprint `prop-pod-biduality-at-the-point`: biduality at the point.

For a perfect point complex `C` and every object `D` of `D(R)`, the canonical tensor–internal-Hom
comparison `C^∨ ⊗ᴸ_R D ⟶ RHom_R(C, D)` is an isomorphism. -/
theorem IsPerfect.isIso_ihomUnitTensorToIhom {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) (D : DerivedCategory (ModuleCat.{u} R)) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom C D) := by
  obtain ⟨_⟩ := hC.isDualizable
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let := BraidedCategory.exactPairing_swap C Cᘁ
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Cᘁ C D

end Biduality

end DerivedCategory
