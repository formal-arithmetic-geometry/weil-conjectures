/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
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
- `DerivedCategory.IsPerfect.bounded`, `DerivedCategory.IsPerfect.finite_homology`: a perfect
  complex over a Noetherian ring is bounded with finitely generated cohomology.
- `DerivedCategory.isPerfect_of_finiteTorAmplitude` (`sk-lem-finite`, Step 2): conversely, over a
  Noetherian ring a bounded complex with finitely generated cohomology and finite Tor amplitude
  is perfect.
- `DerivedCategory.IsPerfect.tensor_homology` (`sk-lem-finite`, Step 3): after a flat extension
  of scalars to a field the cohomology is finite dimensional and bounded.
- `DerivedCategory.IsPerfect.ihom_unit` (`sk-lem-finite`, Step 3): the dual
  `C^∨ = RHom_R(C, R)` of a perfect complex is perfect.
- `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit` (`prop-pod-biduality-at-the-point`): for
  any braiding of `D(R)`, the canonical biduality map `C ⟶ C^∨∨` is an isomorphism for a
  perfect `C`, where `C^∨ = RHom_R(C, R)`.
- `DerivedCategory.IsPerfect.isIso_ihomUnitTensorToIhom` (`prop-pod-biduality-at-the-point`):
  the canonical comparison `C^∨ ⊗ᴸ_R D ⟶ RHom_R(C, D)` is an isomorphism for a perfect `C` and
  any `D`.
- `DerivedCategory.nonempty_iso_homology_ihom` (`lem-pod-cohomology-of-dual-over-field`): over
  a field, `H^{-i}(C^∨) ≅ H^i(C)^∨`.

## Implementation notes

The biduality statements are deduced from the dualizability of a perfect complex for the
derived tensor product (`DerivedCategory.IsPerfect.isDualizable`), by the formal arguments of a
rigid braided monoidal category. The tensor–internal-Hom comparison needs no braiding and is
the canonical map `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`. The canonical biduality
map `C ⟶ C^∨∨` needs a braiding. `D(R)` only carries one up to `Nonempty`
(`DerivedCategory.nonempty_braidedCategory`), so biduality is stated for an arbitrary braiding
instance; `DerivedCategory.IsPerfect.nonempty_iso_ihom_ihom` is the braiding-free consequence.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped TensorProduct

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Blueprint `sk-def-perfect` (also `def-pod-perfect-point-complex`): perfect point complexes.

An object `C` of `D(R)` is *perfect* if it is isomorphic to the image of a bounded complex of
finitely generated projective `R`-modules. -/
def IsPerfect (C : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P)

/-- Perfectness is invariant under isomorphism. -/
theorem IsPerfect.of_iso {C D : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect)
    (e : C ≅ D) : D.IsPerfect := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := hC
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- The cohomology of `Q.obj L` in degree `i` is that of the complex `L`. -/
private noncomputable def homologyQObjIso (L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj L) ≅ L.homology i :=
  (homologyFunctorFactors _ i).app L

/-- A perfect complex is bounded: its cohomology is concentrated in some interval `[a, b]`. -/
theorem IsPerfect.exists_homologyConcentratedIn {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) : ∃ a b : ℤ, homologyConcentratedIn a b C := by
  obtain ⟨P, a, b, ha, hb, -, ⟨e⟩⟩ := hC
  let eH : ∀ i, (homologyFunctor (ModuleCat.{u} R) i).obj C ≅ P.homology i := fun i ↦
    (homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫ homologyQObjIso P i
  refine ⟨a, b, ?_, ?_⟩
  · change C.IsGE a
    rw [isGE_iff]
    intro i hi
    exact (P.exactAt_of_isGE a i hi).isZero_homology.of_iso (eH i)
  · change C.IsLE b
    rw [isLE_iff]
    intro i hi
    exact (P.exactAt_of_isLE b i hi).isZero_homology.of_iso (eH i)

/-- A perfect complex is bounded for the canonical t-structure. -/
theorem IsPerfect.bounded {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    TStructure.t.bounded C :=
  (exists_homologyConcentratedIn_iff_bounded C).1 hC.exists_homologyConcentratedIn

/-- The cohomology modules of a perfect complex over a Noetherian ring are finitely generated:
`H^i(P)` is a quotient of the submodule of cycles of the finitely generated module `P^i`. -/
theorem IsPerfect.finite_homology [IsNoetherianRing R] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) (i : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C) := by
  obtain ⟨P, a, b, -, -, hP, ⟨e⟩⟩ := hC
  let eH : (homologyFunctor (ModuleCat.{u} R) i).obj C ≅ P.homology i :=
    (homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫ homologyQObjIso P i
  have := (hP i).2
  have : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite R (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv eH.toLinearEquiv.symm

/-- Blueprint `sk-lem-finite` (Step 3 of its proof): flat extension of scalars to a field.

For a perfect complex `C` over a Noetherian ring `R` and an `R`-algebra `E` which is a field
(such as `E = Frac 𝒪_E` over `𝒪_E`), the spaces `E ⊗_R Hⁱ(C)` are finite dimensional and vanish
outside a finite interval. For `E` flat over `R` they are the cohomology spaces of
`C ⊗ᴸ_R E`, so this says that `C ⊗ᴸ_R E` is a perfect complex of `E`-vector spaces
(`DerivedCategory.isPerfect_iff`). -/
theorem IsPerfect.tensor_homology [IsNoetherianRing R] (E : Type*) [Field E] [Algebra R E]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    (∀ i, FiniteDimensional E (E ⊗[R] (homologyFunctor (ModuleCat.{u} R) i).obj C)) ∧
      ∃ a b : ℤ, ∀ i, i < a ∨ b < i →
        Subsingleton (E ⊗[R] (homologyFunctor (ModuleCat.{u} R) i).obj C) := by
  refine ⟨fun i ↦ have := hC.finite_homology i; inferInstance, ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hC.exists_homologyConcentratedIn
  refine ⟨a, b, fun i hi ↦ ?_⟩
  have hz : IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj C) := by
    rcases hi with hi | hi
    · exact C.isZero_of_isGE a i hi
    · exact C.isZero_of_isLE b i hi
  have := (ModuleCat.isZero_iff_subsingleton).1 hz
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul e m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- Blueprint `sk-lem-finite` (Step 2 of its proof): perfectness over a Noetherian ring.

Over a Noetherian ring `R`, a bounded complex `C` with finitely generated cohomology modules and
finite Tor amplitude is perfect. Take a bounded above resolution of `C` by finitely generated
free modules and truncate it in the lowest degree `a` of the Tor amplitude: the cokernel in
degree `a` is finitely presented of Tor dimension zero, hence flat, hence projective. -/
theorem isPerfect_of_finiteTorAmplitude [IsNoetherianRing R]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : TStructure.t.bounded C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C))
    (hTor : finiteTorAmplitude (ModuleCat.{u} R) C) : C.IsPerfect :=
  sorry

/-- Blueprint `sk-lem-finite` (Step 3 of its proof): the dual of a perfect point complex.

The dual `C^∨ = RHom_R(C, R)` of a perfect complex `C` is perfect: if `C` is represented by a
bounded complex `P` of finitely generated projective modules, `C^∨` is represented by the
termwise dual complex `Hom_R(P^{-i}, R)`, again bounded with finitely generated projective
terms. -/
theorem IsPerfect.ihom_unit {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    ((ihom C).obj (𝟙_ _)).IsPerfect :=
  sorry

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
/-- A complex of modules over a semisimple ring (for example a field) is quasi-isomorphic to the
complex of its cohomology modules with zero differential: a choice of sections of the
surjections `Z^i(L) ↠ H^i(L)` defines a quasi-isomorphism from the latter to `L`. -/
private theorem exists_quasiIso_of_zero_differential [IsSemisimpleRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (H : CochainComplex (ModuleCat.{u} R) ℤ) (φ : H ⟶ L), QuasiIso φ ∧ (∀ i j, H.d i j = 0) ∧
      ∀ i, Nonempty (H.X i ≅ L.homology i) := by
  have hs : ∀ i, ∃ s : L.homology i ⟶ L.cycles i, s ≫ L.homologyπ i = 𝟙 _ := fun i ↦ by
    have hπ : Function.Surjective (L.homologyπ i).hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have := Module.projective_of_isSemisimpleRing R (L.homology i)
    obtain ⟨g, hg⟩ := Module.projective_lifting_property (L.homologyπ i).hom LinearMap.id hπ
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  choose s hs using hs
  let H : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := fun i ↦ L.homology i
      d := fun _ _ ↦ 0 }
  let φ : H ⟶ L :=
    { f := fun i ↦ s i ≫ L.iCycles i }
  refine ⟨H, φ, ⟨fun i ↦ ?_⟩, fun _ _ ↦ rfl, fun i ↦ ⟨Iso.refl _⟩⟩
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

section Field

variable {K : Type u} [Field K] [HasDerivedCategory.{u} (ModuleCat.{u} K)]

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
    obtain ⟨H, φ, hφ, -, eH⟩ := exists_quasiIso_of_zero_differential L
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

For a perfect point complex `C` and any braiding of `D(R)`, the canonical biduality map
`C ⟶ C^∨∨`, where `C^∨ = RHom_R(C, R)`, is an isomorphism. -/
theorem IsPerfect.isIso_toIhomIhomUnit [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    IsIso (MonoidalClosed.toIhomIhomUnit C) := by
  obtain ⟨_⟩ := hC.isDualizable
  exact MonoidalClosed.isIso_toIhomIhomUnit C

/-- Biduality at the point without a chosen braiding: a perfect point complex `C` is isomorphic
to its double derived dual `C^∨∨`. This only asserts that some isomorphism exists; it is the
biduality map of `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit` for a braiding of `D(R)`, of
which only the existence is known (`DerivedCategory.nonempty_braidedCategory`). -/
theorem IsPerfect.nonempty_iso_ihom_ihom {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) :
    Nonempty (C ≅ (ihom ((ihom C).obj (𝟙_ _))).obj (𝟙_ _)) := by
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  have := hC.isIso_toIhomIhomUnit
  exact ⟨asIso (MonoidalClosed.toIhomIhomUnit C)⟩

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

section CohomologyDual

/-- Blueprint `lem-pod-cohomology-of-dual-over-field`: cohomology of the dual of a finite complex
over a field.

Over a field `R`, the cohomology of the dual `C^∨ = RHom_R(C, R)` of a complex `C` is the dual
of the cohomology: `H^{-i}(C^∨) ≅ H^i(C)^∨` for every `i`. The blueprint states this for a
perfect point complex `C` (a bounded complex of finite-dimensional vector spaces); it holds for
every `C`. Biduality `C ≅ C^∨∨` for perfect `C`, the other half of the node, is
`DerivedCategory.IsPerfect.isIso_toIhomIhomUnit`.

As in the blueprint, `C` is split: it is quasi-isomorphic to the complex `H` of its cohomology
spaces with zero differential. The single complex `R[0]` is K-injective, `R` being an injective
`R`-module, so `C^∨` is computed by the internal hom complex `Hom^•(H, R[0])`, which has zero
differential and the dual `Hom_R(H^i(C), R)` in degree `-i`.

The field is a commutative ring `R` with `IsField R`, so that the statement applies to the module
categories of the coefficient rings of the six-functor formalism, which are commutative
rings. -/
theorem nonempty_iso_homology_ihom (hR : IsField R) (C : DerivedCategory (ModuleCat.{u} R))
    (i : ℤ) :
    Nonempty ((homologyFunctor (ModuleCat.{u} R) (-i)).obj ((ihom C).obj (𝟙_ _)) ≅
      ModuleCat.of R (Module.Dual R ((homologyFunctor (ModuleCat.{u} R) i).obj C))) := by
  have : IsSemisimpleRing R := by
    let := hR.toField
    infer_instance
  obtain ⟨H, φ, hφ, hd, eH⟩ := exists_quasiIso_of_zero_differential (Q.objPreimage C)
  let P := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj H
  -- The unit `R[0]` of `D(R)`, a K-injective complex.
  let Y := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of R R)
  have hY : ∀ n, n ≠ 0 → IsZero (Y.X n) := fun n hn ↦
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have : ∀ n, Injective (Y.X n) := fun n ↦ by
    by_cases hn : n = 0
    · subst hn
      have := Module.injective_of_isSemisimpleRing R R
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).symm
        (Module.injective_object_of_injective_module R R)
    · exact (hY n hn).injective
  have : CochainComplex.IsKInjective Y := CochainComplex.isKInjective_of_injective Y 0
  have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} R) φ).2 hφ
  let eC : Qh.obj P ≅ C :=
    (quotientCompQhIso _).app H ≪≫ asIso (Q.map φ) ≪≫ Q.objObjPreimageIso C
  let U := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj Y
  -- `C^∨` is computed by the internal hom complex `K = Hom^•(H, R[0])`.
  let K := CochainComplex.internalHomObj H Y
  let e₁ : (ihom C).obj (𝟙_ _) ≅ Q.obj K :=
    (MonoidalClosed.internalHom.mapIso eC.op).app _ ≪≫
      ((ihom.adjunction (Qh.obj P)).rightAdjointUniq (tensorHomAdjunctionQhObj P)).app _ ≪≫
      (asIso ((internalHomQhObjUnit P).app U)).symm ≪≫ (quotientCompQhIso _).app K
  have hK : ∀ a b, K.d a b = 0 := fun a b ↦ by
    refine CochainComplex.internalHomObj_hom_ext fun p q hpq ↦ ?_
    rw [zero_comp, CochainComplex.internalHomObj_d_π H Y a b p q hpq (p + a) (q - a) rfl
      (by lia), hd]
    simp [Y]
  let e₂ : K.homology (-i) ≅ K.X (-i) :=
    (K.isoHomologyπ (-i - 1) (-i) (by simp) (hK _ _)).symm ≪≫
      K.iCyclesIso (-i) (-i + 1) (by simp) (hK _ _)
  -- In degree `-i`, the only nonzero factor of `K` is `Hom(H^i, R)`.
  let j₀ : CochainComplex.HomComplex.Triplet (-i) := ⟨i, 0, by lia⟩
  let e₃ : K.X (-i) ≅ (ihom (H.X i)).obj (ModuleCat.of R R) :=
    (by classical exact Pi.isoOfIsZero _ j₀ (fun T hT ↦ by
      have hq : T.q ≠ 0 := by
        intro hq
        apply hT
        obtain ⟨p, q, hpq⟩ := T
        simp only at hq
        subst hq
        obtain rfl : p = i := by lia
        rfl
      exact Functor.map_isZero _ (hY _ hq))) ≪≫
      (ihom (H.X i)).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  let f : H.X i ≅ (homologyFunctor (ModuleCat.{u} R) i).obj C :=
    (eH i).some ≪≫ ((homologyFunctorFactors _ i).app _).symm ≪≫
      (homologyFunctor (ModuleCat.{u} R) i).mapIso (Q.objObjPreimageIso C)
  exact ⟨(homologyFunctor (ModuleCat.{u} R) (-i)).mapIso e₁ ≪≫
    (homologyFunctorFactors _ (-i)).app K ≪≫ e₂ ≪≫ e₃ ≪≫
    (ModuleCat.homLinearEquiv (S := R)).toModuleIso ≪≫
    (f.symm.toLinearEquiv.dualMap).toModuleIso⟩

end CohomologyDual

end DerivedCategory
