/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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
- `DerivedCategory.IsPerfect.isDualizable` (`prop-pod-biduality-at-the-point`, Steps 1–3): a
  perfect complex is dualizable for the derived tensor product.
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

/-- Blueprint `pur9-def-perfect-complex`: Perfect complex of finite modules.

Also blueprint `sk-def-perfect` (also `def-pod-perfect-point-complex`): perfect point complexes.

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

/-- The image in `D(R)` of a bounded complex of finitely generated projective modules is
perfect. -/
lemma isPerfect_Q_obj (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    (Q.obj P).IsPerfect :=
  ⟨P, a, b, inferInstance, inferInstance, hP, ⟨Iso.refl _⟩⟩

/-- Perfect complexes are stable under shifts. -/
lemma IsPerfect.shift {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) (n : ℤ) :
    (C⟦n⟧).IsPerfect := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  exact (isPerfect_Q_obj (P⟦n⟧) (a - n) (b - n) fun i ↦ hP (i + n)).of_iso
    (((Q.commShiftIso n).app P) ≪≫ (shiftFunctor _ n).mapIso e.symm)

/-- The mapping cone of a morphism between bounded complexes of finitely generated projective
modules is again such a complex. -/
lemma isPerfect_Q_obj_mappingCone {P₁ P₂ : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P₁ ⟶ P₂)
    (a₁ b₁ a₂ b₂ : ℤ) [P₁.IsStrictlyGE a₁] [P₁.IsStrictlyLE b₁] [P₂.IsStrictlyGE a₂]
    [P₂.IsStrictlyLE b₂] (h₁ : ∀ i, Module.Projective R (P₁.X i) ∧ Module.Finite R (P₁.X i))
    (h₂ : ∀ i, Module.Projective R (P₂.X i) ∧ Module.Finite R (P₂.X i)) :
    (Q.obj (CochainComplex.mappingCone φ)).IsPerfect := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (min (a₁ - 1) a₂) :=
    CochainComplex.isStrictlyGE_mappingCone φ a₁ a₂ _
  have : (CochainComplex.mappingCone φ).IsStrictlyLE (max (b₁ - 1) b₂) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega), P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  refine isPerfect_Q_obj _ (min (a₁ - 1) a₂) (max (b₁ - 1) b₂) fun i ↦ ?_
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd (P₁.X (i + 1)) (P₂.X i)
  have := (h₁ (i + 1)).1
  have := (h₁ (i + 1)).2
  have := (h₂ i).1
  have := (h₂ i).2
  exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
    Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- Perfect complexes are stable under extensions: in a distinguished triangle
`C₁ ⟶ C₂ ⟶ C₃ ⟶ C₁[1]` with `C₁` and `C₃` perfect, `C₂` is perfect. The map `C₃ ⟶ C₁[1]` lifts
to a morphism of complexes, its source being K-projective, and `C₂[1]` is its mapping cone. -/
lemma isPerfect_obj₂_of_distTriang
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : T.obj₁.IsPerfect) (h₃ : T.obj₃.IsPerfect) :
    T.obj₂.IsPerfect := by
  obtain ⟨P₁, a₁, b₁, _, _, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, a₃, b₃, _, _, hP₃, ⟨e₃⟩⟩ := h₃
  have : ∀ n, Projective (P₃.X n) := fun n ↦ by
    have := (hP₃ n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : P₃.IsKProjective := CochainComplex.isKProjective_of_projective _ b₃
  have := P₁.isStrictlyGE_shift a₁ 1 (a₁ - 1) (by omega)
  have := P₁.isStrictlyLE_shift b₁ 1 (b₁ - 1) (by omega)
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P₃ (P₁⟦(1 : ℤ)⟧)
    (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).inv)
  have hcomm : Q.map ψ ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).hom ≫ e₁.inv⟦(1 : ℤ)⟧' =
      e₃.inv ≫ T.mor₃ := by
    rw [hψ]
    simp [← Functor.map_comp]
  obtain ⟨f, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ hT))
    (Arrow.isoMk e₃.symm (((Q.commShiftIso (1 : ℤ)).app P₁) ≪≫ (shiftFunctor _ 1).mapIso e₁.symm)
      hcomm.symm)
  have hcone := isPerfect_Q_obj_mappingCone ψ a₃ b₃ (a₁ - 1) (b₁ - 1) hP₃ fun i ↦ hP₁ (i + 1)
  exact ((hcone.of_iso (Pretriangulated.Triangle.π₃.mapIso f)).shift (-1)).of_iso
    ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)

section FiniteTorAmplitude

variable [IsNoetherianRing R]

/-- A complex of flat modules concentrated in degree `b`, whose cohomology in degree `b` is
finitely generated, has a perfect image in `D(R)`: its term in degree `b` is its cohomology, a
finitely presented flat module, hence projective. -/
private lemma isPerfect_Q_obj_of_flat (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyGE b] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hb : Module.Finite R (P.homology b)) :
    (Q.obj P).IsPerfect := by
  refine isPerfect_Q_obj P b b fun i ↦ ?_
  have : Module.Flat R (P.X i) := (ModuleCat.flat_iff_flat _).1 (hP i)
  have : Module.Finite R (P.X i) := by
    by_cases hi : i = b
    · subst hi
      have := P.isIso_homologyπ (i - 1) i (by simp)
        ((P.isZero_of_isStrictlyGE i (i - 1) (by omega)).eq_of_src _ _)
      have := P.isIso_iCycles i (i + 1) (by simp)
        ((P.isZero_of_isStrictlyLE i (i + 1) (by omega)).eq_of_tgt _ _)
      exact Module.Finite.equiv
        ((asIso (P.homologyπ i)).symm ≪≫ asIso (P.iCycles i)).toLinearEquiv
    · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.1 <| by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact P.isZero_of_isStrictlyGE b i hi
        · exact P.isZero_of_isStrictlyLE b i hi
      infer_instance
  have := Module.finitePresentation_of_finite R (P.X i)
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- The base case of `DerivedCategory.isPerfect_of_finiteTorAmplitude`: an object of Tor
amplitude in `[c, b]` with `b ≤ c` and finitely generated cohomology is perfect. It is
represented by a complex of flat modules concentrated in degree `b`. -/
private lemma isPerfect_of_torAmplitudeIn_of_le {c b : ℤ} (hbc : b ≤ c)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    C.IsPerfect := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hC
  have : P.IsStrictlyGE b := CochainComplex.isStrictlyGE_of_ge P b c hbc
  refine (isPerfect_Q_obj_of_flat P b hP ?_).of_iso e
  have := hfin b
  exact Module.Finite.equiv
    ((homologyFunctor _ b).mapIso e.symm ≪≫ (homologyFunctorFactors _ b).app P).toLinearEquiv

/-- The induction step of `DerivedCategory.isPerfect_of_finiteTorAmplitude`. Let `C` have Tor
amplitude in `[c, b]` with `c < b` and finitely generated cohomology. Represent `C` by a complex
`P` of flat modules in degrees `[c, b]`, choose a finite free module `F` mapping onto
`H^b(C) = P^b / d(P^{b-1})` and lift it to a map `φ : F[-b] ⟶ P`. Its mapping cone `C'` is a
complex of flat modules in degrees `[c, b]` with `H^b(C') = 0`, so it has Tor amplitude in
`[c, b - 1]`, and its cohomology is finitely generated. If `C'` is perfect, so is `C`, as an
extension of `C'` by the perfect complex `F[-b]`. -/
private lemma exists_isPerfect_imp_of_torAmplitudeIn {c b : ℤ} (hcb : c < b)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    ∃ C' : DerivedCategory (ModuleCat.{u} R), torAmplitudeIn _ c (b - 1) C' ∧
      (∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C')) ∧
      (C'.IsPerfect → C.IsPerfect) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hC
  let H (i : ℤ) := homologyFunctor (ModuleCat.{u} R) i
  let eH (L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
      (H i).obj (Q.obj L) ≅ L.homology i :=
    (homologyFunctorFactors _ i).app L
  have hPfin (i : ℤ) : Module.Finite R (P.homology i) := by
    have := hfin i
    exact Module.Finite.equiv ((H i).mapIso e.symm ≪≫ eH P i).toLinearEquiv
  -- a finite free module `F` mapping onto `H^b(P)`, lifted to the cycles of `P` in degree `b`
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (P.homology b)
  have hπ : Function.Surjective (P.homologyπ b).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (P.homologyπ b).hom g hπ
  let F := ModuleCat.of R (Fin n → R)
  let S : CochainComplex (ModuleCat.{u} R) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) b).obj F
  let φ : S ⟶ P := HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom h ≫ P.iCycles b)
    (by rintro k (rfl : b + 1 = k); simp)
  let K := CochainComplex.mappingCone φ
  let T := CochainComplex.mappingCone.triangle φ
  have hT : Q.mapTriangle.obj T ∈ distTriang _ := mappingCone_triangle_distinguished φ
  have hSX (i : ℤ) (hi : i ≠ b) : IsZero (S.X i) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  have hS : (Q.obj S).IsPerfect := isPerfect_Q_obj S b b fun i ↦ by
    by_cases hi : i = b
    · subst hi
      let e' := (HomologicalComplex.singleObjXSelf (.up ℤ) i F).toLinearEquiv
      exact ⟨Module.Projective.of_equiv e'.symm, Module.Finite.equiv e'.symm⟩
    · have : Subsingleton (S.X i) := ModuleCat.isZero_iff_subsingleton.1 (hSX i hi)
      have : Module.Flat R (S.X i) :=
        (ModuleCat.flat_iff_flat _).1 (ObjectProperty.flat_of_isZero (hSX i hi))
      have := Module.finitePresentation_of_finite R (S.X i)
      exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩
  -- the mapping cone is a complex of flat modules in degrees `[c, b]`
  have hSflat (i : ℤ) : Module.Flat R (S.X i) := by
    by_cases hi : i = b
    · subst hi
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) i F).toLinearEquiv
    · exact (ModuleCat.flat_iff_flat _).1 (ObjectProperty.flat_of_isZero (hSX i hi))
  have hKflat (i : ℤ) : ObjectProperty.flat (K.X i) := by
    have := hSflat (i + 1)
    have := (ModuleCat.flat_iff_flat _).1 (hP i)
    exact (ModuleCat.flat_iff_flat _).2 (Module.Flat.of_linearEquiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl ≪≫
        ModuleCat.biprodIsoProd (S.X (i + 1)) (P.X i)).toLinearEquiv)
  have : K.IsStrictlyGE c := CochainComplex.isStrictlyGE_mappingCone φ b c c
  have : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨S.isZero_of_isStrictlyLE b _ (by omega), P.isZero_of_isStrictlyLE b _ (by omega)⟩
  -- `H^b(φ)` is surjective, so `H^b(K) = 0`
  have hepi : Epi (HomologicalComplex.homologyMap φ b) := by
    have : IsIso (S.iCycles b) := S.isIso_iCycles b (b + 1) (by simp)
      ((hSX (b + 1) (by omega)).eq_of_tgt _ _)
    have hc : HomologicalComplex.cyclesMap φ b = S.iCycles b ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) b F).hom ≫ ModuleCat.ofHom h := by
      rw [← cancel_mono (P.iCycles b), HomologicalComplex.cyclesMap_i]
      simp [φ, HomologicalComplex.mkHomFromSingle_f]
    have : Epi (ModuleCat.ofHom h ≫ P.homologyπ b) := by
      rw [ModuleCat.epi_iff_surjective]
      change Function.Surjective ((P.homologyπ b).hom ∘ₗ h)
      rw [hh]
      exact hg
    have : Epi (S.homologyπ b ≫ HomologicalComplex.homologyMap φ b) := by
      rw [HomologicalComplex.homologyπ_naturality, hc]
      simp only [Category.assoc]
      infer_instance
    exact epi_of_epi (S.homologyπ b) _
  have hKb : IsZero (K.homology b) :=
    (CochainComplex.homologyMap_exact₃_of_distTriang T hT b (b + 1)).isZero_X₂
      ((CochainComplex.homologyMap_exact₂_of_distTriang T hT b).epi_f_iff.1 hepi)
      (((S.exactAt_of_isLE b (b + 1) (by omega)).isZero_homology).eq_of_tgt _ _)
  have hKle : (Q.obj K).IsLE (b - 1) := by
    rw [isLE_Q_obj_iff, CochainComplex.isLE_iff]
    intro i hi
    obtain rfl | hi := eq_or_lt_of_le (show b ≤ i by omega)
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hKb
    · exact K.exactAt_of_isLE b i hi
  have hK' : torAmplitudeIn _ c (b - 1) (Q.obj K) := fun N ↦ by
    refine ⟨(torAmplitudeIn_Q_obj_of_flat K c b hKflat N).1, ?_⟩
    have := isLE_tensor (Q.obj K) ((singleFunctor _ 0).obj N) (b - 1) 0
    rwa [add_zero] at this
  -- the cohomology of `K` is finitely generated
  have hKfin (i : ℤ) : Module.Finite R ((H i).obj (Q.obj K)) := by
    have : Module.Finite R (T.obj₂.homology i) := hPfin i
    have : Module.Finite R (T.obj₁.homology (i + 1)) := by
      have := hS.finite_homology (i + 1)
      exact Module.Finite.equiv (eH S (i + 1)).toLinearEquiv
    have : Module.Finite R (K.homology i) :=
      (CochainComplex.homologyMap_exact₃_of_distTriang T hT i (i + 1)).moduleFinite_X₂
    exact Module.Finite.equiv (eH K i).toLinearEquiv.symm
  exact ⟨Q.obj K, hK', hKfin, fun hK ↦ (isPerfect_obj₂_of_distTriang _ hT hS hK).of_iso e⟩

/-- Induction on the length `b - c` of the Tor amplitude: an object of Tor amplitude in `[c, b]`
with finitely generated cohomology is perfect. -/
private lemma isPerfect_of_torAmplitudeIn (n : ℕ) {c b : ℤ} (hn : b - c ≤ n)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    C.IsPerfect := by
  induction n generalizing b C with
  | zero => exact isPerfect_of_torAmplitudeIn_of_le (by omega) hC hfin
  | succ n ih =>
    by_cases hbc : b ≤ c
    · exact isPerfect_of_torAmplitudeIn_of_le hbc hC hfin
    · obtain ⟨C', hC', hfin', himp⟩ := exists_isPerfect_imp_of_torAmplitudeIn (by omega) hC hfin
      exact himp (ih (by omega) hC' hfin')

end FiniteTorAmplitude

/-- Blueprint `sk-lem-finite` (Step 2 of its proof): perfectness over a Noetherian ring.

Over a Noetherian ring `R`, a bounded complex `C` with finitely generated cohomology modules and
finite Tor amplitude is perfect. The proof is by induction on the length of the Tor amplitude
`[c, b]`. If `b ≤ c`, then `C` is represented by a complex of flat modules concentrated in
degree `b`, whose term is finitely presented and flat, hence projective. Otherwise a finite free
module `F` maps onto `H^b(C)`, and the cone of the lifted map `F[-b] ⟶ C` has Tor amplitude in
`[c, b - 1]` and finitely generated cohomology; `C` is an extension of it by `F[-b]`. The
boundedness hypothesis is implied by the finite Tor amplitude. -/
theorem isPerfect_of_finiteTorAmplitude [IsNoetherianRing R]
    {C : DerivedCategory (ModuleCat.{u} R)} (_hC : TStructure.t.bounded C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C))
    (hTor : finiteTorAmplitude (ModuleCat.{u} R) C) : C.IsPerfect := by
  obtain ⟨c, d, hcd⟩ := hTor
  exact isPerfect_of_torAmplitudeIn (d - c).toNat (by omega) hcd hfin

section Field

variable {K : Type u} [Field K] [HasDerivedCategory.{u} (ModuleCat.{u} K)]

end Field

section Biduality

end Biduality

section CohomologyDual

end CohomologyDual

end DerivedCategory
