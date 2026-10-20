/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# Constant coefficient tensor comparison for an open immersion

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
lemma lem-exc-constant-tensor (blueprint: lem-exc-constant-tensor).

The comparison is the existing unbounded projection-formula morphism at the constant
module sheaf in degree zero. Its target is identified with the tensor by the constant
module on the source through the canonical constant inverse-image isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ExceptionalConstantTensor

open CategoryTheory CategoryTheory.Limits

universe v

variable {R : Type v} [CommRing R]

/-- Free module on the elements of a module, with its canonical finite basis when finite. -/
private noncomputable abbrev freeModule (M : ModuleCat.{v} R) := ModuleCat.of R (M →₀ R)

private noncomputable def cover (M : ModuleCat.{v} R) : freeModule M ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination R (fun x : M ↦ x))

private theorem cover_surjective (M : ModuleCat.{v} R) : Function.Surjective (cover M) := by
  intro x
  exact ⟨Finsupp.single x 1, by simp [cover]⟩

private noncomputable def syzygy (M : ModuleCat.{v} R) : ℕ → ModuleCat.{v} R
  | 0 => M
  | n + 1 => ModuleCat.of R (LinearMap.ker (cover (syzygy M n)).hom)

private theorem finite_syzygy [Finite R] (M : ModuleCat.{v} R) [Finite M] (n : ℕ) :
    Finite (syzygy M n) := by
  classical
  induction n with
  | zero => exact ‹Finite M›
  | succ n ih =>
    let := ih
    let := Fintype.ofFinite (syzygy M n)
    let := Fintype.ofFinite R
    change Finite (LinearMap.ker (cover (syzygy M n)).hom)
    infer_instance

private noncomputable def differential (M : ModuleCat.{v} R) (n : ℕ) :
    freeModule (syzygy M (n + 1)) ⟶ freeModule (syzygy M n) :=
  cover (syzygy M (n + 1)) ≫
    ModuleCat.ofHom (LinearMap.ker (cover (syzygy M n)).hom).subtype

private theorem differential_cover (M : ModuleCat.{v} R) (n : ℕ) :
    differential M n ≫ cover (syzygy M n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (cover (syzygy M (n + 1)) x).property

private theorem differential_sq (M : ModuleCat.{v} R) (n : ℕ) :
    differential M (n + 1) ≫ differential M n = 0 := by
  change differential M (n + 1) ≫
    (cover (syzygy M (n + 1)) ≫
      ModuleCat.ofHom (LinearMap.ker (cover (syzygy M n)).hom).subtype) = 0
  rw [← Category.assoc, differential_cover, zero_comp]

private noncomputable def resolutionComplex (M : ModuleCat.{v} R) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n ↦ freeModule (syzygy M n)) (differential M) (differential_sq M)

private theorem differential_exact (M : ModuleCat.{v} R) (n : ℕ) :
    (ShortComplex.mk (differential M (n + 1)) (differential M n)
      (differential_sq M n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : cover (syzygy M (n + 1)) x = 0 := by
    apply Subtype.ext
    exact hx
  obtain ⟨y, hy⟩ := cover_surjective (syzygy M (n + 2)) ⟨x, hx'⟩
  exact ⟨y, congrArg Subtype.val hy⟩

private theorem augmentation_exact (M : ModuleCat.{v} R) :
    (ShortComplex.mk (differential M 0) (cover M) (differential_cover M 0)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := cover_surjective (syzygy M 1) ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- The explicit free resolution obtained by repeatedly covering the kernel. -/
private noncomputable def resolution (M : ModuleCat.{v} R) : ProjectiveResolution M where
  complex := resolutionComplex M
  projective n := ModuleCat.projective_of_free (Finsupp.basisSingleOne)
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨cover M, by
    change differential M 0 ≫ cover M = 0
    exact differential_cover M 0⟩
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨augmentation_exact M, (ModuleCat.epi_iff_surjective _).2 (cover_surjective M)⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by change differential M 0 = differential M 0; rfl) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
        simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
          resolutionComplex, ChainComplex.of.d] using differential_exact M n
      · apply ChainComplex.exactAt_succ_single_obj⟩

section Devissage

variable {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : _root_.DerivedCategory (ModuleCat.{v} R) ⥤ D}
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

omit [NatTrans.CommShift τ ℤ] in
private theorem isIso_free (M : ModuleCat.{v} R) [Finite M]
    (h : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of R R)))) :
    IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj (freeModule M))) := by
  classical
  let Z : M → ModuleCat.{v} R := fun _ ↦ ModuleCat.of R R
  have hsum : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.coproductCocone Z).pt)) :=
    NatTrans.isIso_app_of_isColimit_cofan τ
      (_root_.DerivedCategory.isColimitCofanMkQObj
        (isColimitCofanMkObjOfIsColimit (HomologicalComplex.single _ (.up ℤ) 0) _ _
          (ModuleCat.coproductCoconeIsColimit Z))) (fun _ ↦ h)
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (finsuppLEquivDirectSum R R M).toModuleIso)).2 hsum

private theorem isIso_telescope
    [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]
    {L : CochainComplex (ModuleCat.{v} R) ℤ} (N : ℕ → L.SubcomplexFamily)
    (hN : ∀ n, N n ≤ N (n + 1)) (hL : ∀ i (x : L.X i), ∃ n, x ∈ (N n).N i)
    (h : ∀ n, IsIso (τ.app (_root_.DerivedCategory.Q.obj
      (CochainComplex.subcomplex (N n))))) :
    IsIso (τ.app (_root_.DerivedCategory.Q.obj L)) := by
  have hsum : IsIso (τ.app (_root_.DerivedCategory.Q.obj
      (∐ fun n ↦ CochainComplex.subcomplex (N n)))) :=
    NatTrans.isIso_app_of_isColimit_cofan τ
      (_root_.DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct _)) h
  exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ
    (_root_.DerivedCategory.triangleOfSES_distinguished
      (CochainComplex.telescopeShortComplex_shortExact N hN hL)) hsum hsum

private theorem isIso_finite [Finite R]
    [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]
    (h : IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of R R)))) (M : ModuleCat.{v} R) [Finite M] :
    IsIso (τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj M)) := by
  let P := resolution M
  have hterm (i : ℤ) : IsIso (τ.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (P.cochainComplex.X i))) := by
    by_cases hi : i ≤ 0
    · let k := (-i).toNat
      have e := P.cochainComplexXIso i k (by dsimp [k]; omega)
      apply (NatTrans.isIso_app_iff_of_iso τ
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e)).2
      have : Finite (syzygy M k) := finite_syzygy M k
      exact isIso_free τ (syzygy M k) h
    · have hz : IsZero ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (P.cochainComplex.X i)) :=
        (_root_.DerivedCategory.singleFunctor _ 0).map_isZero
          (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 i (by omega))
      exact ⟨⟨0, (F.map_isZero hz).eq_of_src _ _, (G.map_isZero hz).eq_of_src _ _⟩⟩
  have hP : IsIso (τ.app (_root_.DerivedCategory.Q.obj P.cochainComplex)) :=
    isIso_telescope τ (fun m ↦ CochainComplex.stupidTruncGEFamily P.cochainComplex (-m))
      (fun m ↦ CochainComplex.stupidTruncGEFamily_le_of_le (by omega))
      (fun i x ↦ ⟨(-i).toNat,
        (CochainComplex.mem_stupidTruncGEFamily_iff x).2 (Or.inl (by omega))⟩)
      (fun m ↦ _root_.DerivedCategory.isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE
        τ _ (-m) 0 (fun i ↦ by
          by_cases hi : - (m : ℤ) ≤ i
          · have := CochainComplex.isIso_subcomplexι_stupidTruncGEFamily_f
              (L := P.cochainComplex) (Or.inl hi)
            exact (NatTrans.isIso_app_iff_of_iso τ
              ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
                (asIso ((CochainComplex.subcomplexι
                  (CochainComplex.stupidTruncGEFamily P.cochainComplex (-m))).f i)))).2
              (hterm i)
          · have hz := CochainComplex.isZero_of_isStrictlyGE
              (CochainComplex.subcomplex
                (CochainComplex.stupidTruncGEFamily P.cochainComplex (-m))) (-m) i (by omega)
            have hz' := (_root_.DerivedCategory.singleFunctor _ 0).map_isZero hz
            exact ⟨⟨0, (F.map_isZero hz').eq_of_src _ _, (G.map_isZero hz').eq_of_src _ _⟩⟩))
  exact (NatTrans.isIso_app_iff_of_iso τ
    (asIso (_root_.DerivedCategory.Q.map P.π'))).1 hP

end Devissage

end ExceptionalConstantTensor

namespace AlgebraicGeometry.Etale

/-- If the unbounded derived direct image of an open immersion preserves countable
coproducts, its canonical projection-formula map is invertible at every finite constant
module over a finite commutative coefficient ring. Here the second argument is `N_T[0]`;
the canonical constant inverse-image isomorphism identifies its derived inverse image
with `N_U[0]`, so this is precisely `(Rj_*K) tensor^L N_T → Rj_*(K tensor^L N_U)`.

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-exc-constant-tensor.md
(blueprint: lem-exc-constant-tensor).

Proof:
1. Construct a free resolution of N by repeatedly taking the free module on the elements
   of the preceding kernel. Each kernel is finite because A and the preceding module are
   finite. Surjectivity of the covers proves exactness and the augmentation quasi-isomorphism.
2. Precompose the canonical projection map with the exact derived constant-sheaf functor.
   Its value on A[0] is invertible by the existing projection-map unit theorem and the
   monoidal constant-sheaf unit isomorphism. The existing projection-map shift theorem
   supplies compatibility with shifts, and the functors are triangulated.
3. Naturality on a finite coproduct identifies the component on each finite free module
   with the finite coproduct of the component on A[0]. Thus it is invertible on every
   resolution term placed in degree zero.
4. Apply the existing bounded-complex induction from ModuleCatGeneration to each brutal
   truncation of the resolution. This induction uses the short exact sequence adjoining
   one term and two out of three for the resulting distinguished triangles.
5. The brutal truncations increase to the resolution. Their module-complex telescope is
   short exact. Its derived distinguished triangle has two copies of the countable sum
   of the truncations followed by the resolution.
6. The derived constant-sheaf functor, inverse image, and tensor functors preserve countable
   coproducts by their adjunctions. Derived direct image does so by hypothesis. Naturality
   identifies the projection-map component on the sum with a sum of isomorphisms. Shift
   compatibility and two out of three in the telescope triangle give invertibility on
   the resolution, and the augmentation transfers this to N[0].
7. The natural comparison between the derived exact constant-sheaf functor and the
   degree-zero single functor transfers the result to the stated constant sheaf N_T[0].
   No bound on K or on the length of the free resolution is used. -/
theorem isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    [PreservesColimitsOfShape (Discrete ℕ)
      (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]
    (K : DerivedCategoryModule A U) (N : ModuleCat.{u + 1} A) [Finite N] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N))) := by
  let c := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory
  let τ : (derivedTensor (ModuleCat.{u + 1} A) T).obj
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K) ⟶
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} A) U).obj K) ⋙
        (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor :=
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K
  let α := Functor.whiskerLeft c τ
  have hunit : IsIso (α.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A))) := by
    have h : IsIso (τ.app (𝟙_ _)) :=
      isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit _ j K
    change IsIso (τ.app (c.obj _))
    refine (NatTrans.isIso_app_iff_of_iso τ ?_).2 h
    exact (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso
        (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).symm ≪≫
      _root_.DerivedCategory.singleFunctorObjUnitIso _
  have hshift : NatTrans.CommShift α ℤ := inferInstance
  have hc : PreservesColimitsOfShape (Discrete ℕ) c := by
    let adj := (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).derivedAdjunction
    have : PreservesColimitsOfShape (Discrete ℕ)
        (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesColimitsOfShape_of_natIso
      (Functor.leftDerivedFunctorIsoMapDerivedCategory
        (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
  have hG : PreservesColimitsOfShape (Discrete ℕ)
      (((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} A) U).obj K) ⋙
        (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor) := by
    have : PreservesColimitsOfShape (Discrete ℕ)
        (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor :=
      (derivedUpperStarLowerStarAdjunction _ j).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimitsOfShape (Discrete ℕ)
        ((derivedTensor (ModuleCat.{u + 1} A) U).obj K) :=
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    infer_instance
  have hF : PreservesColimitsOfShape (Discrete ℕ)
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj K)) :=
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) _).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have hN := ExceptionalConstantTensor.isIso_finite α hunit N
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((Functor.mapDerivedCategorySingleFunctor _ 0).app N)).1 hN

end AlgebraicGeometry.Etale
