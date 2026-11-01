/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.AugmentedCechLocalOrthogonality
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.AugmentedCechCoverConeLocalization
import WeilConjectures.CategoryTheory.AugmentedCechCoverLocalComparison

/-! # Recognition of augmented extended Cech complexes on a cover

Source: Stacks Project, algebraization.tex, Tag 099E, and dualizing.tex, Tag 0A6R;
the cover-recognition criterion is the agent-formulated consequence recorded in the DAG.
(blueprint: lem-weil-pbc-augmented-cech-cover-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Pretriangulated

private theorem augmentation_postcomp_bijective
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (X : D)
    (h₀ : Subsingleton (X ⟶ T.obj₃))
    (h₁ : Subsingleton (X ⟶ T.obj₃⟦(-1 : ℤ)⟧)) :
    Function.Bijective (fun f : X ⟶ T.obj₁ ↦ f ≫ T.mor₁) := by
  constructor
  · intro f g hfg
    obtain ⟨q, hq⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang T hT)
      (f - g) (by
        change (f - g) ≫ T.mor₁ = 0
        simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)
    have hq₀ : q = 0 := h₁.elim _ _
    rw [hq₀, zero_comp] at hq
    exact sub_eq_zero.mp hq
  · intro f
    obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f (h₀.elim _ _)
    exact ⟨g, hg.symm⟩

private theorem sheaf_isIso_of_covering_components
    {D : Type u} [SmallCategory D] {L : GrothendieckTopology D}
    {F G : Sheaf L AddCommGrpCat.{u}} (f : F ⟶ G)
    (h : ∀ V : D, ∃ S : Sieve V, S ∈ L V ∧
      ∀ (W : D) (a : W ⟶ V), S a → IsIso (f.hom.app (op W))) : IsIso f := by
  apply (Sheaf.isLocallyBijective_iff_isIso f).1
  constructor
  · constructor
    intro V x y hxy
    obtain ⟨S, hS, hi⟩ := h V.unop
    apply L.superset_covering _ hS
    intro W a ha
    have := hi W a ha
    apply (ConcreteCategory.bijective_of_isIso (f.hom.app (op W))).1
    simpa only [Presheaf.equalizerSieve_apply, NatTrans.naturality_apply] using
      congrArg (G.obj.map a.op) hxy
  · constructor
    intro V x
    obtain ⟨S, hS, hi⟩ := h V
    apply L.superset_covering _ hS
    intro W a ha
    have := hi W a ha
    exact (ConcreteCategory.bijective_of_isIso (f.hom.app (op W))).2 (G.obj.map a.op x)

set_option maxHeartbeats 2000000 in
-- Allow room for the functor identifications in the identity pushforward comparison.
private noncomputable def overMap_id_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) : SheafOfModules.overMap.{u} R (𝟙 U) ≅ 𝟭 _ :=
  by
  unfold SheafOfModules.overMap
  let e :=
    SheafOfModules.pushforwardCongr₂.{u, u, u, u, u, u}
      (J := J.over U) (K := J.over U) (T := R.over U) (S := R.over U)
      (F := Over.map (𝟙 U)) (G := 𝟭 (Over U))
      (ψ := (Sheaf.pushforwardOverMapIso R (𝟙 U)).inv)
      (𝟙 (R.over U)) (Over.mapId U) (by
        ext X x
        change R.obj.map (𝟙 _) x = x
        simp)
  let eId : SheafOfModules.pushforward.{u} (F := 𝟭 (Over U)) (𝟙 (R.over U)) ≅
      𝟭 (SheafOfModules.{u} (R.over U)) := SheafOfModules.pushforwardId (R.over U)
  exact e.symm ≪≫ eId

private noncomputable def derivedOverMap_id_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C)
    [hU : HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))] :
    ringedKoszulDerivedOverMap O (𝟙 U) ≅ 𝟭 _ := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let : HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U)) := hU
  exact Functor.mapDerivedCategoryNatIso (overMap_id_iso R U) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem derivedOverMap_isIso_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (U : C) {X Y : ringedSiteDerived (O.over U)} (f : X ⟶ Y)
    (h : ∀ (V : C) (a : V ⟶ U), ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (b : W ⟶ V), S b →
        IsIso ((ringedKoszulDerivedOverMap O (b ≫ a)).map f)) : IsIso f := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let (V : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
  apply (DerivedCategory.isIso_iff _ f).2
  intro n
  let g := (DerivedCategory.homologyFunctor _ n).map f
  have hcomponent (V : C) (a : V ⟶ U)
      (hf : IsIso ((ringedKoszulDerivedOverMap O a).map f)) :
      IsIso (((SheafOfModules.toSheaf (R.over U)).map g).hom.app (op (Over.mk a))) := by
    let F := SheafOfModules.overMap.{u} R a
    change IsIso (F.mapDerivedCategory.map f) at hf
    have : IsIso (F.map g) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
          (F.mapDerivedCategory.map f))))
    have h' : IsIso (((SheafOfModules.toSheaf (R.over V)).map (F.map g)).hom.app
        (op (Over.mk (𝟙 V)))) := inferInstance
    change IsIso (((SheafOfModules.toSheaf (R.over U)).map g).hom.app
      (op (Over.mk (𝟙 V ≫ a)))) at h'
    exact (NatTrans.isIso_app_iff_of_iso
      (((SheafOfModules.toSheaf (R.over U)).map g).hom)
      (eqToIso (congrArg (fun t : V ⟶ U ↦ Over.mk t) (Category.id_comp a))).op).2 h'
  have : IsIso ((SheafOfModules.toSheaf (R.over U)).map g) := by
    apply sheaf_isIso_of_covering_components
    intro V
    obtain ⟨S, hS, hi⟩ := h V.left V.hom
    refine ⟨(Sieve.overEquiv V).symm S, J.overEquiv_symm_mem_over V S hS, ?_⟩
    intro W a ha
    have hf := hi W.left a.left ha
    rw [Over.w a] at hf
    exact hcomponent W.left W.hom hf
  exact isIso_of_reflects_iso g (SheafOfModules.toSheaf (R.over U))

/-- An augmented complex which has specified extended localization models on a cover has
such a model for every generating list on every slice. No compatibility of the supplied
isomorphisms is assumed.

Source: Stacks Project, algebraization.tex, Tag 099E (augmented local models), and
 dualizing.tex, Tag 0A6R (localization orthogonality and the augmentation lift).
(blueprint: lem-weil-pbc-augmented-cech-cover-criterion).

Proof:
1. Keep the supplied covering objects, lists and augmented isomorphisms. Complete
   `Q K → O[0]` to the distinguished mapping-cone triangle with third vertex `E`, and
   restrict it exactly to the slice of a fixed object `V` with generating list `g`.
2. By lem-weil-pbc-augmented-cech-cover-local-comparison, below every arrow `W → V`
   there is a covering sieve on whose members `T` an isomorphism
   `c_T : Q C_g|_T ≅ Q K|_T` commutes with the actual augmentations after the inverse
   ring comparison. No compatibility of the `c_T` is used.
3. By lem-weil-pbc-augmented-cech-cover-cone-localization, `E|_V` lies locally, on every
   slice, in the finite triangulated localization class `P_T`.
4. Apply lem-weil-pbc-augmented-cech-local-orthogonality: for every further slice `T`
   and integer `n`, `Hom(Q C_g|_T, E|_T[n]) = 0`; on `V` itself use the identity
   slice comparison. In particular the groups with targets `E` and `E[-1]` vanish.
5. Hom exactness for the triangle and its inverse rotation make postcomposition with
   `Q K|_V → O_V[0]` bijective on maps from `Q C_g`: this gives the unique lift `φ` of
   the actual augmentation.
6. On each member `T` of the covering sieves of step 2 the same bijectivity, for the
   restricted triangle, gives `φ|_T = c_T`, an isomorphism. Exact restriction commutes
   with homology (def-sfb-exact-derived-cohomology-comparison), so every homology sheaf
   of `φ` has bijective components on a covering sieve below every object; a locally
   bijective sheaf morphism is invertible, the forgetful functor reflects it, and the
   derived homology criterion gives `IsIso φ`. Cancel the inverse ring comparison in its
   augmentation equation. Arbitrary `V,g` give the conclusion. -/
theorem hasLocalExtendedCechDescription_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (A : Type u) (U : A → C)
    (hcover : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (f : W ⟶ V), S f → ∃ a : A, Nonempty (W ⟶ U a))
    (r : A → ℕ) (b : ∀ a : A, Fin (r a) → O.obj.obj (op (U a)))
    (hgen : ∀ a : A, IsRingedIdealGeneratingList O I ι (U a) (r a) (b a))
    (e : ∀ a : A, DerivedCategory.Q.obj
        (ringedExtendedCech (O.over (U a)) (r a)
          (fun i ↦ ringedSliceSection O (U a) (b a i))).1 ≅
        (ringedDerivedRestriction O (U a)).obj (DerivedCategory.Q.obj K))
    (he : ∀ a : A,
      (e a).hom ≫ (ringedDerivedRestriction O (U a)).map (DerivedCategory.Q.map ε) ≫
          (ringedDerivedRingRestrictionIso O (U a)).hom =
        DerivedCategory.Q.map
          (ringedExtendedCech (O.over (U a)) (r a)
            (fun i ↦ ringedSliceSection O (U a) (b a i))).2) :
    HasLocalExtendedCechDescription O I ι K ε := by
  intro V q g hg
  let X := DerivedCategory.Q.obj
    (ringedExtendedCech (O.over V) q (fun i ↦ ringedSliceSection O V (g i))).1
  let F := ringedDerivedRestriction O V
  let : F.CommShift ℤ := by dsimp [F, ringedDerivedRestriction]; infer_instance
  let : F.IsTriangulated := by dsimp [F, ringedDerivedRestriction]; infer_instance
  let E := F.obj (DerivedCategory.Q.obj (CochainComplex.mappingCone ε))
  let T := F.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle ε))
  have hT : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished ε)
  have hlocal := augmented_cech_cover_cone_localization O I ι K ε A U hcover r b
    hgen e he V
  have horth := ringed_augmented_cech_local_orthogonality O I ι V q g hg E hlocal
  have hvan (n : ℤ) : Subsingleton (X ⟶ E⟦n⟧) := by
    have := horth V (𝟙 V) n
    let ei := derivedOverMap_id_iso O V
    exact (Iso.homCongr (ei.app X) ((shiftFunctor _ n).mapIso (ei.app E))).symm.subsingleton
  have hz : Subsingleton (X ⟶ E) := by
    have := hvan 0
    exact (Iso.homCongr (Iso.refl X) ((shiftFunctorZero _ ℤ).app E)).symm.subsingleton
  let c := DerivedCategory.Q.map
    (ringedExtendedCech (O.over V) q (fun i ↦ ringedSliceSection O V (g i))).2 ≫
      (ringedDerivedRingRestrictionIso O V).inv
  obtain ⟨φ, hφ⟩ := (augmentation_postcomp_bijective T hT X hz (hvan (-1))).2 c
  have hφ' : φ ≫ F.map (DerivedCategory.Q.map ε) = c := hφ
  have hiso : IsIso φ := by
    apply derivedOverMap_isIso_of_cover O V
    intro W a
    obtain ⟨S, hS, hi⟩ := augmented_cech_cover_local_comparison O I ι K ε A U hcover
      r b hgen e he V q g hg W a
    refine ⟨S, hS, ?_⟩
    intro Z d hd
    obtain ⟨eZ, heZ⟩ := hi Z d hd
    let G := ringedKoszulDerivedOverMap O (d ≫ a)
    let : G.CommShift ℤ := by dsimp [G, ringedKoszulDerivedOverMap]; infer_instance
    let : G.IsTriangulated := by dsimp [G, ringedKoszulDerivedOverMap]; infer_instance
    have hG : G.mapTriangle.obj T ∈ distTriang _ := G.map_distinguished T hT
    have h₀ : Subsingleton (G.obj X ⟶ G.obj E) := by
      have := horth Z (d ≫ a) 0
      exact (Iso.homCongr (Iso.refl _) ((shiftFunctorZero _ ℤ).app _)).symm.subsingleton
    have h₁ : Subsingleton (G.obj X ⟶ (G.obj E)⟦(-1 : ℤ)⟧) :=
      horth Z (d ≫ a) (-1)
    have hm : G.map φ = eZ.hom := by
      apply (augmentation_postcomp_bijective (G.mapTriangle.obj T) hG (G.obj X) h₀ h₁).1
      change G.map φ ≫ G.map (F.map (DerivedCategory.Q.map ε)) =
        eZ.hom ≫ G.map (F.map (DerivedCategory.Q.map ε))
      rw [← G.map_comp, hφ', heZ]
    rw [hm]
    infer_instance
  refine ⟨asIso φ, ?_⟩
  change φ ≫ F.map (DerivedCategory.Q.map ε) ≫
    (ringedDerivedRingRestrictionIso O V).hom = _
  rw [← Category.assoc, hφ']
  simp only [c, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory
