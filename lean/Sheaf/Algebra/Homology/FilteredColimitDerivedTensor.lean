/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Sheaf.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Filtered colimits and cohomology of derived tensor products

Source: Stacks Project, Tags 06Y6, 06YR and 00DB
(blueprint: lem-pc-filtered-colimit-derived-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

private theorem colimitPost_natTrans
    {C D : Type*} [Category C] [Category D]
    (I : Type*) [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    (F G : C ⥤ D) (η : F ⟶ G) (N : I ⥤ C) :
    colim.map (Functor.whiskerLeft N η) ≫ colimit.post N G =
      colimit.post N F ≫ η.app (colimit N) := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_map_assoc]
  simp only [whiskerLeft_app, colimit.ι_post, colimit.ι_post_assoc]
  exact (η.naturality (colimit.ι N j)).symm

namespace DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]

set_option backward.isDefEq.respectTransparency false in
private theorem shortComplexHomologyPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor (ModuleCat.{u} S)) := by
  classical
  refine ⟨fun {F} ↦ ?_⟩
  have : (colim (J := I) (C := ModuleCat.{u} S)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let K := (ShortComplex.functorEquivalence I (ModuleCat.{u} S)).inverse.obj F
  let e : K.homology ≅ F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S) :=
    NatIso.ofComponents
      (fun i ↦ (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj i)).symm)
      (by
        intro i j f
        have h := K.homologyMap_mapNatTrans ((evaluation I (ModuleCat.{u} S)).map f)
        change ShortComplex.homologyMap (F.map f) = _ at h
        change K.homology.map f ≫
          (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj j)).inv =
          (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj i)).inv ≫
            ShortComplex.homologyMap (F.map f)
        rw [h]
        simp)
  let a : colimit (F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S)) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
    (colim.mapIso e).symm ≪≫ (K.mapHomologyIso colim).symm
  refine preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F) ?_
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
  refine Cocone.ext a ?_
  intro i
  have h := K.homologyMap_mapNatTrans (colim.ι (C := ModuleCat.{u} S) i)
  change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
  change colimit.ι _ i ≫ a.hom =
    ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
  rw [h]
  simp [a, e]

private theorem complexHomologyPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I] [IsFiltered I] (n : ℤ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℤ) n) := by
  have := shortComplexHomologyPreserves S I
  have : PreservesColimitsOfShape I
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} S) (.up ℤ) n).symm

private theorem tensorComplexPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) :
    PreservesColimitsOfShape I (MonoidalCategory.tensorRight P) := by
  have (X : ModuleCat.{u} S) :
      PreservesColimitsOfShape I (MonoidalCategory.tensorRight X) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  exact inferInstanceAs (PreservesColimitsOfShape I
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} S)).map₂CochainComplex.flip.obj P))

set_option maxHeartbeats 400000 in
-- The mixed-tensor and restriction comparisons unfold several nested functor structures.
private theorem balancedModel (f : R →+* A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : E ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj M)
    (he : QuasiIso e) (hE : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E)
    (n : ℤ) :
    let T := Classical.choose (exists_derivedTensor_second_factor_functor f).2
    Nonempty ((Q ⋙ T.obj M ⋙ homologyFunctor (ModuleCat.{u} A) n) ⋙
      ModuleCat.restrictScalars f ≅
      MonoidalCategory.tensorRight E ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n) := by
  classical
  dsimp only
  let T := Classical.choose (exists_derivedTensor_second_factor_functor f).2
  obtain ⟨ε, _, _, hcompute, _⟩ :=
    Classical.choose_spec (exists_derivedTensor_second_factor_functor f).2
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
  let L := Λ.resolutionFunctor
  let s := Λ.resolutionNatTrans
  have hL (N : CochainComplex (ModuleCat.{u} R) ℤ) :
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat (L.obj N) :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le N
  let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
  let H := Q ⋙ T.obj M ⋙ homologyFunctor (ModuleCat.{u} A) n
  let HA := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n
  let HR := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n
  let S := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let t : L ⋙ (Q ⋙ T.obj M) ⟶ Q ⋙ T.obj M := Functor.whiskerRight s (Q ⋙ T.obj M)
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).2
    intro N
    have hs : QuasiIso (s.app N) := inferInstance
    have : IsIso (Q.map (s.app N)) := (isIso_Q_map_iff_quasiIso _ _).2 hs
    change IsIso ((T.obj M).map (Q.map (s.app N)))
    infer_instance
  have : IsIso (Functor.whiskerLeft L (ε M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro N
    exact hcompute M (L.obj N) (hL N)
  let a : H ≅ L ⋙ B.flip.obj M ⋙ HA :=
    isoWhiskerRight (asIso t).symm (homologyFunctor (ModuleCat.{u} A) n) ≪≫
      isoWhiskerRight (asIso (Functor.whiskerLeft L (ε M)))
        (homologyFunctor (ModuleCat.{u} A) n) ≪≫
      isoWhiskerLeft (L ⋙ B.flip.obj M) (homologyFunctorFactors (ModuleCat.{u} A) n)
  obtain ⟨r⟩ := CochainComplex.exists_mixedTensor_restriction_iso f
  let rM : B.flip.obj M ⋙ S ≅ MonoidalCategory.tensorRight (S.obj M) :=
    NatIso.ofComponents (fun N ↦ (r.app N).app M) (by
      intro N N' g
      exact congrArg (fun t ↦ t.app M) (r.hom.naturality g))
  let aR : H ⋙ ModuleCat.restrictScalars f ≅
      L ⋙ MonoidalCategory.tensorRight (S.obj M) ⋙ HR :=
    isoWhiskerRight a (ModuleCat.restrictScalars f) ≪≫
      isoWhiskerLeft (L ⋙ B.flip.obj M)
        ((ModuleCat.restrictScalars f).mapHomologicalComplexHomologyIso (.up ℤ) n).symm ≪≫
      isoWhiskerRight (isoWhiskerLeft L rM) HR
  let b : L ⋙ MonoidalCategory.tensorRight E ⋙ HR ⟶
      L ⋙ MonoidalCategory.tensorRight (S.obj M) ⋙ HR :=
    Functor.whiskerRight (Functor.whiskerLeft L
      ((MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).flip.map e)) HR
  have : IsIso b := by
    apply (NatTrans.isIso_iff_isIso_app b).2
    intro N
    have : QuasiIso (MonoidalCategory.whiskerLeft (L.obj N) e) := (hL N).whiskerLeft he
    change IsIso (HomologicalComplex.homologyMap (MonoidalCategory.whiskerLeft (L.obj N) e) n)
    infer_instance
  let c : L ⋙ MonoidalCategory.tensorRight E ⋙ HR ⟶
      MonoidalCategory.tensorRight E ⋙ HR :=
    Functor.whiskerRight s (MonoidalCategory.tensorRight E ⋙ HR)
  have : IsIso c := by
    apply (NatTrans.isIso_iff_isIso_app c).2
    intro N
    have hs : QuasiIso (s.app N) := inferInstance
    have : QuasiIso (MonoidalCategory.whiskerRight (s.app N) E) := hE.whiskerRight hs
    change IsIso (HomologicalComplex.homologyMap (MonoidalCategory.whiskerRight (s.app N) E) n)
    infer_instance
  exact ⟨aR ≪≫ (asIso b).symm ≪≫ asIso c⟩

/-- The canonical cohomology comparison for a filtered colimit is an `A`-module isomorphism,
natural in the fixed `A`-complex and in the diagram. Source: Stacks Project, Tags 06Y6,
06YR and 00DB (blueprint: lem-pc-filtered-colimit-derived-tensor).

`T` is the bifunctor supplied by `lem-pc-derived-tensor-second-factor-functor`, selected
from its existence theorem. `H M` is `Hⁿ(M ⊗ᴸ_R -)` on complexes of `R`-modules.
The comparison is `colimit.post`; its coprojection equation specifies the original maps,
and the last two equations give naturality in `M` and in the diagram, respectively.

Proof:
1. Use the source library's reduced functorial flat resolution `L` with augmentation `s`.
   For the restricted fixed complex choose `E = L(S(M))`, `e = s(S(M))`.
   The source proves `E` K-flat and `e` a quasi-isomorphism. The derived comparison `ε`
   is invertible on every `L(N)`, so the augmentation and `ε` identify derived
   cohomology with the cohomology of the mixed tensor `B(L(N), M)`, naturally in `N`.
2. Restriction preserves homology. The mixed-tensor restriction comparison identifies
   the latter model with `L(N) ⊗ S(M)`. The two maps of the balanced zigzag
   `L(N) ⊗ S(M) ← L(N) ⊗ E → N ⊗ E` are quasi-isomorphisms, by K-flatness of
   `L(N)` and `E`. Apply ordinary homology to get a natural isomorphism from the
   restriction of derived cohomology to `N ↦ Hⁿ(N ⊗ E)`.
3. Tensor totalization preserves colimits by the source library's generic bifunctor
   colimit instance and the tensor-Hom adjunction. Exact filtered colimits of modules
   preserve short-complex homology: compare the homology of the short complex in the
   diagram category with its evaluations and its colimit. Evaluation at the three
   adjacent degrees then shows that ordinary complex homology preserves filtered
   colimits, with no boundedness assumption. Thus `N ↦ Hⁿ(N ⊗ E)` preserves them.
4. Transport preservation across the natural isomorphism from step 2. Restriction of
   scalars preserves colimits and reflects isomorphisms, hence reflects colimits.
   This proves that the canonical `A`-linear comparison is invertible. The coprojection
   equation is `colimit.ι_post`. Naturality in `M` follows by colimit extensionality
   and naturality of the induced transformation; diagram naturality is
   `colimit.map_post`. -/
theorem filteredColimit_derivedTensor_cohomology (f : R →+* A)
    (I : Type u) [SmallCategory I] [IsFiltered I] (n : ℤ) :
    let QR := (Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤
      DerivedCategory (ModuleCat.{u} R))
    let T := Classical.choose (exists_derivedTensor_second_factor_functor f).2
    let H := fun M : CochainComplex (ModuleCat.{u} A) ℤ ↦
      QR ⋙ T.obj M ⋙ homologyFunctor (ModuleCat.{u} A) n
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ),
      IsIso (colimit.post N (H M))) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (j : I),
      colimit.ι (N ⋙ H M) j ≫ colimit.post N (H M) = (H M).map (colimit.ι N j)) ∧
    (∀ (M M' : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ M')
      (N : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ),
      let η := whiskerRight (whiskerLeft QR (T.map g))
        (homologyFunctor (ModuleCat.{u} A) n)
      colim.map (whiskerLeft N η) ≫ colimit.post N (H M') =
        colimit.post N (H M) ≫ η.app (colimit N)) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
      (N N' : I ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (a : N ⟶ N'),
      colim.map (whiskerRight a (H M)) ≫ colimit.post N' (H M) =
        colimit.post N (H M) ≫ (H M).map (colim.map a)) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N
    let S := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
    let Λ := (Classical.choice (inferInstance :
      Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
    let E := Λ.resolutionFunctor.obj (S.obj M)
    let e := Λ.resolutionNatTrans.app (S.obj M)
    have he : QuasiIso e := inferInstance
    have hE : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E :=
      Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le (S.obj M)
    obtain ⟨a⟩ := balancedModel f M E e he hE n
    have := complexHomologyPreserves R I n
    have := tensorComplexPreserves R I E
    have := preservesColimitsOfShape_of_natIso (J := I) a.symm
    have : ReflectsColimitsOfShape I (ModuleCat.restrictScalars f) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    have := preservesColimitsOfShape_of_reflects_of_preserves (J := I)
      (Q ⋙ (Classical.choose (exists_derivedTensor_second_factor_functor f).2).obj M ⋙
        homologyFunctor (ModuleCat.{u} A) n) (ModuleCat.restrictScalars f)
    infer_instance
  · intro M N j
    exact colimit.ι_post N _ j
  · intro M M' g N
    exact colimitPost_natTrans I _ _ _ N
  · intro M N N' a
    exact (colimit.map_post a _).symm

end DerivedCategory
