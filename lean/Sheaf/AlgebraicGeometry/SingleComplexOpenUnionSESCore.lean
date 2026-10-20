module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

import WeilConjectures.AlgebraicGeometry.OpenUnionImageComplexExact
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonIso
import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private noncomputable def open_adj
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι := by
  let a : schemeOpenRestriction X U ⊣
      RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom := schemeOpenModuleAdjunction X U
  exact a.mapDerivedCategoryRightDerivedAdjunction

private theorem iso_pullback_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : Scheme.{u}} (s : A ≅ B) :
    IsIso (relativeMVAdj s.hom).unit := by
  obtain ⟨_, i, _, _, _⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  let b : derivedPullback s.hom ⋙ derivedPullback s.inv ≅ 𝟭 _ :=
    relativeMVComp s.inv s.hom ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.inv_hom_id) ≪≫ i B
  let c : derivedPullback s.inv ⋙ derivedPullback s.hom ≅ 𝟭 _ :=
    relativeMVComp s.hom s.inv ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.hom_inv_id) ≪≫ i A
  have : (derivedPullback s.inv).Faithful := Functor.Faithful.of_comp_iso c
  have : (derivedPullback s.hom).Faithful := Functor.Faithful.of_comp_iso b
  have : (derivedPullback s.hom).Full := Functor.Full.of_comp_faithful_iso b
  infer_instance

private noncomputable def open_iso_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B X : Scheme.{u}} (s : B ≅ A)
    (j : A ⟶ X) (p : B ⟶ X) (h : s.hom ≫ j = p)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage j).obj ((derivedPullback j).obj K) ≅
      (schemeDerivedDirectImage p).obj ((derivedPullback p).obj K) := by
  let c := relativeMVComp s.hom j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  have : IsIso (relativeMVAdj s.hom).unit := iso_pullback_unit s
  exact (schemeDerivedDirectImage j).mapIso
      (asIso ((relativeMVAdj s.hom).unit.app ((derivedPullback j).obj K))) ≪≫
    (schemeDerivedDirectImage s.hom ⋙ schemeDerivedDirectImage j).mapIso (c.app K) ≪≫
    ((((relativeMVAdj j).comp (relativeMVAdj s.hom)).ofNatIsoLeft c).rightAdjointUniq
      (relativeMVAdj p)).app ((derivedPullback p).obj K)


private theorem open_union_cone_models
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (U V : X.Opens) (K : schemeDerivedCategory X)
    (F : schemeDerivedCategory X ⥤ schemeDerivedCategory S)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Additive] :
    let H := fun W : X.Opens ↦ F.obj ((schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K))
    ∃ (A B : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (t : A ⟶ B),
      Nonempty (DerivedCategory.Q.obj A ≅ H (U ⊔ V)) ∧
      Nonempty (DerivedCategory.Q.obj B ≅ H U ⊞ H V) ∧
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ H (U ⊓ V)) := by
  classical
  dsimp only
  let M := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} M).obj
    (DerivedCategory.Q.objPreimage K)
  have : I.IsKInjective := inferInstance
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} M).app
      (DerivedCategory.Q.objPreimage K)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} M _).2
  let e : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{u} M).app
      (DerivedCategory.Q.objPreimage K)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let J := fun W : X.Opens ↦ schemeOpenModuleImageComplex X W I
  let eJ (W : X.Opens) :=
    schemeOpenModuleImageComplexComparison X W I (open_adj X W) ≪≫
      ((schemeOpenRestriction X W).mapDerivedCategory ⋙
        schemeDerivedDirectImage W.ι).mapIso e
  obtain ⟨hz, hS⟩ := schemeOpenUnionImageComplex_shortExact X U V I
    (fun _ ↦ inferInstance)
  let T := F.mapTriangle.obj (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (schemeDerivedCategory S) :=
    F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  obtain ⟨A, B, t, ⟨i⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  have : PreservesBinaryBiproducts (DerivedCategory.Q ⋙ F) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  refine ⟨A, B, t, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact Pretriangulated.Triangle.π₁.mapIso i.symm ≪≫ F.mapIso (eJ (U ⊔ V))
  · exact Pretriangulated.Triangle.π₂.mapIso i.symm ≪≫
      (DerivedCategory.Q ⋙ F).mapBiprod (J U) (J V) ≪≫
      biprod.mapIso (F.mapIso (eJ U)) (F.mapIso (eJ V))
  · exact Pretriangulated.Triangle.π₃.mapIso i.symm ≪≫ F.mapIso (eJ (U ⊓ V))

-- The compactness and quasi-coherence assumptions and the existential names are kept
-- exactly as in the interface; this object-only construction does not need them.
set_option linter.unusedVariables false in
/-- Chain-level model data for the union comparison arrows.

Source: Stacks Project, Cohomology, Tags 08HZ and 08HY; perfect.tex, Tag 0DJ9.
The K-injective restriction construction and its functorial coefficient map produce
strict chain maps and the displayed derived-category comparison isomorphisms.
(blueprint: new-single-complex-open-union-ses-core).
-/
theorem singleComplexOpenComparison_union_ses_core
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ (a (U ⊔ V)).left)
      (e₂ : DerivedCategory.Q.obj B ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ (a (U ⊔ V)).right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (a (U ⊓ V)).right), True := by
  classical
  dsimp only
  let : (derivedPullback g).CommShift ℤ := (relativeMVAdj g).leftAdjointCommShift ℤ
  have : (relativeMVAdj g).CommShift ℤ := (relativeMVAdj g).commShift_of_rightAdjoint ℤ
  have : (derivedPullback g).IsTriangulated := (relativeMVAdj g).isTriangulated_leftAdjoint
  have : (derivedPullback g).IsLeftAdjoint := (relativeMVAdj g).isLeftAdjoint
  have : (derivedPullback g).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (derivedPullback g)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (schemeDerivedDirectImage f).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (schemeDerivedDirectImage f').Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨A, B, t, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    open_union_cone_models U V K (schemeDerivedDirectImage f ⋙ derivedPullback g)
  obtain ⟨A', B', t', ⟨e₁'⟩, ⟨e₂'⟩, ⟨e₃'⟩⟩ :=
    open_union_cone_models (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) K' (schemeDerivedDirectImage f')
  let eL (W : X.Opens) := (derivedPullback g).mapIso
    ((schemeDerivedDirectImage f).mapIso ((schemeDerivedDirectImage W.ι).mapIso
      (((open_adj X W).leftAdjointUniq (relativeMVAdj W.ι)).app K)) ≪≫
      (relativeMVImageComp W.ι f).app ((derivedPullback W.ι).obj K))
  let eR (W : X.Opens) := (schemeDerivedDirectImage f').mapIso
    ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).mapIso
      (((open_adj X' (g' ⁻¹ᵁ W)).leftAdjointUniq
        (relativeMVAdj (g' ⁻¹ᵁ W).ι)).app K') ≪≫
      open_iso_transport (pullbackRestrictIsoRestrict g' W) (g' ⁻¹ᵁ W).ι
        (pullback.fst g' W.ι) (pullbackRestrictIsoRestrict_hom_ι g' W) K') ≪≫
    (relativeMVImageComp (pullback.fst g' W.ι) f').app
      ((derivedPullback (pullback.fst g' W.ι)).obj K')
  refine ⟨A, B, A', B', t, t', 0, 0, by simp, e₁ ≪≫ eL (U ⊔ V),
    e₂ ≪≫ biprod.mapIso (eL U) (eL V), e₃ ≪≫ eL (U ⊓ V),
    ?_, e₂' ≪≫ biprod.mapIso (eR U) (eR V), ?_, trivial⟩
  · exact e₁' ≪≫ eqToIso (by rw [Scheme.Hom.preimage_sup]) ≪≫ eR (U ⊔ V)
  · exact e₃' ≪≫ eqToIso (by rw [Scheme.Hom.preimage_inf]) ≪≫ eR (U ⊓ V)

end AlgebraicGeometry
