/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import all Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
import Mathlib.CategoryTheory.Adjunction.Restrict
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Invertibility of the open-square mate

Source: Stacks Project, duality.tex, Lemma 48.12.2 (Tag 0E4J).
(blueprint: lem-sc-proper-flat-open-square-mate-isiso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Compare exact restriction and derived pullback via their left-derived universal properties.
private theorem open_pullback_restriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    Nonempty ((schemeOpenRestriction X U).mapDerivedCategory ≅ derivedPullback U.ι) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in by
  classical
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    T, hT, hTmap, hTadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec U.ι)
  have ht : T = Scheme.Modules.tensorPullback U.ι :=
    CategoryTheory.Functor.ext hT (fun _ _ φ ↦ hTmap φ)
  subst T
  let R := schemeOpenRestriction X U
  have : R.Additive := inferInstance
  have : (Scheme.Modules.tensorPullback U.ι).Additive := hTadd
  let θ : R ≅ Scheme.Modules.tensorPullback U.ι :=
    Scheme.Modules.overFunctorEquiv U ≪≫
      ((Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
        (Scheme.Modules.restrictAdjunction U.ι)).symm
  let θh : R.mapHomotopyCategory (.up ℤ) ≅
      (Scheme.Modules.tensorPullback U.ι).mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  let e := R.mapDerivedCategoryFactorsh ≪≫ Functor.isoWhiskerRight θh DerivedCategory.Qh
  let S := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : R.mapDerivedCategory.IsLeftDerivedFunctor e.hom S :=
    Functor.isLeftDerivedFunctor_of_inverts S _ e
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε S := hL
  have : R.mapDerivedCategory.IsRightKanExtension e.hom :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _ S
  have : (derivedPullback U.ι).IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _ S
  exact ⟨Functor.rightKanExtensionUnique R.mapDerivedCategory e.hom (derivedPullback U.ι) ε⟩

-- The pullback projection factors through the inverse-image open by a scheme isomorphism.
private theorem openSquare_pullback_isIso_of_restriction
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    {E F : schemeDerivedCategory X} (φ : E ⟶ F)
    (hφ : IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ W)).mapDerivedCategory.map φ)) :
    IsIso ((derivedPullback (pullback.fst f W.ι)).map φ) := by
  obtain ⟨eU⟩ := open_pullback_restriction_iso X (f ⁻¹ᵁ W)
  have : IsIso ((derivedPullback (f ⁻¹ᵁ W).ι).map φ) :=
    (NatIso.isIso_map_iff eU φ).mp hφ
  let r := pullbackRestrictIsoRestrict f W
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition
  let e : derivedPullback (f ⁻¹ᵁ W).ι ⋙ derivedPullback r.hom ≅
      derivedPullback (pullback.fst f W.ι) :=
    c r.hom (f ⁻¹ᵁ W).ι ≪≫ eqToIso (congrArg
      (fun k : pullback f W.ι ⟶ X ↦ derivedPullback.{u, w} k)
      (pullbackRestrictIsoRestrict_hom_ι f W))
  have : IsIso ((derivedPullback (f ⁻¹ᵁ W).ι ⋙ derivedPullback r.hom).map φ) := by
    change IsIso ((derivedPullback r.hom).map ((derivedPullback (f ⁻¹ᵁ W).ι).map φ))
    infer_instance
  exact (NatIso.isIso_map_iff e φ).mp inferInstance

-- Deriving a fully faithful open pushforward preserves full faithfulness.
private noncomputable def open_direct_image_fullyFaithful
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {Z T : Scheme.{u}} (j : Z ⟶ T) [IsOpenImmersion j] :
    (schemeDerivedDirectImage j).FullyFaithful := by
  let G := RingedSpace.moduleDirectImage j.toLRSHom.toShHom
  have : (Scheme.Modules.restrictFunctor j).Additive :=
    Functor.additive_of_preserves_binary_products _
  let adj := Scheme.Modules.restrictAdjunction j
  let : G.PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  let : G.Full := adj.fullyFaithfulROfIsIsoCounit.full
  let : G.Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
  exact Functor.FullyFaithful.ofFullyFaithful G.rightDerivedFunctor

/-- The canonical right-adjoint mate of a proper-flat morphism along an affine
open immersion is invertible, for any supplied right adjoints and adjunctions.
Source: Stacks Project, duality.tex, Tag 0E4J (part (2)), and Tag 0A9L,
equation-sheafy; the identification with the base-change mate is Tag 0E9S.
(blueprint: lem-sc-proper-flat-open-square-mate-isiso)

Proof: Put U = f inverse(W). Exact restriction to W and U is derived pullback.
The square with U and W is cartesian; its pullback object is canonically isomorphic
to U by the projection equations. Both opens are quasi-compact: W is affine and
f is proper. Derived open direct image preserves quasi-coherent cohomology.
Apply proper_flat_rightAdjoint_restriction_open to the canonical lift of Rf_*
for the supplied square with change of base W.ι. Its first clause
says that restriction to U of a applied to the open-unit K -> Rj_* j^* K is
invertible. The conjugate of ordinary open base change identifies a Rj_* with
Ri_* a', using the given adjunctions and the assumed ordinary base-change isomorphism.
Apply exact restriction to this identification. The open counit i^* Ri_* -> id
is invertible. Thus the unit, inverse conjugate, counit expression defining
this canonical mate is a composite of three invertible arrows. The projection
comparison transports this conclusion from U to the canonical pullback scheme.
Uniqueness of right adjoints transports it to the supplied a' and its adjunction.
This argument applies to all unbounded quasi-coherent objects and to the empty open;
it does not use global invertibility of proper-flat base change.
-/
theorem proper_flat_openSquare_mate_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (W : Y.Opens) [IsAffine W.toScheme]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory W.toScheme ⥤ schemeDerivedQCohCategory (pullback f W.ι))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f W.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f W.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f W.ι)) _ _ _ _
          (pullback.snd f W.ι) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f W.ι) W.ι (pullback.fst f W.ι)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    IsIso (@dualityEquationBaseChangeMap _ X Y W.toScheme
      (QuasiCompact.compactSpace_of_compactSpace f)
      (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
      f W.ι a a' adjf adjf' hβ K) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in by
  classical
  dsimp -zeta only [dualityEquationBaseChangeMap]
  extract_lets PX PY PY' PX' Lg LgX Rf Rf' β hβlift hβiso
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let Rg := PY.lift (PY'.ι ⋙ schemeDerivedDirectImage W.ι)
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint W.toScheme Y W.ι).fst E.obj E.property)
  let RgX := PX.lift (PX'.ι ⋙ schemeDerivedDirectImage (pullback.fst f W.ι))
    (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f W.ι)) _ _ _ _
      (pullback.fst f W.ι) _ _).fst E.obj E.property)
  let adjg : Lg ⊣ Rg := Adjunction.restrictFullyFaithful
    (Classical.choose (exists_schemeDerivedAdjunction W.ι
      (hAdd := (Classical.choose exists_derivedPullbackComposition) W.ι)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition))
        W.ι)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) W.ι)))
    PY.fullyFaithfulι PY'.fullyFaithfulι
    (PY'.liftCompιIso _ _).symm (PY.liftCompιIso _ _).symm
  let adjgX : LgX ⊣ RgX := Adjunction.restrictFullyFaithful
    (Classical.choose (exists_schemeDerivedAdjunction (pullback.fst f W.ι)
      (hAdd := (Classical.choose exists_derivedPullbackComposition) (pullback.fst f W.ι))
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition))
        (pullback.fst f W.ι))
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) (pullback.fst f W.ι))))
    PX.fullyFaithfulι PX'.fullyFaithfulι
    (PX'.liftCompιIso _ _).symm (PX.liftCompιIso _ _).symm
  change IsIso ((mateEquiv adjf adjf' (inv β)).app K)
  rw [← secondMate_formula adjf adjf' adjgX adjg β K]
  -- Recover the ambient adjunction used by the canonical restricted unit.
  let adjJ := Classical.choose (exists_schemeDerivedAdjunction W.ι
    (hAdd := (Classical.choose exists_derivedPullbackComposition) W.ι)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) W.ι)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) W.ι))
  obtain ⟨eW⟩ := open_pullback_restriction_iso Y W
  let adjW : (schemeOpenRestriction Y W).mapDerivedCategory ⊣
      schemeDerivedDirectImage W.ι := adjJ.ofNatIsoLeft eW.symm
  let hopen (E : schemeDerivedQCohCategory Y) : PY
      ((schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction Y W).mapDerivedCategory.obj E.obj)) := by
    have hp := (schemeDerivedDirectImage_qcqs_hasRightAdjoint W.toScheme Y W.ι).fst
      ((derivedPullback W.ι).obj E.obj)
      ((derivedPullback_tensor_preserve_QCoh W.ι).1 E.obj E.property)
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((schemeDerivedDirectImage W.ι).mapIso (eW.app E.obj).symm)) (hp n)
  let η : K ⟶ ⟨(schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj), hopen K⟩ :=
    ObjectProperty.homMk (adjW.unit.app K.obj)
  let γ : ⟨(schemeDerivedDirectImage W.ι).obj
      ((schemeOpenRestriction Y W).mapDerivedCategory.obj K.obj), hopen K⟩ ≅
      Rg.obj (Lg.obj K) :=
    ObjectProperty.isoMk PY ((schemeDerivedDirectImage W.ι).mapIso (eW.app K.obj))
  have hu : adjg.unit.app K = η ≫ γ.hom := by
    ext
    change PY.ι.map (adjg.unit.app K) =
      (adjJ.unit.app K.obj ≫ (schemeDerivedDirectImage W.ι).map (eW.inv.app K.obj)) ≫
        (schemeDerivedDirectImage W.ι).map (eW.hom.app K.obj)
    dsimp only [adjg]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    change adjJ.unit.app K.obj ≫ (schemeDerivedDirectImage W.ι).map (𝟙 _) ≫ 𝟙 _ =
      (adjJ.unit.app K.obj ≫ (schemeDerivedDirectImage W.ι).map (eW.inv.app K.obj)) ≫
        (schemeDerivedDirectImage W.ι).map (eW.hom.app K.obj)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Category.comp_id]
  -- Apply the existing geometric theorem to the exact restriction unit.
  have hres : IsIso ((schemeOpenRestriction X (f ⁻¹ᵁ W)).mapDerivedCategory.map
      (PX.ι.map (a.map η))) :=
    (proper_flat_rightAdjoint_restriction_open W.ι f Rf
      (PY.liftCompιIso _ _) a adjf Rf' (PY'.liftCompιIso _ _) a' adjf').1
      W (show IsAffineOpen W from ‹IsAffine W.toScheme›).isCompact adjW hopen K
  have hunit : IsIso (LgX.map (a.map (adjg.unit.app K))) := by
    have : IsIso (PX'.ι.map (LgX.map (a.map (adjg.unit.app K)))) := by
      change IsIso ((derivedPullback (pullback.fst f W.ι)).map
        (PX.ι.map (a.map (adjg.unit.app K))))
      apply openSquare_pullback_isIso_of_restriction f W
      rw [hu, Functor.map_comp, Functor.map_comp, Functor.map_comp]
      infer_instance
    exact PX'.fullyFaithfulι.isIso_of_isIso_map _
  -- The inverse conjugate is invertible by hβ; open pushforward has invertible counit.
  have hff := open_direct_image_fullyFaithful (pullback.fst f W.ι)
  let : (schemeDerivedDirectImage (pullback.fst f W.ι)).Full := hff.full
  let : (schemeDerivedDirectImage (pullback.fst f W.ι)).Faithful := hff.faithful
  have : RgX.Full := by dsimp [RgX]; infer_instance
  have : RgX.Faithful := by dsimp [RgX]; infer_instance
  have : IsIso adjgX.counit := adjgX.counit_isIso_of_R_fully_faithful
  infer_instance

end AlgebraicGeometry
