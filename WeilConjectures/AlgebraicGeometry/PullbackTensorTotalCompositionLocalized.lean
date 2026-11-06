/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.FiniteStructureTensorComparisonComposition

/-! # Ordinary tensor pullback composition after localization

Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-pullback-tensor-total-composition-localized).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

private abbrev tensorAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)

private abbrev tensorCompMate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateIsoEquiv (tensorAdj (f ≫ g)) ((tensorAdj g).comp (tensorAdj f))).symm
    (Scheme.Modules.pushforwardComp f g).symm

private theorem tensorCompMate_tensor {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (Scheme.Modules.tensorPullback f).map
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor f))
        ((Scheme.Modules.tensorPullback g).obj M)
        ((Scheme.Modules.tensorPullback g).obj N)).hom ≫
      ((tensorCompMate f g).hom.app M ⊗ₘ (tensorCompMate f g).hom.app N) =
    (tensorCompMate f g).hom.app (M ⊗ N) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g))) M N).hom  := by
  have hc : Scheme.Modules.pushforwardCongr (rfl : f ≫ g = f ≫ g) = Iso.refl _ := by
    ext A U s
    simp
  simpa only [Scheme.Modules.tensorPullbackCompositionIso, hc,
    conjugateIsoEquiv_symm_apply_inv, conjugateIsoEquiv_symm_apply_hom,
    Iso.symm_hom, tensorCompMate, tensorAdj,
    Iso.trans_inv, NatTrans.comp_app,
    eqToIso_refl, Iso.refl_inv, Category.id_comp] using
    Scheme.Modules.finiteStructure_tensorComparison_composition f g (f ≫ g) rfl M N


variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

set_option maxHeartbeats 600000 in
-- Comparing the scheme-module and sheaf-module tensor interfaces needs extra elaboration.
/-- Localization of the ordinary tensor/composition square.
Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-pullback-tensor-total-composition-localized).

Proof: the localization tensor map is natural in both complex inputs. Apply
this naturality to the ordinary composition mate on P and N. The two ordinary
chain maps from f*g*Tot(P,N) to Tot((fg)*P,(fg)*N) agree on each (p,q)
summand: transpose by the pinned adjunctions, and evaluate on pure tensor
sections. The composite adjunction unit inserts the same successive unit
images in both factors. Tensor universality proves the module equality, and
joint epimorphy of total-complex summand inclusions proves the chain equality.
More explicitly, write b_R for the chain composition mate and Tot(b_P,b_N)
for its induced map on total tensor complexes. The chain equality is
f*(psi.hom);theta.hom;Tot(b_P,b_N) = b_Tot;phi.hom. The mate identity
identifies the direct adjunction unit followed by b_R with the successive
adjunction unit, transported along pushforwardComp. Thus the transposed
summand maps both send s tensor t to the tensor of those successive unit
images. Pullbacks are left adjoints, so they preserve the coproducts of
summands; the mapped inclusions are jointly epimorphic as required above.
Naturality gives (Q(b_P) tensor Q(b_N));mu_direct =
mu_successive;Q(Tot(b_P,b_N)). Precompose the chain equality with
theta.inv followed by f*(psi.inv), then localize and substitute it here.
No K-flatness is required. Identity arrows, zero complexes and empty schemes
satisfy the same universal-property calculation.
-/
theorem pullback_tensor_total_composition_localized
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (ψ : ((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal Y
        (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hψ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor Y
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor (SheafOfModules.{u}
      (moduleRings Z.toRingedSpace))) (.up ℤ) p q n h) ≫
          ψ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
            (.up ℤ) p q n h)
    (θ : ((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Y (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up
      ℤ)).obj P) (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
        (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)))
    (hθ :
      letI := pullbackDescentModuleTensor Y
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f)).map
            (HomologicalComplex.ιMapBifunctor (((Scheme.Modules.tensorPullback
      g).mapHomologicalComplex (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback
      g).mapHomologicalComplex (.up ℤ)).obj N) (curriedTensor (SheafOfModules.{u} (moduleRings
      Y.toRingedSpace))) (.up ℤ) p q n h) ≫
          θ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f)))
          ((((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P).X p)
      ((((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N).X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
            (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N))
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    cast (by rfl)
      (((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj P))) ⊗ₘ
      ((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj N)))) ≫
      pullbackTensorModelMap X (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex
      (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up
      ℤ)).obj N) =
    pullbackTensorModelMap X (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up
      ℤ)).obj (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ≫
      DerivedCategory.Q.map θ.inv ≫
      DerivedCategory.Q.map
        (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).map ψ.inv) ≫
      cast (by rfl)
        ((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj
          (pullbackTensorTotal Z P N)))) ≫
      DerivedCategory.Q.map φ.hom := by
  let : MonoidalCategory Z.Modules := pullbackDescentModuleTensor Z
  let : MonoidalCategory Y.Modules := pullbackDescentModuleTensor Y
  let : MonoidalCategory X.Modules := pullbackDescentModuleTensor X
  let : (curriedTensor Z.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
  let : (curriedTensor Y.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
  let : (curriedTensor X.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : ∀ M : Z.Modules,
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf M
  let : ∀ M : Y.Modules,
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf M
  let : ∀ M : X.Modules,
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M
  let : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    pullbackDescentModuleTensor X
  let : (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : ∀ M : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M
  let : MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    pullbackDescentModuleTensor Y
  let : (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
  let : ∀ M : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf M
  let : MonoidalCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    pullbackDescentModuleTensor Z
  let : (curriedTensor (SheafOfModules.{u} (moduleRings Z.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
  let : ∀ M : SheafOfModules.{u} (moduleRings Z.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf M
  let : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let F := Scheme.Modules.tensorPullback f
  let G := Scheme.Modules.tensorPullback g
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let b := Functor.mapHomologicalComplexCompIso (tensorCompMate f g) (.up ℤ)
  have : F.IsLeftAdjoint := ⟨_, ⟨tensorAdj f⟩⟩
  have : G.IsLeftAdjoint := ⟨_, ⟨tensorAdj g⟩⟩
  have hchain : Fc.map ψ.hom ≫ θ.hom ≫
      HomologicalComplex.mapBifunctorMap (b.hom.app P) (b.hom.app N)
        (curriedTensor _) (.up ℤ) =
      b.hom.app (pullbackTensorTotal Z P N) ≫ φ.hom := by
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext_of_map (G ⋙ F)
    intro p q h
    let H := Scheme.Modules.tensorPullback (f ≫ g)
    let iZ : P.X p ⊗ N.X q ⟶ (pullbackTensorTotal Z P N).X n :=
      HomologicalComplex.ιMapBifunctor P N (curriedTensor Z.Modules) (.up ℤ) p q n h
    let iY : G.obj (P.X p) ⊗ G.obj (N.X q) ⟶
        (pullbackTensorTotal Y (Gc.obj P) (Gc.obj N)).X n :=
      HomologicalComplex.ιMapBifunctor (Gc.obj P) (Gc.obj N)
        (curriedTensor Y.Modules) (.up ℤ) p q n h
    let iX : F.obj (G.obj (P.X p)) ⊗ F.obj (G.obj (N.X q)) ⟶
        (pullbackTensorTotal X (Fc.obj (Gc.obj P)) (Fc.obj (Gc.obj N))).X n :=
      HomologicalComplex.ιMapBifunctor (Fc.obj (Gc.obj P)) (Fc.obj (Gc.obj N))
        (curriedTensor X.Modules) (.up ℤ) p q n h
    let iD : H.obj (P.X p) ⊗ H.obj (N.X q) ⟶
        (pullbackTensorTotal X ((H.mapHomologicalComplex (.up ℤ)).obj P)
          ((H.mapHomologicalComplex (.up ℤ)).obj N)).X n :=
      HomologicalComplex.ιMapBifunctor
        ((H.mapHomologicalComplex (.up ℤ)).obj P)
        ((H.mapHomologicalComplex (.up ℤ)).obj N)
        (curriedTensor X.Modules) (.up ℤ) p q n h
    let eg := ((Classical.choose (Scheme.Modules.module_pullback_tensor g))
      (P.X p) (N.X q)).hom
    let ef := ((Classical.choose (Scheme.Modules.module_pullback_tensor f))
      (G.obj (P.X p)) (G.obj (N.X q))).hom
    let ed := ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
      (P.X p) (N.X q)).hom
    let bP := (tensorCompMate f g).hom.app (P.X p)
    let bN := (tensorCompMate f g).hom.app (N.X q)
    let bT := (tensorCompMate f g).hom.app ((pullbackTensorTotal Z P N).X n)
    let bS := (tensorCompMate f g).hom.app (P.X p ⊗ N.X q)
    have hψ' : G.map iZ ≫ ψ.hom.f n = eg ≫ iY := hψ p q n h
    have hθ' : F.map iY ≫ θ.hom.f n = ef ≫ iX := hθ p q n h
    have hφ' : H.map iZ ≫ φ.hom.f n = ed ≫ iD := hφ p q n h
    clear hψ hθ hφ
    have hb : F.map (G.map iZ) ≫ bT = bS ≫ H.map iZ :=
      (tensorCompMate f g).hom.naturality iZ
    have hm : F.map eg ≫ ef ≫ (bP ⊗ₘ bN) = bS ≫ ed :=
      tensorCompMate_tensor f g (P.X p) (N.X q)
    have hi : iX ≫ (HomologicalComplex.mapBifunctorMap (b.hom.app P)
        (b.hom.app N) (curriedTensor X.Modules) (.up ℤ)).f n =
        (bP ⊗ₘ bN) ≫ iD := by
      change HomologicalComplex.ιMapBifunctor (Fc.obj (Gc.obj P)) (Fc.obj (Gc.obj N))
        (curriedTensor X.Modules) (.up ℤ) p q n h ≫ _ = _
      rw [HomologicalComplex.ι_mapBifunctorMap]
      simp only [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
      rfl
    change F.map (G.map iZ) ≫ F.map (ψ.hom.f n) ≫ θ.hom.f n ≫
        (HomologicalComplex.mapBifunctorMap (b.hom.app P) (b.hom.app N)
          (curriedTensor X.Modules) (.up ℤ)).f n =
      F.map (G.map iZ) ≫ bT ≫ φ.hom.f n
    rw [← F.map_comp_assoc, hψ', F.map_comp, Category.assoc,
      reassoc_of% hθ', hi, reassoc_of% hm, reassoc_of% hb, hφ']
  have hsol : HomologicalComplex.mapBifunctorMap (b.hom.app P) (b.hom.app N)
      (curriedTensor _) (.up ℤ) =
      θ.inv ≫ Fc.map ψ.inv ≫ b.hom.app (pullbackTensorTotal Z P N) ≫ φ.hom := by
    apply (cancel_epi θ.hom).1
    apply (cancel_epi (Fc.map ψ.hom)).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, ← Fc.map_comp_assoc,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp,
      show Fc.map (𝟙 _) = 𝟙 _ from Fc.map_id _] using hchain
  let : SymmetricCategory X.Modules := moduleSymmetric X
  have : MonoidalPreadditive X.Modules := modulePreadditive X
  let : MonoidalClosed X.Modules := moduleClosed X
  have : IsGrothendieckAbelian.{u} X.Modules := moduleGrothendieck X
  have : Abelian.HasFunctorialFlatResolution X.Modules := moduleResolutions X
  have : Functor.HasDerivedMonoidalCategory (DerivedCategory.Qh (C := X.Modules))
      (HomotopyCategory.quasiIso X.Modules (.up ℤ)) := moduleDerivedMonoidal X
  let : MonoidalCategory (DerivedCategory X.Modules) := schemeDerivedTensorMonoidal X
  let : Functor.LaxMonoidal (DerivedCategory.Q (C := X.Modules)) := pullbackDescentQLax X
  change (DerivedCategory.Q.map (b.hom.app P) ⊗ₘ
      DerivedCategory.Q.map (b.hom.app N)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q _ _ =
    Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
      DerivedCategory.Q.map θ.inv ≫ DerivedCategory.Q.map (Fc.map ψ.inv) ≫
      DerivedCategory.Q.map (b.hom.app (pullbackTensorTotal Z P N)) ≫
      DerivedCategory.Q.map φ.hom
  rw [Functor.LaxMonoidal.μ_natural]
  change pullbackTensorModelMap X (Fc.obj (Gc.obj P)) (Fc.obj (Gc.obj N)) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (b.hom.app P) (b.hom.app N) (curriedTensor _) (.up ℤ)) = _
  rw [hsol, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

end AlgebraicGeometry
