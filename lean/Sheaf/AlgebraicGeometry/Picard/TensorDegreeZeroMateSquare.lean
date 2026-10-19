/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare
import Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare
import Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit
import Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Degree-zero mates with the specified tensor pullback

Source: Stacks Project, Cohomology, Remark 08HY; flat-module comparison, Tag 06YJ.
(blueprint: lem-sc-picard-tensor-degree-zero-mate-square).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor-form degree-zero mate compatibility with the canonical single-image unit.
The derived module comparison is not assumed invertible. Only its source module's
ordinary direct image needs to be finite locally free.
Source: Stacks Project, Remark 08HY, canonical adjunction construction; Tag 06YJ.
(blueprint: lem-sc-picard-tensor-degree-zero-mate-square).

Proof:
1. Use the left-derived counit for tensor pullback chosen by
   exists_derivedPullbackComposition. At G[0] followed by the single-map comparison,
   it defines c:Lv*G[0] to (v*G)[0]. Compose the canonical derived base-change map
   with Rp'*(c) to get phi. This is IsDerivedModuleBaseChangeMap by definition.
2. The direct image M is finite locally free and hence flat. Its single complex is
   K-flat. The same left-derived counit at M[0] is therefore invertible. The inverse
   single-homology identification followed by the inverse H0 counit gives
   e0:k*M to H0(Lk*M[0]).
3. Apply derivedBaseChange_unit_compatibility to the single complex G[0].
   Naturality of the pinned tensor-pullback counit and the right-derived
   direct-image unit reduces its square to the ordinary termwise exchange map.
   The singleMapHomologicalComplex comparisons identify this exchange map with
   singleFunctor.map(moduleBaseChangeMap): check its degree-zero component and
   use functor identity laws. The quotient functor descends this equality to
   the homotopy category. Thus cg followed by single(beta) and the canonical
   single direct-image unit equals Lg(a) followed by phi.
4. Apply H0. canonicalDirectImageH0Unit identifies H0 of the direct-image unit
   followed by the canonical H0 isomorphism with the single-homology identification.
   Naturality of the single-homology isomorphism identifies the ordinary map.
   Cancel the invertible H0 source comparison to obtain the formula. Neither phi
   nor beta is cancelled. The zero module and rank zero require no change. -/
theorem tensorDegreeZeroMateSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [(tensorPullback (pullback.fst f g)).Additive]
    [HasInjectiveResolutions (Limits.pullback f g).Modules]
    (G : X.Modules) [((pushforward f).obj G).IsFiniteLocallyFree] :
    let M := (pushforward f).obj G
    let K := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0
    ∃ (e0 : (tensorPullback g).obj M ≅
        H.obj ((derivedPullback g).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M)))
      (φ : (derivedPullback g).obj K ⟶
        (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace)) 0).obj
            ((tensorPullback (pullback.fst f g)).obj G))),
      IsDerivedModuleBaseChangeMap f g G φ ∧
      moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition G =
        e0.hom ≫ H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f G)) ≫
          H.map φ ≫ (canonicalDirectImageH0Iso (pullback.snd f g)
            ((tensorPullback (pullback.fst f g)).obj G)).hom := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  classical
  let := canonicalTensorPullbackAdditive g
  let M := (pushforward f).obj G
  let εg := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) g
  let εv := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) (pullback.fst f g)
  let cg := εg.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app M))
  let cv := εv.app ((HomotopyCategory.singleFunctor _ 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback (pullback.fst f g)) (ComplexShape.up ℤ) 0).hom.app G))
  have hcg : IsDerivedModulePullbackComparison g M cg := by
    refine ⟨εg, ?_, rfl⟩
    exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) g
  have hcv : IsDerivedModulePullbackComparison (pullback.fst f g) G cv := by
    refine ⟨εv, ?_, rfl⟩
    exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (pullback.fst f g)
  have hflat : M.IsFlatOver (𝟙 S) := by
    intro V U e
    let := ((𝟙 S : S ⟶ S).appLE V.1 U.1 e).hom.toAlgebra
    have : Module.Flat Γ(S, V.1) Γ(S, U.1) :=
      HasRingHomProperty.appLE @Flat (𝟙 S) inferInstance V U e
    have : Module.Projective Γ(S, U.1) Γ(M, U.1) :=
      (finitePresentation_projective_sections M U.2).2
    let : Module Γ(S, V.1) Γ(M, U.1) :=
      Module.compHom _ ((𝟙 S : S ⟶ S).appLE V.1 U.1 e).hom
    have : IsScalarTower Γ(S, V.1) Γ(S, U.1) Γ(M, U.1) :=
      ⟨fun a b m ↦ mul_smul _ _ _⟩
    exact Module.Flat.trans Γ(S, V.1) Γ(S, U.1) Γ(M, U.1)
  have : IsIso cg := isIso_modulePullbackComparison_of_isFlatOver_identity g M hflat cg hcg
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0
  let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).app ((tensorPullback g).obj M)
  let e := H.mapIso (asIso cg) ≪≫ k
  let φ := schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map cv
  refine ⟨e.symm, φ, ⟨cv, hcv, rfl⟩, ?_⟩
  have hs := congrArg H.map
    (tensorSingleBaseChangeSquare f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition G)
  have hu := canonicalDirectImageH0Unit (pullback.snd f g)
    ((tensorPullback (pullback.fst f g)).obj G)
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).hom.naturality
      (moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) pullback.condition G)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  change H.map (canonicalSingleDirectImageMap (pullback.snd f g)
      ((tensorPullback (pullback.fst f g)).obj G)) ≫
    (canonicalDirectImageH0Iso (pullback.snd f g)
      ((tensorPullback (pullback.fst f g)).obj G)).hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).hom.app
          ((pushforward (pullback.snd f g)).obj
            ((tensorPullback (pullback.fst f g)).obj G)) at hu
  simp only [Functor.map_comp] at hs
  have he : e.hom ≫
      moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g) pullback.condition G =
    H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f G)) ≫ H.map φ ≫
      (canonicalDirectImageH0Iso (pullback.snd f g)
        ((tensorPullback (pullback.fst f g)).obj G)).hom := by
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
    dsimp only [k, M]
    erw [← hn, ← hu]
    simpa only [φ, cg, cv, εg, εv, M, Functor.map_comp, Category.assoc] using
      congrArg (fun q ↦ q ≫ (canonicalDirectImageH0Iso (pullback.snd f g)
        ((tensorPullback (pullback.fst f g)).obj G)).hom) hs
  simpa only [H, Iso.symm_hom, Functor.id_obj, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun q ↦ e.inv ≫ q) he

end AlgebraicGeometry.Scheme.Modules
