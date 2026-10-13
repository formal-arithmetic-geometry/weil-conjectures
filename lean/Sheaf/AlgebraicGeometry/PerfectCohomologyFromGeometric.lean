/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups J2 and H3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Topology.RingedSpaceModuleCohomology

import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.RingTheory.Flat.Stability
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Finite projective complex models for cohomology over an affine base

Source: Stacks Project, Tags 0B91(2), 08EB and 01F2.
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images-perfectness).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite locally free coefficients are relatively flat along a flat morphism.
This is transitivity of flatness on each pair of affine opens. -/
private theorem isFlatOver_of_isFiniteLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (F : X.Modules) [F.IsFiniteLocallyFree] : F.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat f ‹_› V U e
  have : Module.Projective Γ(X, U.1) Γ(F, U.1) :=
    (finitePresentation_projective_sections F U.2).2
  let : Module Γ(S, V.1) Γ(F, U.1) :=
    Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(S, V.1) Γ(X, U.1) Γ(F, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(S, V.1) Γ(X, U.1) Γ(F, U.1)

/-- Scalar multiplication commutes with module-valued cohomology. -/
private theorem moduleCohomology_map_smulHom
    (Y : Scheme.{u}) (q : ℕ) (M : Y.Modules) (a : Γ(Y, ⊤))
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace q).obj M) :
    (RingedSpace.moduleCohomology Y.toRingedSpace q).map (M.smulHom a) x = a • x := by
  have : IsGrothendieckAbelian.{u} Y.Modules := isGrothendieckAbelian Y
  let G : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    RingedSpace.globalSectionsFunctor Y.toRingedSpace
  have : G.Additive := by constructor; intro M N a b; rfl
  have h := G.rightDerived_map_app_eq
    { app N := smulHom N a, naturality _ _ φ := (smulHom_naturality φ a).symm }
    { app N := ModuleCat.ofHom (LinearMap.lsmul Γ(Y, ⊤) N a)
      naturality := by intro N N' φ; ext y; simp }
    (fun N ↦ by ext y; exact smulHom_app_top_apply N a y) q M
  exact congrArg (fun g ↦ g x) h

/-- The affine Leray edge retains the scalar action from the base. -/
private theorem nonempty_module_leray_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsAffine Y]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Nonempty (((ModuleCat.restrictScalars f.appTop.hom).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)) ≅
      (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F)) := by
  classical
  have : IsGrothendieckAbelian.{u} X.Modules := isGrothendieckAbelian X
  obtain ⟨ε, _, hε⟩ := exists_lerayEdge_isIso_of_vanishing f
  have : IsIso ((ε q).app F) := hε F
    (fun n p hp ↦ isZero_affine_higherDirectImage_moduleCohomology f F
      inferInstance n p hp) q
  let e := asIso ((ε q).app F)
  let S := (ModuleCat.restrictScalars f.appTop.hom).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
  let T : ModuleCat.{u} Γ(Y, ⊤) :=
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj
    (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F)
  let l : S →ₗ[Γ(Y, ⊤)] T :=
    { toFun := fun x ↦ ((ε q).app F) x
      map_add' := by intro x y; exact ((ε q).app F).hom.map_add x y
      map_smul' := by
        intro a x
        let : Module Γ(Y, ⊤) T := T.isModule
        have h := (ε q).naturality (F.smulHom (f.appTop a))
        have hs := moduleCohomology_map_smulHom X q F (f.appTop a) x
        have ht := higherDirectImage_map_smulHom f q F a
        have hh := congrArg (fun g ↦ g x) h
        change ((ε q).app F)
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (F.smulHom (f.appTop a)) x) =
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).map
              (F.smulHom (f.appTop a))) (((ε q).app F) x) at hh
        rw [hs] at hh
        refine hh.trans ?_
        change (RingedSpace.globalSectionsFunctor Y.toRingedSpace).map
          ((higherDirectImage f q).map (F.smulHom (f.appTop a))) _ = _
        rw [ht]
        exact smulHom_app_top_apply _ a _ }
  let L : S ⟶ T := @ModuleCat.ofHom Γ(Y, ⊤) _ S T _ S.isModule _ T.isModule l
  have : IsIso L := (ConcreteCategory.isIso_iff_bijective L).mpr
    (ConcreteCategory.bijective_of_isIso e.hom)
  exact ⟨asIso L⟩

set_option maxHeartbeats 400000 in
-- Derived comparisons unfold composed functors and scalar restrictions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper flat finite-presentation morphisms with finite locally free coefficients admit a
bounded finite projective complex model for every cohomology module over the affine base.
No coherence or valuation hypothesis on the base ring is required for this model.
Source: Stacks Project, perfect.tex, Tags 0B91(2) and 08EB; cohomology.tex, Tag 01F2.
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images-perfectness)

Proof: Finite local freeness implies finite presentation and quasi-coherence. Since f is
flat, every local free summand is flat over the base, so the coefficient module is relatively
flat. Apply perfect_derivedDirectImage_baseChange to obtain perfectness of Rf_*F. On the
affine base Spec A, perfect_iff_affine_bounded_projective (Tag 08EB) gives a bounded
complex P of finite projective A-modules whose associated-sheaf complex represents Rf_*F.
Perfect objects have quasi-coherent homology: this is local, and on each strictly perfect
neighbourhood it follows from exactness of the affine associated-sheaf functor. That same
exactness identifies the homology sheaves of the global model with the associated sheaves
of H^q(P). Their positive cohomology on Spec A vanishes by affine acyclicity.
For scalar compatibility, take the additive Leray edge supplied by
exists_lerayEdge_isIso_of_vanishing. Affine vanishing for the higher direct images makes
it invertible. Its naturality with respect to F.smulHom (f.appTop a), together with
rightDerived_map_app_eq for sections and higherDirectImage_map_smulHom, proves that
its underlying additive map is linear over Gamma(Spec A). Lift it to a module morphism;
bijectivity makes this lifted morphism invertible. The comparison between unbounded
derived homology and ordinary higher direct images identifies its target with sections
of the derived model's homology. Exactness of tilde identifies this with tilde(H^q(P)).
Restrict scalars along GammaSpecIso.inv and apply tilde.toTildeΓNatIso to recover
H^q(P). The terminal-object restriction in moduleSpecΓFunctor acts by the identity
on the section ring, giving the required scalar-compatible comparison.
For an empty X or rank-zero coefficient use the zero complex; the
same proof also covers q above the complex bounds, when both modules vanish. The model is
used only in propositions, and no definition selects an arbitrary witness. -/
theorem exists_finiteProjectiveComplex_model_moduleCohomology
    {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (d : ℕ) (F : X.Modules) [F.IsFiniteLocallyFreeOfRank d] (q : ℕ) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n)) ∧
      Nonempty (((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)) ≅ P.homology (q : ℤ)) := by
  classical
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  have hadd {Y Z : Scheme.{u}} (k : Y ⟶ Z) : (tensorPullback k).Additive := by
    obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction k
    let : (tensorPullback k).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (tensorPullback k).Additive := hadd
  have : F.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F d
  let E := (schemeDerivedDirectImage f).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  have hE : Scheme.IsPerfect (Spec (.of A)) E :=
    (perfect_derivedDirectImage_baseChange f F
      (isFlatOver_of_isFiniteLocallyFree f F)).1
  have hqc : schemeDerivedQCohProperty (Spec (.of A)) E :=
    schemeDerivedQCohProperty_of_isPerfect _ E hE
  let EQ : schemeDerivedQCohCategory (Spec (.of A)) := ⟨E, hqc⟩
  obtain ⟨P, hb, hf, hp, ⟨e⟩⟩ :=
    (perfect_iff_affine_bounded_projective A EQ).mp hE
  refine ⟨P, hb, fun n ↦ ⟨hf n, hp n⟩, ?_⟩
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  have : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
  have : T.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    exact Functor.additive_of_preservesBinaryBiproducts T
  have htilde : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N),
      PreservesLimit (parallelPair g 0) T := by
    intro M N g
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
    let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    have : (T.obj M).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) M).IsQuasicoherent
      infer_instance
    have : (T.obj N).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) N).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map g)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map g)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
    let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
    let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map g))
    have ht : t ≫ g = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
    let c := Limits.KernelFork.ofι t ht
    have hc : Limits.IsLimit (c.map T) := by
      apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map g))
      exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
    have hc' : Limits.IsLimit c :=
      Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact Limits.preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  let : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N),
      PreservesLimit (parallelPair g 0) T := htilde
  have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) (q : ℤ)
  let eh : H.obj E ≅ T.obj (P.homology (q : ℤ)) :=
    H.mapIso e ≪≫ (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _ ≪≫
      (T.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) (q : ℤ)).app P
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let eR : H.obj E ≅ (D.rightDerived q).obj F :=
    D.homologyRightDerivedFunctorObjSingleFunctorIso F q
  obtain ⟨edge⟩ := nonempty_module_leray_iso f F q
  let R := ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  let G := moduleSpecΓFunctor (R := .of A)
  let M := (D.rightDerived q).obj F
  let S := R.obj ((RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace).obj M)
  let N := G.obj M
  let eΓ : S ≅ N :=
    ({ toFun := id
       invFun := id
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_add' := fun _ _ ↦ rfl
       map_smul' := by
         intro a x
         change (Scheme.ΓSpecIso (.of A)).inv a • x =
           ((moduleRings (Spec (.of A)).toRingedSpace).obj.map
             ((initialOpOfTerminal isTerminalTop).to (Opposite.op ⊤))).hom
             ((Scheme.ΓSpecIso (.of A)).inv a) • x
         rw [show (initialOpOfTerminal isTerminalTop).to
           (Opposite.op (⊤ : (Spec (.of A)).Opens)) = 𝟙 _ from Subsingleton.elim _ _,
           CategoryTheory.Functor.map_id]
         rfl } : S ≃ₗ[A] N).toModuleIso
  let eC := (ModuleCat.restrictScalarsComp (Scheme.ΓSpecIso (.of A)).inv.hom
    f.appTop.hom).app ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
  let e1 := R.mapIso edge
  let e2 : N ≅ G.obj (T.obj (P.homology (q : ℤ))) := G.mapIso (eR.symm ≪≫ eh)
  let e3 : G.obj (T.obj (P.homology (q : ℤ))) ≅ P.homology (q : ℤ) :=
    ((tilde.toTildeΓNatIso (R := .of A)).app (P.homology (q : ℤ))).symm
  exact ⟨eC ≪≫ e1 ≪≫ eΓ ≪≫ e2 ≪≫ e3⟩

end AlgebraicGeometry.Scheme.Modules
