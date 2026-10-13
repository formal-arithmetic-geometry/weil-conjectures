/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # AffineBaseChangeTildeCanonicalGlobalComparison

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-canonical-global-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Affine mate calculation for the fixed module-derived tensor construction.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof and equation-bc;
more-algebra.tex, Tag 06Y6; perfect.tex, Tag 08IB.
(blueprint: lem-pc-affine-base-change-tilde-canonical-global-comparison).

Proof: unfold the fixed tensor model, whose functor is constructed by an R-K-flat
resolution and extension of scalars. Affine higher-direct-image vanishing, with
unbounded cohomological bound one, identifies derived direct-image cohomology
naturally with ordinary direct image of cohomology. Compose with the tilde/Gamma
counit and restriction-of-scalars comparison to obtain d. Exact tilde identifies
the cohomology of the scalar-extended resolution with the associated sheaf of
its module cohomology. The cartesian tensor-algebra isomorphism transports it to
A', giving eU. On this fixed resolution the scheme mate is the scalar extension
of the augmentation to the restricted A-complex, by the tensor-pullback unit
formula. Its homology is the fixed model's comparison. The localized comparison
is its adjoint after extension to A'. The inverse pullback counit and e give the
target coordinate b. Applying homology to the mate equation gives the square.
There is no comparison of two arbitrary derived functors or tensor actions in
this statement; that is the separate model-independence lemma. Zero rings and
zero complexes obey the same construction; no boundedness is used. -/
theorem exists_affineBaseChangeTildeCanonicalGlobalComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    :
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let a := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b
    ∃ eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L := by sorry

end AlgebraicGeometry
