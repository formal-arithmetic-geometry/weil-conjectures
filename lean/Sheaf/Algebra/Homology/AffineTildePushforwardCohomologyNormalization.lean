/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Normalized affine pushforward cohomology

Source: Stacks Project, Tags 0AVW, 08D4 and 0DJ8.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

/-- Associated sheaf, with its scheme-module category displayed explicitly.
Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
abbrev affineTildeFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)


/-- Instance bridge for the displayed affine tilde abbreviation, reusing exact tilde's
existing zero-map instance. Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
@[instance] theorem affineTildeFunctor_preservesZero (A : Type u) [CommRing A] :
    (affineTildeFunctor A).PreservesZeroMorphisms :=
  affineBaseChangeTilde_preservesZero A

/-- The ordinary affine pushforward comparison, constructed from the tilde unit,
sections restriction and the tilde counit. Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
def affineTildePushforwardComparison (A B : Type u) [CommRing A] [CommRing B]
    (φ : B →+* A) :
    ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B ≅
      affineTildeFunctor A ⋙ Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)) := by
  let S := moduleSpecΓFunctor (R := .of A)
  let T := affineTildeFunctor B
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))
  let ν : ModuleCat.restrictScalars φ ⟶
      affineTildeFunctor A ⋙ P ⋙ moduleSpecΓFunctor (R := .of B) :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (tilde.toTildeΓNatIso (R := .of A)).hom
        (ModuleCat.restrictScalars φ) ≫
      (Functor.associator (affineTildeFunctor A) S (ModuleCat.restrictScalars φ)).hom ≫
      Functor.whiskerLeft (affineTildeFunctor A)
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom φ)).inv
  let σ : ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B ⟶
      affineTildeFunctor A ⋙ P :=
    { app := fun N ↦ T.map (ν.app N) ≫
        Scheme.Modules.fromTildeΓ (R := .of B) (P.obj ((affineTildeFunctor A).obj N))
      naturality := by
        intro N N' a
        dsimp only [Functor.comp_map]
        rw [← Functor.map_comp_assoc, ν.naturality, Functor.map_comp, Category.assoc]
        exact congrArg (fun f ↦ T.map (ν.app N) ≫ f)
          ((Scheme.Modules.fromTildeΓNatTrans (R := .of B)).naturality
            (P.map ((affineTildeFunctor A).map a))) }
  have : IsIso ν := by dsimp only [ν]; infer_instance
  have : IsIso σ := by
    apply (NatTrans.isIso_iff_isIso_app σ).2
    intro N
    have : ((affineTildeFunctor A).obj N).IsQuasicoherent := by
      change (tilde (R := .of A) N).IsQuasicoherent
      infer_instance
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A)
        ((affineTildeFunctor A).obj N)) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of B)
        (P.obj ((affineTildeFunctor A).obj N))) :=
      isIso_fromTildeΓ_pushforward (CommRingCat.ofHom φ) _
    dsimp only [σ]
    infer_instance
  exact asIso σ

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The actual map from ordinary module cohomology to derived affine pushforward.
No object or map is chosen from an existence theorem. Source: Stacks, Tags 0AVW and 0DJ8.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
def affineTildePushforwardCohomologyMap (A B : Type u) [CommRing A] [CommRing B]
    (φ : B →+* A) (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affineTildeFunctor B).obj ((ModuleCat.restrictScalars φ).obj (C.homology i)) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
          (DerivedCategory.Q.obj
            (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C))) := by
  let T := affineTildeFunctor A
  let F := ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))
  let : (affineTildeFunctor B).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (affineTildeFunctor B).PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits (affineTildeFunctor B) :=
    Functor.preservesFiniteLimits_of_preservesHomology (affineTildeFunctor B)
  let : PreservesFiniteColimits (affineTildeFunctor B) :=
    Functor.preservesFiniteColimits_of_preservesHomology (affineTildeFunctor B)
  let : F.PreservesHomology := inferInstance
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : P.Additive := inferInstance
  let D := (T.mapHomologicalComplex (.up ℤ)).obj C
  let a : (F.mapHomologicalComplex (.up ℤ)).obj C ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj D :=
    ((affineTildePushforwardComparison A B φ).hom.mapHomologicalComplex (.up ℤ)).app C
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  let β := (RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit
  exact ((C.sc i).mapHomologyIso F).inv ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
    H.map (DerivedCategory.Q.map a) ≫
    H.map (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D))

/-- Coordinates of the cohomology of any tilde representative.
Source: Stacks Project, Tags 01I9 and 06Z0.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
def affineTildeRepresentativeCohomologyIso (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : schemeDerivedCategory (Spec (.of A)))
    (t : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L) (i : ℤ) :
    C.homology i ≅ (moduleSpecΓFunctor (R := .of A)).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L) := by
  let T := affineTildeFunctor A
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : T.PreservesHomology := tilde_preservesHomology A
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  exact tilde.isoTop (R := .of A) (C.homology i) ≪≫
    (moduleSpecΓFunctor (R := .of A)).mapIso
      (((C.sc i).mapHomologyIso T).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          ((T.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫ H.mapIso t)

/-- The affine cohomology presentation is normalized by the right-derived unit
on all complexes of associated sheaves, and hence on every representative.
Source: Stacks Project, perfect.tex, Tag 0AVW, proof of
lemma-affine-morphism-equivalence; Tags 08D4 and 0DJ8, affine cohomology calculation.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization).

Proof: For the affine morphism Spec A to Spec B, higher direct images of
quasi-coherent modules vanish. Apply the unbounded acyclic-pushforward theorem
with bound one on inverse images of affine opens. Its comparison is the one
induced by the right-derived unit: use a K-injective resolution, apply sections,
and the truncation comparison in each degree. Composing the inverse comparison
with the tilde/Gamma counit and the identity-on-sections scalar restriction gives
d naturally on the entire quasi-coherent derived category. For a complex C of
A-modules, exact tilde and exact restriction of scalars identify its ordinary
cohomology with the source of the displayed map. The termwise comparison is
constructed from the same tilde unit and counit. The unit/counit triangle identity
therefore identifies its image under the right-derived unit with d at Q(tilde C)
after the canonical cohomology coordinates. Naturality of d with respect to the
representative isomorphism t gives the displayed equation at L. These arguments
use no boundedness of C; zero rings and zero complexes give the same identities. -/
theorem exists_affineTildePushforwardCohomologyNormalization
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    ∃ d : affineDerivedCohomologyModules A i ⋙
          (ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B) ≅
        (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
      ∀ (L : schemeDerivedQCohCategory (Spec (.of A)))
        (C : CochainComplex (ModuleCat.{u} A) ℤ)
        (t : DerivedCategory.Q.obj
          (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
        affineTildePushforwardCohomologyMap A B φ C i ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
            ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map t.hom) =
          (affineTildeFunctor B).map ((ModuleCat.restrictScalars φ).map
            (affineTildeRepresentativeCohomologyIso A C L.obj t i).hom) ≫ d.hom.app L := by sorry

end AlgebraicGeometry
