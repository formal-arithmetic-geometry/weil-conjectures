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

/-- The normalization equation for a fixed representative.
Source: Stacks Project, Tags 0AVW, 08D4 and 0DJ8.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
def affineTildePushforwardNormalizationEquation
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (d : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B) ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i)
    (L : schemeDerivedQCohCategory (Spec (.of A)))
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (t : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj) : Prop :=
  affineTildePushforwardCohomologyMap A B φ C i ≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map t.hom) =
    (affineTildeFunctor B).map ((ModuleCat.restrictScalars φ).map
      (affineTildeRepresentativeCohomologyIso A C L.obj t i).hom) ≫ d.hom.app L

/-- The identity-representative part of affine pushforward normalization.
Source: Stacks Project, Tags 0AVW, 08D4 and 0DJ8.
Proof: construct the affine comparison using acyclic pushforward and verify the
canonical representative by the tilde/Gamma counit and derived unit identities.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization-base). -/
def affineTildePushforwardIdentityNormalization
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (d : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B) ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  ∀ (L : schemeDerivedQCohCategory (Spec (.of A)))
    (t : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
    (∃ h : DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) = L.obj,
      t.hom = eqToHom h) →
      affineTildePushforwardNormalizationEquation A B φ i d L C t

/-- Identity representatives determine the comparison by naturality.
Source: Stacks Project, Tag 0AVW.
Proof: transport the identity equation along the representative isomorphism,
using functoriality of derived pushforward, homology, and the cohomology coordinates.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization-extend). -/
theorem affineTildePushforwardCohomologyNormalization_extend
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (d : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B) ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i)
    (h : ∀ C : CochainComplex (ModuleCat.{u} A) ℤ,
      affineTildePushforwardIdentityNormalization A B φ i d C) :
    ∀ (L : schemeDerivedQCohCategory (Spec (.of A)))
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (t : DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
      affineTildePushforwardNormalizationEquation A B φ i d L C t := by
  intro L C t
  let K := DerivedCategory.Q.obj
    (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C)
  have hK : schemeDerivedQCohProperty (Spec (.of A)) K := by
    intro n
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).mapIso t.symm)
      (L.property n)
  let L₀ : schemeDerivedQCohCategory (Spec (.of A)) := ⟨K, hK⟩
  have h₀ := h C L₀ (Iso.refl K) ⟨rfl, rfl⟩
  let a : L₀ ⟶ L := ObjectProperty.homMk t.hom
  have hn := d.hom.naturality a
  have hb : (affineTildeRepresentativeCohomologyIso A C L.obj t i).hom =
      (affineTildeRepresentativeCohomologyIso A C L₀.obj (Iso.refl K) i).hom ≫
        (moduleSpecΓFunctor (R := .of A)).map
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).map t.hom) := by
    dsimp only [affineTildeRepresentativeCohomologyIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  unfold affineTildePushforwardNormalizationEquation at h₀ ⊢
  dsimp only [Iso.refl_hom] at h₀
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id] at h₀
  erw [h₀, Category.assoc]
  change (affineTildeFunctor B).map ((ModuleCat.restrictScalars φ).map
      ((moduleSpecΓFunctor (R := .of A)).map
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).map t.hom))) ≫
      d.hom.app L = _ at hn
  erw [← hn]
  rw [hb]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Base affine comparison, normalized on identity representatives.
Source: Stacks Project, Tags 0AVW, 08D4 and 0DJ8.
Proof: On inverse images of affine opens, quasi-coherent sheaves have no higher
cohomology. The bound-one truncation calculation of Tag 08D4 therefore identifies
H^i(Rf_*L) naturally with f_*H^i(L), also for unbounded L. Use a K-injective
resolution to compute this comparison: the map from termwise pushforward into
Rf_* is the right-derived unit, so its cohomology is this comparison whenever
the input is a complex of associated sheaves. The quasi-coherent counit identifies
T_A Gamma_A H^i(L) with H^i(L); apply f_* and the ordinary affine pushforward
comparison to identify T_B res_phi Gamma_A H^i(L) with f_*H^i(L). Compose with
the inverse cohomology comparison to obtain d, naturally in L. For Q(T_A C),
exactness of tilde and restriction of scalars identifies cohomology with
T_B res_phi H^i(C). Under this identification the tilde unit/counit triangle
identity makes the preceding ordinary comparison precisely the termwise map
in affineTildePushforwardCohomologyMap. Its composite with the derived unit
is thus the coordinate map followed by d. This proves the identity case.
For t.hom = eqToHom h, eliminate h and use uniqueness of inverses to reduce
t to the identity isomorphism. No step requires a nonzero ring or a bound on C.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization-base). -/
theorem affineTildePushforwardCohomologyNormalization_base
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    ∃ d : affineDerivedCohomologyModules A i ⋙
          (ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B) ≅
        (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
      ∀ C : CochainComplex (ModuleCat.{u} A) ℤ,
        affineTildePushforwardIdentityNormalization A B φ i d C := by
  sorry

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
            (affineTildeRepresentativeCohomologyIso A C L.obj t i).hom) ≫ d.hom.app L := by
  obtain ⟨d, hd⟩ := affineTildePushforwardCohomologyNormalization_base A B φ i
  refine ⟨d, ?_⟩
  intro L C t
  have h := affineTildePushforwardCohomologyNormalization_extend A B φ i d hd L C t
  simpa [affineTildePushforwardNormalizationEquation] using h

end AlgebraicGeometry
