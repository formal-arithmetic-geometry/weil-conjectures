/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.FiniteStratificationWidePullback
import Sheaf.AlgebraicGeometry.FiniteTypeConstantModulePullback
public import Sheaf.AlgebraicGeometry.NormalizedLocalModulePullback

/-!
# Common finite stratifications and pullback of chosen module trivializations

Source: Stacks Project, Modules on Sites, Tag 093R, and the common-strata argument
in the finite-reductions proof, Step 6
(blueprint: lem-sfb-adic-finite-stratification-pullback).

The Boolean site parameter is false for the small etale site and true for the small
pro-etale site. `AsSmall` enlarges only the arrow universe to the object universe;
it retains every original site object. Coefficients are arbitrary commutative rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
-- The adjunction and dependent scalar-restriction comparisons need this elaboration budget.
set_option maxHeartbeats 100000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The two sites in Stacks 093R, before the harmless small-model transport.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationSite (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- Original arrow universes of the sites in Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationSiteCategory (pro : Bool) (X : Scheme.{u}) :
    Category.{u} (adicStratificationSite pro X) :=
  match pro with
  | false => inferInstanceAs (Category.{u} X.Etale)
  | true => inferInstanceAs (Category.{u} X.ProEt)

/-- The specified topology, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationTopology (pro : Bool) (X : Scheme.{u}) :
    GrothendieckTopology (adicStratificationSite pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => ProEt.topology X

/-- Genuine scheme-theoretic base change, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationBaseChange (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationSite pro Y ⥤ adicStratificationSite pro X :=
  match pro with
  | false => MorphismProperty.Over.pullback @Etale ⊤ f
  | true => proEtaleBaseChange f

/-- Continuity transported from the existing scheme sites, Stacks 093R and 09A5.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationBaseChangeContinuous (pro : Bool) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (adicStratificationBaseChange pro f).IsContinuous
      (adicStratificationTopology pro Y) (adicStratificationTopology pro X) :=
  match pro with
  | false => AlgebraicGeometry.Etale.isContinuous_overPullback f
  | true => proEtaleBaseChange_isContinuous f

/-- An equivalent small site retaining every original object, Stacks size convention.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModel (pro : Bool) (X : Scheme.{u}) :=
  AsSmall.{u + 1} (adicStratificationSite pro X)

/-- Transported topology, Stacks size convention and Tag 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationModelTopology (pro : Bool) (X : Scheme.{u}) :=
  (AsSmall.down : adicStratificationModel pro X ⥤ adicStratificationSite pro X).inducedTopology
    (adicStratificationTopology pro X)

/-- Base change transported to the equivalent small sites, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModelBaseChange (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationModel pro Y ⥤ adicStratificationModel pro X :=
  AsSmall.down ⋙ adicStratificationBaseChange pro f ⋙ AsSmall.up

/-- The inverse transport is continuous by the equivalence of sites, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelUpContinuous (pro : Bool) (X : Scheme.{u}) :
    (AsSmall.up : adicStratificationSite pro X ⥤ adicStratificationModel pro X).IsContinuous
      (adicStratificationTopology pro X) (adicStratificationModelTopology pro X) :=
  inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1}
    (C := adicStratificationSite pro X)).functor.IsContinuous
      (adicStratificationTopology pro X)
      ((AsSmall.equiv.{u, u + 1, u + 1}
        (C := adicStratificationSite pro X)).inverse.inducedTopology
          (adicStratificationTopology pro X)))

private instance adicModelDownContinuous (pro : Bool) (X : Scheme.{u}) :
    (AsSmall.down : adicStratificationModel pro X ⥤ adicStratificationSite pro X).IsContinuous
      (adicStratificationModelTopology pro X) (adicStratificationTopology pro X) := by
  unfold adicStratificationModelTopology
  infer_instance

/-- Continuity on the small model, Stacks 093R and the size convention.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelBaseChangeContinuous (pro : Bool) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (adicStratificationModelBaseChange pro f).IsContinuous
      (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X) :=
  haveI := Functor.isContinuous_comp (adicStratificationBaseChange pro f) AsSmall.up
    (adicStratificationTopology pro Y) (adicStratificationTopology pro X)
    (adicStratificationModelTopology pro X)
  Functor.isContinuous_comp AsSmall.down (adicStratificationBaseChange pro f ⋙ AsSmall.up)
    (adicStratificationModelTopology pro Y) (adicStratificationTopology pro Y)
    (adicStratificationModelTopology pro X)

/-- Ring sheafification on the transported small site, using the usual concrete
sheafification construction. Naming the instance prevents repeated search through
scheme-site constructions. Source: Stacks 00ZG.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelRingSheafify (pro : Bool) (X : Scheme.{u}) :
    HasWeakSheafify (adicStratificationModelTopology pro X) RingCat.{u + 1} :=
  (fun {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C) ↦
    (inferInstance : HasWeakSheafify J RingCat.{u + 1}))
      (adicStratificationModelTopology pro X)

/-- Additive sheafification on the small model, specialized from the generic construction.
Source: Stacks 00ZG (blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelAddSheafify (pro : Bool) (X : Scheme.{u}) :
    HasWeakSheafify (adicStratificationModelTopology pro X) AddCommGrpCat.{u + 1} :=
  (fun {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C) ↦
    (inferInstance : HasWeakSheafify J AddCommGrpCat.{u + 1}))
      (adicStratificationModelTopology pro X)

/-- Local bijections characterize additive sheafification on the small model.
Source: Stacks 00ZG (blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelAddWEquals (pro : Bool) (X : Scheme.{u}) :
    (adicStratificationModelTopology pro X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  (fun {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C) ↦
    (inferInstance : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}))
      (adicStratificationModelTopology pro X)

/-- Ring-valued left Kan extensions exist on the small models.
Source: Stacks 03D2 (blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModelRingLeftKan (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ P : (adicStratificationModel pro Y)ᵒᵖ ⥤ RingCat.{u + 1},
      (adicStratificationModelBaseChange pro f).op.HasLeftKanExtension P := by
  intro P
  have h : ∀ W : (adicStratificationModel pro X)ᵒᵖ,
      HasColimit (CostructuredArrow.proj (adicStratificationModelBaseChange pro f).op W ⋙ P) := by
    intro W
    have : HasColimits RingCat.{u + 1} := RingCat.Colimits.hasColimits_ringCat
    have : HasColimitsOfShape
        (CostructuredArrow (adicStratificationModelBaseChange pro f).op W)
          RingCat.{u + 1} := HasColimitsOfSize.has_colimits_of_shape _
    exact HasColimitsOfShape.has_colimit _
  exact Functor.instHasLeftKanExtension _ _

attribute [local irreducible] adicStratificationModelTopology

/-- Constant-ring module sheaves on the chosen site, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationModules (pro : Bool) (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] :=
  ringedSiteModules.{u + 1} ((constantSheaf (adicStratificationModelTopology pro X)
    RingCat.{u + 1}).obj (RingCat.of R))

/-- The specified constant-section map rho, Stacks 0H7J and 093R.
Its adjoint is the canonical constant-ring inverse-image comparison.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationRho (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSheaf (adicStratificationModelTopology pro Y) RingCat.{u + 1}).obj (RingCat.of R) ⟶
      ((adicStratificationModelBaseChange pro f).sheafPushforwardContinuous RingCat.{u + 1}
        (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X)).obj
          ((constantSheaf (adicStratificationModelTopology pro X) RingCat.{u + 1}).obj
            (RingCat.of R)) :=
  ((sheafificationAdjunction (adicStratificationModelTopology pro Y) RingCat.{u + 1}).homEquiv
    _ _).symm (Functor.whiskerLeft (adicStratificationModelBaseChange pro f).op
      (toSheafify (adicStratificationModelTopology pro X)
        ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))))

/-- The existing module direct image has a left adjoint. Specializing the generic
small-site proof avoids repeating its Kan-extension and sheafification instance search.
Source: Stacks 03D2 (blueprint: lem-sfb-adic-finite-stratification-pullback). -/
instance adicStratificationModulePushforwardRightAdjoint
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u + 1} (adicStratificationRho pro R f)).IsRightAdjoint :=
  by infer_instance

/-- Canonical module pullback along rho, Stacks 03D2 and 093R.
This is the existing sheafified module Kan extension, not an arbitrary functor.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationPullback (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    adicStratificationModules pro Y R ⥤ adicStratificationModules pro X R :=
  SheafOfModules.pullback.{u + 1} (adicStratificationRho pro R f)

/-- The ring comparison adjoint to constant sections, Stacks 0H7J.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationRingMap (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (adicStratificationModelBaseChange pro f) RingCat.{u + 1}
    (adicStratificationModelTopology pro Y) (adicStratificationModelTopology pro X)).homEquiv
    _ _).symm (adicStratificationRho pro R f)

/-- The specified coefficient map fixes constant scalars, by sheafification adjunction.
Source: Stacks 0H7J and 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
private theorem adicStratificationRho_constants
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : (adicStratificationModel pro Y)ᵒᵖ) :
    (toSheafify (adicStratificationModelTopology pro Y)
      ((Functor.const (adicStratificationModel pro Y)ᵒᵖ).obj (RingCat.of R))).app W ≫
        (adicStratificationRho pro R f).hom.app W =
      (toSheafify (adicStratificationModelTopology pro X)
        ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))).app
          ((adicStratificationModelBaseChange pro f).op.obj W) := by
  let F := ((adicStratificationModelBaseChange pro f).sheafPushforwardContinuous
    RingCat.{u + 1} (adicStratificationModelTopology pro Y)
      (adicStratificationModelTopology pro X)).obj
        ((constantSheaf (adicStratificationModelTopology pro X) RingCat.{u + 1}).obj
          (RingCat.of R))
  have h := ((sheafificationAdjunction (adicStratificationModelTopology pro Y)
    RingCat.{u + 1}).homEquiv _ F).apply_symm_apply
      (Functor.whiskerLeft (adicStratificationModelBaseChange pro f).op
        (toSheafify (adicStratificationModelTopology pro X)
          ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))))
  change toSheafify _ _ ≫ (adicStratificationRho pro R f).hom = _ at h
  exact congrArg (fun k ↦ k.app W) h

attribute [local irreducible] adicStratificationRho

/-- The specified ring comparison is invertible, Stacks 0H7J and proof Step 5.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: base change preserves a terminal site object, also after transport to AsSmall.
The composite of constant sheafification and inverse image is therefore left adjoint
to evaluation at the base-changed terminal object, just as target constant sheafification
is. Uniqueness of left adjoints gives an isomorphism. Its adjoint agrees with rho:
apply the source constant-sheaf adjunction and check the constant-section equation
at the terminal object. Thus the prescribed map is the hom of this isomorphism.
Neither finiteness nor a Noetherian hypothesis on R enters the argument. -/
theorem adicStratificationRingMap_isIso (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (adicStratificationRingMap pro R f) := by
  let b := adicStratificationModelBaseChange pro f
  have : HasTerminal (adicStratificationSite pro Y) := by
    cases pro
    · exact inferInstanceAs (HasTerminal Y.Etale)
    · exact inferInstanceAs (HasTerminal Y.ProEt)
  have : HasTerminal (adicStratificationModel pro Y) := inferInstance
  have : PreservesFiniteLimits (adicStratificationBaseChange pro f) := by
    cases pro
    · exact inferInstanceAs
        (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
    · exact proEtaleBaseChange_preservesFiniteLimits f
  have : PreservesFiniteLimits
      (AsSmall.down : adicStratificationModel pro Y ⥤ adicStratificationSite pro Y) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro Y)).inverse)
  have : PreservesFiniteLimits
      (AsSmall.up : adicStratificationSite pro X ⥤ adicStratificationModel pro X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro X)).functor)
  have : PreservesFiniteLimits b :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.down ⋙ adicStratificationBaseChange pro f ⋙ AsSmall.up))
  let T := ⊤_ (adicStratificationModel pro Y)
  let hT : IsTerminal T := terminalIsTerminal
  let hGT : IsTerminal (b.obj T) := hT.isTerminalObj b T
  let J := adicStratificationModelTopology pro Y
  let K := adicStratificationModelTopology pro X
  let ar := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    b RingCat.{u + 1} J K
  let av := constantSheafAdj J RingCat.{u + 1} hT
  let au := constantSheafAdj K RingCat.{u + 1} hGT
  let ac := (av.comp ar).ofNatIsoRight
    (b.sheafPushforwardContinuousCompSheafSectionsObjIso RingCat.{u + 1} J K (op T))
  let c := (ac.leftAdjointUniq au).app (RingCat.of R)
  have hc : ar.homEquiv _ _ c.hom = adicStratificationRho pro R f := by
    apply (av.homEquiv _ _).injective
    have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app ac au (RingCat.of R)
    change ac.homEquiv _ _ c.hom = _ at ht
    dsimp only [ac] at ht
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at ht
    change av.homEquiv _ _ (ar.homEquiv _ _ c.hom) ≫ 𝟙 _ = au.unit.app _ at ht
    rw [Category.comp_id] at ht
    rw [ht]
    change (toSheafify K
      ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))).app
        (op (b.obj T)) =
      (toSheafify J
        ((Functor.const (adicStratificationModel pro Y)ᵒᵖ).obj (RingCat.of R))).app (op T) ≫
          (adicStratificationRho pro R f).hom.app (op T)
    exact (adicStratificationRho_constants pro R f (op T)).symm
  have hm : adicStratificationRingMap pro R f = c.hom := by
    apply (ar.homEquiv _ _).injective
    exact ((ar.homEquiv _ _).apply_symm_apply _).trans hc.symm
  rw [hm]
  infer_instance

/-- Actual constant sections of the existing module sheafification, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationConstantSection (pro : Bool) (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (M : ModuleCat.{u + 1} R)
    (W : (adicStratificationModel pro X)ᵒᵖ) (m : M) :
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro X) R).obj M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1}
    (toSheafify (adicStratificationModelTopology pro X)
      ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R)))).unit.app
        ((SheafOfModules.strictPerfectConstantPresheaf
          (C := adicStratificationModel pro X) R).obj M)).app W) m

set_option backward.isDefEq.respectTransparency false in
/-- The uniquely normalized comparison for constant modules, Stacks 093R and proof Steps 5–7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: send each constant generator m to the constant section m after base change.
Naturality and R-linearity give a map of constant module presheaves; sheafification and
the module adjunction give c. Uniqueness follows from sheafification's universal property:
every section is locally a constant generator. This specifies actual module maps, with
the scalar action from rho, for arbitrary modules and rings. -/
theorem adicStratificationConstantMap_existsUnique
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} R) :
    ∃! c : (adicStratificationPullback pro R f).obj
        ((SheafOfModules.strictPerfectConstantSheaf
          (adicStratificationModelTopology pro Y) R).obj M) ⟶
        (SheafOfModules.strictPerfectConstantSheaf
          (adicStratificationModelTopology pro X) R).obj M,
      ∀ (W : (adicStratificationModel pro Y)ᵒᵖ) (m : M),
        (((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)).homEquiv
          _ _ c).val.app W) (adicStratificationConstantSection pro R Y M W m) =
            adicStratificationConstantSection pro R X M
              ((adicStratificationModelBaseChange pro f).op.obj W) m := by
  let b := adicStratificationModelBaseChange pro f
  let J := adicStratificationModelTopology pro Y
  let K := adicStratificationModelTopology pro X
  let α := toSheafify J
    ((Functor.const (adicStratificationModel pro Y)ᵒᵖ).obj (RingCat.of R))
  let β := toSheafify K
    ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))
  let N := (SheafOfModules.strictPerfectConstantPresheaf
    (C := adicStratificationModel pro X) R).obj M
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1} β).unit.app N
  let G := (SheafOfModules.strictPerfectConstantSheaf K R).obj M
  let H := (SheafOfModules.pushforward.{u + 1} (adicStratificationRho pro R f)).obj G
  let h : (SheafOfModules.strictPerfectConstantPresheaf
      (C := adicStratificationModel pro Y) R).obj M ⟶
      (PresheafOfModules.restrictScalars α).obj H.val :=
    { app W := ModuleCat.ofHom (X := M)
        (Y := ((PresheafOfModules.restrictScalars α).obj H.val).obj W)
        (show M →ₗ[R] (((PresheafOfModules.restrictScalars α).obj H.val).obj W) from
        { toFun := fun m ↦ η.app (b.op.obj W) m
          map_add' := fun m n ↦ map_add (η.app (b.op.obj W)).hom m n
          map_smul' := by
            intro r m
            change η.app (b.op.obj W) (r • m) =
              @SMul.smul
                (((constantSheaf K RingCat.{u + 1}).obj (RingCat.of R)).obj.obj (b.op.obj W))
                (G.val.obj (b.op.obj W)) inferInstance
                ((adicStratificationRho pro R f).hom.app W (α.app W r))
                (η.app (b.op.obj W) m)
            have hr := ConcreteCategory.congr_hom
              (adicStratificationRho_constants pro R f W) r
            change (adicStratificationRho pro R f).hom.app W (α.app W r) =
              β.app (b.op.obj W) r at hr
            erw [hr]
            exact (η.app (b.op.obj W)).hom.map_smul r m })
      naturality := by
        intro W V a
        ext m
        exact PresheafOfModules.naturality_apply η (b.op.map a) m }
  let aj := PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1} α
  let af := SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)
  let c := (af.homEquiv ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) G).symm
    ((aj.homEquiv ((SheafOfModules.strictPerfectConstantPresheaf R).obj M) H).symm h)
  have hc : aj.homEquiv ((SheafOfModules.strictPerfectConstantPresheaf R).obj M) H
      (af.homEquiv ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) G c) = h := by
    simp only [c, Equiv.apply_symm_apply]
  have happ (d : (adicStratificationPullback pro R f).obj
      ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) ⟶ G)
      (W : (adicStratificationModel pro Y)ᵒᵖ) (m : M) :
      (aj.homEquiv ((SheafOfModules.strictPerfectConstantPresheaf R).obj M) H
        (af.homEquiv ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) G d)).app W m =
        (af.homEquiv ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) G d).val.app W
          (adicStratificationConstantSection pro R Y M W m) := by
    rfl
  refine ⟨c, ?_, ?_⟩
  · intro W m
    have hx := congrArg (fun k ↦ k.app W m) hc
    rw [happ] at hx
    exact hx
  · intro c' hc' 
    apply (af.homEquiv ((SheafOfModules.strictPerfectConstantSheaf J R).obj M) G).injective
    apply (aj.homEquiv ((SheafOfModules.strictPerfectConstantPresheaf R).obj M) H).injective
    trans h
    · ext W m
      rw [happ]
      exact hc' W m
    · exact hc.symm

/-- The map determined uniquely by its constant sections, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationConstantMap (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ModuleCat.{u + 1} R) :=
  Classical.choose (adicStratificationConstantMap_existsUnique pro R f M).exists

/-- Evaluation at a terminal object classifies maps from constant module presheaves.
The inverse restricts a linear map along the unique arrows to that terminal object. -/
private def adicStratificationConstantHomEquiv {C : Type v} [SmallCategory C]
    (R : Type v) [CommRing R] (T : C) (hT : IsTerminal T)
    (M : ModuleCat.{v} R)
    (N : PresheafOfModules.{v} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) :
    ((SheafOfModules.strictPerfectConstantPresheaf (C := C) R).obj M ⟶ N) ≃
      (M ⟶ N.obj (op T)) where
  toFun f := f.app (op T)
  invFun g :=
    { app W := g ≫ N.map (hT.from W.unop).op
      naturality := by
        intro W V a
        ext m
        change N.map (hT.from V.unop).op (g m) =
          N.map a (N.map (hT.from W.unop).op (g m))
        rw [← N.map_comp_apply]
        have h : hT.from V.unop = a.unop ≫ hT.from W.unop := hT.hom_ext _ _
        rw [h]
        rfl }
  left_inv f := by
    ext W m
    exact (PresheafOfModules.naturality_apply f (hT.from W.unop).op m).symm
  right_inv g := by
    ext m
    change N.map (hT.from T).op (g m) = g m
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    rw [h]
    exact ConcreteCategory.congr_hom (N.map_id _) (g m)

set_option backward.isDefEq.respectTransparency false in
/-- Constant-module inverse image is invertible, Stacks 093R and proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: on underlying sets the comparison is the inverse image of the coproduct of
terminal sheaves indexed by M, identified with the same coproduct on the target site.
The canonical coefficient comparison transports the module structure. The comparison
and its inverse preserve addition and scalar multiplication, as checked on constants
and then locally. This proves invertibility without assuming M finitely presented. -/
theorem adicStratificationConstantMap_isIso
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} R) : IsIso (adicStratificationConstantMap pro R f M) := by
  let b := adicStratificationModelBaseChange pro f
  have : HasTerminal (adicStratificationSite pro Y) := by
    cases pro
    · exact inferInstanceAs (HasTerminal Y.Etale)
    · exact inferInstanceAs (HasTerminal Y.ProEt)
  have : HasTerminal (adicStratificationModel pro Y) := inferInstance
  have : PreservesFiniteLimits (adicStratificationBaseChange pro f) := by
    cases pro
    · exact inferInstanceAs
        (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
    · exact proEtaleBaseChange_preservesFiniteLimits f
  have : PreservesFiniteLimits
      (AsSmall.down : adicStratificationModel pro Y ⥤ adicStratificationSite pro Y) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro Y)).inverse)
  have : PreservesFiniteLimits
      (AsSmall.up : adicStratificationSite pro X ⥤ adicStratificationModel pro X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro X)).functor)
  have : PreservesFiniteLimits b :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.down ⋙ adicStratificationBaseChange pro f ⋙ AsSmall.up))
  let T := ⊤_ (adicStratificationModel pro Y)
  let hT : IsTerminal T := terminalIsTerminal
  let hBT : IsTerminal (b.obj T) := hT.isTerminalObj b T
  let J := adicStratificationModelTopology pro Y
  let K := adicStratificationModelTopology pro X
  let α := toSheafify J
    ((Functor.const (adicStratificationModel pro Y)ᵒᵖ).obj (RingCat.of R))
  let β := toSheafify K
    ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))
  let A := (SheafOfModules.strictPerfectConstantSheaf J R).obj M
  let B := (SheafOfModules.strictPerfectConstantSheaf K R).obj M
  let aj := PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1} α
  let ak := PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1} β
  let af := SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)
  let c := adicStratificationConstantMap pro R f M
  apply isIso_of_coyoneda_map_bijective c
  intro N
  let eS := (af.homEquiv A N).trans ((aj.homEquiv _ _).trans
    (adicStratificationConstantHomEquiv R T hT M _))
  let eT := (ak.homEquiv _ N).trans (adicStratificationConstantHomEquiv R (b.obj T) hBT M _)
  have hβ : (β.app (op (b.obj T))).hom =
      ((adicStratificationRho pro R f).hom.app (op T)).hom.comp (α.app (op T)).hom := by
    exact congrArg RingCat.Hom.hom (adicStratificationRho_constants pro R f (op T)).symm
  let eN := ModuleCat.restrictScalarsComp'App (α.app (op T)).hom
    ((adicStratificationRho pro R f).hom.app (op T)).hom
    (β.app (op (b.obj T))).hom hβ (N.val.obj (op (b.obj T)))
  have hcompat (x : B ⟶ N) : eS (c ≫ x) = eT x ≫ eN.hom := by
    change (adicStratificationConstantHomEquiv R T hT M _)
      (aj.homEquiv _ _ (af.homEquiv A N (c ≫ x))) = _
    rw [af.homEquiv_naturality_right, aj.homEquiv_naturality_right]
    ext m
    change x.val.app (op (b.obj T))
      ((af.homEquiv _ _ c).val.app (op T)
        (adicStratificationConstantSection pro R Y M (op T) m)) =
      x.val.app (op (b.obj T))
        (adicStratificationConstantSection pro R X M (op (b.obj T)) m)
    exact congrArg (fun n ↦ x.val.app (op (b.obj T)) n)
      (Classical.choose_spec (adicStratificationConstantMap_existsUnique pro R f M).exists
        (op T) m)
  constructor
  · intro x y h
    apply eT.injective
    apply (cancel_mono eN.hom).mp
    rw [← hcompat, ← hcompat]
    exact congrArg eS h
  · intro y
    refine ⟨eT.symm (eS y ≫ eN.inv), ?_⟩
    apply eS.injective
    rw [hcompat, Equiv.apply_symm_apply, Category.assoc, eN.inv_hom_id]
    exact Category.comp_id _


/-- Pasting of the original base-change functors, Stacks fibre-product universal property.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationBaseChangeComp (pro : Bool) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationBaseChange pro (f ≫ g) ≅
      adicStratificationBaseChange pro g ⋙ adicStratificationBaseChange pro f :=
  match pro with
  | false => MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g
  | true => MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g

/-- The same fibre-product pasting on the small models, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationModelBaseChangeComp (pro : Bool) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationModelBaseChange pro (f ≫ g) ≅
      adicStratificationModelBaseChange pro g ⋙ adicStratificationModelBaseChange pro f :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (adicStratificationBaseChangeComp pro f g) AsSmall.up)

/-- Module direct image with the specified scalar action, Stacks 03D1 and 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
abbrev adicStratificationPushforward (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (adicStratificationRho pro R f)

/-- The uniquely specified sectionwise direct-image composition, Stacks 093R, proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: pullback pasting identifies the two evaluation objects. Restrict sections along
that canonical isomorphism. Naturality gives a map of sheaves, and its inverse comes from
inverse pasting. The rho maps agree on constants, hence on all scalar sections locally;
the comparison is therefore linear. A sheaf map is determined by its section maps,
which proves uniqueness. -/
theorem adicStratificationPushforwardComp_existsUnique
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : adicStratificationPushforward pro R f ⋙ adicStratificationPushforward pro R g ≅
        adicStratificationPushforward pro R (f ≫ g),
      ∀ (G : adicStratificationModules pro X R)
        (W : (adicStratificationModel pro Z)ᵒᵖ)
        (x : G.val.obj ((adicStratificationModelBaseChange pro f).op.obj
          ((adicStratificationModelBaseChange pro g).op.obj W))),
        ((e.hom.app G).val.app W) x = G.val.map
          ((adicStratificationModelBaseChangeComp pro f g).hom.app W.unop).op x := by
  let bf := adicStratificationModelBaseChange pro f
  let bg := adicStratificationModelBaseChange pro g
  let J := adicStratificationModelTopology pro Z
  let K := adicStratificationModelTopology pro Y
  let H := adicStratificationModelTopology pro X
  let A := (constantSheaf H RingCat.{u + 1}).obj (RingCat.of R)
  let i := adicStratificationModelBaseChangeComp pro f g
  have : (bg ⋙ bf).IsContinuous J H := Functor.isContinuous_comp bg bf J K H
  let q : (constantSheaf J RingCat.{u + 1}).obj (RingCat.of R) ⟶
      ((bg ⋙ bf).sheafPushforwardContinuous RingCat.{u + 1} J H).obj A :=
    adicStratificationRho pro R g ≫
    (bg.sheafPushforwardContinuous RingCat.{u + 1} J K).map
      (adicStratificationRho pro R f)
  have : (bg ⋙ bf).IsContinuous J H := Functor.isContinuous_comp bg bf J K H
  have hq : q ≫
      (Functor.sheafPushforwardContinuousNatTrans i.hom RingCat.{u + 1} J H).app A =
        adicStratificationRho pro R (f ≫ g) := by
    apply ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _
      (((adicStratificationModelBaseChange pro (f ≫ g)).sheafPushforwardContinuous
        RingCat.{u + 1} J H).obj A)).injective
    change toSheafify J _ ≫ _ = toSheafify J _ ≫ _
    ext W : 2
    change (toSheafify J
      ((Functor.const (adicStratificationModel pro Z)ᵒᵖ).obj (RingCat.of R))).app W ≫
        ((adicStratificationRho pro R g).hom.app W ≫
          (adicStratificationRho pro R f).hom.app (bg.op.obj W)) ≫
            A.obj.map (i.hom.app W.unop).op =
      (toSheafify J
        ((Functor.const (adicStratificationModel pro Z)ᵒᵖ).obj (RingCat.of R))).app W ≫
          (adicStratificationRho pro R (f ≫ g)).hom.app W
    rw [← Category.assoc, ← Category.assoc,
      adicStratificationRho_constants pro R g W,
      adicStratificationRho_constants pro R f (bg.op.obj W),
      adicStratificationRho_constants pro R (f ≫ g) W]
    have hn := (toSheafify H
      ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R))).naturality
        (i.hom.app W.unop).op
    change 𝟙 (RingCat.of R) ≫ _ = _ at hn
    rw [Category.id_comp] at hn
    exact hn.symm
  let e : adicStratificationPushforward pro R f ⋙ adicStratificationPushforward pro R g ≅
      adicStratificationPushforward pro R (f ≫ g) :=
    SheafOfModules.pushforwardComp (adicStratificationRho pro R g)
      (adicStratificationRho pro R f) ≪≫ SheafOfModules.pushforwardCongr₂
        (F := adicStratificationModelBaseChange pro (f ≫ g)) (G := bg ⋙ bf)
        (S := A) q i hq
  refine ⟨e, ?_, ?_⟩
  · intro G W x
    rfl
  · intro e' he'
    apply Iso.ext
    ext G W x
    exact (he' G W x).trans (by rfl)

/-- Canonical direct-image pasting, uniquely determined on sections, Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationPushforwardComp (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Classical.choose (adicStratificationPushforwardComp_existsUnique pro R f g).exists

/-- The inverse-image composition isomorphism, defined as the adjunction mate of the
specified sectionwise direct-image pasting, Stacks 093R and proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationPullbackComp (pro : Bool) (R : Type (u + 1)) [CommRing R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    adicStratificationPullback pro R (f ≫ g) ≅
      adicStratificationPullback pro R g ⋙ adicStratificationPullback pro R f :=
  ((conjugateIsoEquiv
    (SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R (f ≫ g)))
    ((SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R g)).comp
      (SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)))).symm
        (adicStratificationPushforwardComp pro R f g).symm).symm

/-- Constant sections commute with the specified inverse-image composition,
Stacks 0H7J and 093R, proof Step 7.
(blueprint: lem-sfb-adic-finite-stratification-pullback).
Proof: take adjuncts under the composite module adjunction. Both sides send the
constant generator m to the same constant section m on the iterated fibre product;
the specified pasting identifies that section with the direct pullback section.
Equality follows from the defining uniqueness of the constant-module comparison.
The coefficient maps agree by the identical argument with scalars. -/
theorem adicStratificationConstantMap_comp
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : ModuleCat.{u + 1} R) :
    adicStratificationConstantMap pro R (f ≫ g) M =
      (adicStratificationPullbackComp pro R f g).hom.app
          ((SheafOfModules.strictPerfectConstantSheaf
            (adicStratificationModelTopology pro Z) R).obj M) ≫
        (adicStratificationPullback pro R f).map (adicStratificationConstantMap pro R g M) ≫
          adicStratificationConstantMap pro R f M := by
  let af := SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R f)
  let ag := SheafOfModules.pullbackPushforwardAdjunction (adicStratificationRho pro R g)
  let ad := SheafOfModules.pullbackPushforwardAdjunction
    (adicStratificationRho pro R (f ≫ g))
  let ac := ag.comp af
  let e := adicStratificationPushforwardComp pro R f g
  let b := adicStratificationPullbackComp pro R f g
  let A := (SheafOfModules.strictPerfectConstantSheaf
    (adicStratificationModelTopology pro Z) R).obj M
  let B := (SheafOfModules.strictPerfectConstantSheaf
    (adicStratificationModelTopology pro Y) R).obj M
  let C := (SheafOfModules.strictPerfectConstantSheaf
    (adicStratificationModelTopology pro X) R).obj M
  let cg := adicStratificationConstantMap pro R g M
  let cf := adicStratificationConstantMap pro R f M
  have hm (k : (adicStratificationPullback pro R g ⋙
      adicStratificationPullback pro R f).obj A ⟶ C) :
      ad.homEquiv A C (b.hom.app A ≫ k) = ac.homEquiv A C k ≫ e.hom.app C := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
    rw [← Category.assoc]
    have hu := unit_conjugateEquiv_symm ac ad e.hom A
    change ac.unit.app A ≫ e.hom.app _ = ad.unit.app A ≫
      (adicStratificationPushforward pro R (f ≫ g)).map (b.hom.app A) at hu
    rw [← hu, Category.assoc, ← e.hom.naturality k, ← Category.assoc]
  apply (adicStratificationConstantMap_existsUnique pro R (f ≫ g) M).unique
    (Classical.choose_spec (adicStratificationConstantMap_existsUnique pro R (f ≫ g) M).exists)
  intro W m
  have hk : ad.homEquiv A C
      (b.hom.app A ≫ (adicStratificationPullback pro R f).map cg ≫ cf) =
      (ag.homEquiv A B cg) ≫
        (adicStratificationPushforward pro R g).map (af.homEquiv B C cf) ≫ e.hom.app C := by
    rw [hm, Adjunction.comp_homEquiv]
    change ag.homEquiv _ _ (af.homEquiv _ _
      ((adicStratificationPullback pro R f).map cg ≫ cf)) ≫ e.hom.app C = _
    rw [af.homEquiv_naturality_left, ag.homEquiv_naturality_right, Category.assoc]
  rw [hk]
  change (e.hom.app C).val.app W
    ((af.homEquiv B C cf).val.app ((adicStratificationModelBaseChange pro g).op.obj W)
      ((ag.homEquiv A B cg).val.app W (adicStratificationConstantSection pro R Z M W m))) = _
  have hg : (ag.homEquiv A B cg).val.app W
      (adicStratificationConstantSection pro R Z M W m) =
      adicStratificationConstantSection pro R Y M
        ((adicStratificationModelBaseChange pro g).op.obj W) m :=
    Classical.choose_spec (adicStratificationConstantMap_existsUnique pro R g M).exists W m
  have hf : (af.homEquiv B C cf).val.app
      ((adicStratificationModelBaseChange pro g).op.obj W)
      (adicStratificationConstantSection pro R Y M
        ((adicStratificationModelBaseChange pro g).op.obj W) m) =
      adicStratificationConstantSection pro R X M
        ((adicStratificationModelBaseChange pro f).op.obj
          ((adicStratificationModelBaseChange pro g).op.obj W)) m :=
    Classical.choose_spec (adicStratificationConstantMap_existsUnique pro R f M).exists _ m
  erw [hg, hf]
  erw [Classical.choose_spec
    (adicStratificationPushforwardComp_existsUnique pro R f g).exists]
  exact PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction.{u + 1, u + 1, u + 1, u + 1}
      (toSheafify (adicStratificationModelTopology pro X)
        ((Functor.const (adicStratificationModel pro X)ᵒᵖ).obj (RingCat.of R)))).unit.app
          ((SheafOfModules.strictPerfectConstantPresheaf
            (C := adicStratificationModel pro X) R).obj M))
      ((adicStratificationModelBaseChangeComp pro f g).hom.app W.unop).op m |>.symm

/-- The canonical comparison along a projection whose composite is the stratum map,
Stacks 093R, proof Steps 4 and 7. Equality transport is followed by the adjunction mate.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def adicStratificationProjectionComparison
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S X : Scheme.{u}}
    (h : T ⟶ S) (a : S ⟶ X) (q : T ⟶ X) (w : h ≫ a = q)
    (F : adicStratificationModules pro X R) :
    (adicStratificationPullback pro R q).obj F ≅
      (adicStratificationPullback pro R h).obj ((adicStratificationPullback pro R a).obj F) :=
  eqToIso (congrArg (fun k ↦ (adicStratificationPullback pro R k).obj F) w.symm) ≪≫
    (adicStratificationPullbackComp pro R h a).app F

/-- The exact normalization of a pulled-back chosen local trivialization, Stacks 093R.
It says that the local isomorphism agrees, on the inverse-image adjunction unit, with
the given trivialization followed by the canonical constant-module comparison. This
characterizes the localization comparison, including its coefficient identifications.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def AdicStratificationTrivializationCompatibility
    (pro : Bool) (R : Type (u + 1)) [CommRing R] {T S : Scheme.{u}}
    (h : T ⟶ S) (G : adicStratificationModules pro S R)
    (P : adicStratificationModules pro T R)
    (b : P ≅ (adicStratificationPullback pro R h).obj G)
    (V : adicStratificationModel pro S) (M : ModuleCat.{u + 1} R)
    (e : G.over V ≅ ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M).over V) : Prop :=
  SheafOfModules.NormalizedLocalModuleTrivialization
    (adicStratificationModelTopology pro S) (adicStratificationModelTopology pro T)
    (adicStratificationModelBaseChange pro h) (adicStratificationRho pro R h)
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro S) R).obj M) G
    ((SheafOfModules.strictPerfectConstantSheaf
      (adicStratificationModelTopology pro T) R).obj M) P
    (adicStratificationConstantMap pro R h M) b V e

/-- The hypotheses of the common-strata lemma, bundled without choosing any new sheaves.
Every cover member has its given constructible locally closed scheme stratification.
Source: Stacks 093R and finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
structure AdicStratificationInput (pro : Bool) (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) (r : ℕ) where
  /-- The finite family of constant-ring module sheaves. -/
  sheaf : Fin r → adicStratificationModules pro X R
  /-- An unrestricted index set for each given open cover. -/
  coverIndex : Fin r → Type v
  /-- The given open subsets. -/
  opens : ∀ j : Fin r, coverIndex j → X.Opens
  /-- Each family is an open covering, including empty covers of the empty scheme. -/
  covers : ∀ j : Fin r, ⨆ a, opens j a = ⊤
  /-- The given finite constructible locally closed scheme stratifications. -/
  strata : ∀ (j : Fin r) (a : coverIndex j), Stratification (opens j a).toScheme
  /-- The input restrictions are locally constant of finite type over the same ring. -/
  locallyConstant : ∀ (j : Fin r) (a : coverIndex j) (k : Fin (strata j a).n),
    SheafOfModules.IsFiniteTypeLocallyConstant
      (adicStratificationModelTopology pro ((strata j a).domain k)) R
      ((adicStratificationPullback pro R ((strata j a).immersion k ≫ (opens j a).ι)).obj
        (sheaf j))

namespace AdicStratificationInput

variable {pro : Bool} {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}} {r : ℕ}
  (D : AdicStratificationInput.{u, v} pro R X r)

/-- The common open members are exactly all finite intersections of input members.
Source: finite-reductions Step 6 and Stacks 093R.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def commonOpen (p : ∀ j : Fin r, D.coverIndex j) : X.Opens :=
  ⨅ j : Fin r, D.opens j (p j)

/-- The finite fibre-product factors: the common open and one original input stratum
for each sheaf, all mapped to X. Its limit is equivalently the product over U of the
strata restricted to U. Source: Stacks fibre products, finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def productFactors (p : ∀ j : Fin r, D.coverIndex j)
    (a : ∀ j : Fin r, Fin (D.strata j (p j)).n) : Option (Fin r) → Scheme.{u}
  | none => (D.commonOpen p).toScheme
  | some j => (D.strata j (p j)).domain (a j)

/-- The factor maps used by the universal property, Stacks fibre products.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
def productArrows (p : ∀ j : Fin r, D.coverIndex j)
    (a : ∀ j : Fin r, Fin (D.strata j (p j)).n) :
    ∀ t : Option (Fin r), D.productFactors p a t ⟶ X
  | none => (D.commonOpen p).ι
  | some j => (D.strata j (p j)).immersion (a j) ≫ (D.opens j (p j)).ι

/-- A finite common stratification with actual product projections and every chosen
trivialization transported canonically with its unchanged module model.
Source: Stacks 093R and the eight proof steps of the common-strata lemma.
(blueprint: lem-sfb-adic-finite-stratification-pullback). -/
structure CommonRefinement (p : ∀ j : Fin r, D.coverIndex j) where
  /-- A finite constructible locally closed scheme partition of the intersection U. -/
  strata : Stratification (D.commonOpen p).toScheme
  /-- One original stratum for each input partition and each refined stratum. -/
  factor : Fin strata.n → ∀ j : Fin r, Fin (D.strata j (p j)).n
  /-- All the actual projections, including the map to U. -/
  cone : ∀ k : Fin strata.n, WidePullbackCone (D.productArrows p (factor k))
  /-- The cone's scheme is the refined stratum itself. -/
  point : ∀ k : Fin strata.n, (cone k).pt = strata.domain k
  /-- The projection to U is precisely the stratum immersion. -/
  toOpen : ∀ k : Fin strata.n,
    (eqToHom (point k).symm ≫ (cone k).π none) = strata.immersion k
  /-- The actual universal property of the finite fibre product, including projections. -/
  isLimit : ∀ k : Fin strata.n, IsLimit (cone k)
  /-- Discard the empty products when the input family is nonempty. -/
  nonempty : r ≠ 0 → ∀ k : Fin strata.n, Nonempty (strata.domain k)
  /-- For the empty input family retain the identity one-stratum partition, even if X is empty. -/
  emptyFamily : r = 0 → strata.n = 1 ∧ ∀ k : Fin strata.n, IsIso (strata.immersion k)
  /-- The actual projections to the original strata. -/
  projection : ∀ (k : Fin strata.n) (j : Fin r),
    strata.domain k ⟶ (D.strata j (p j)).domain (factor k j)
  /-- These projections are those of the limiting fibre-product cone. -/
  projection_eq : ∀ (k : Fin strata.n) (j : Fin r),
    projection k j = eqToHom (point k).symm ≫ (cone k).π (some j)
  /-- Projection followed by the original stratum map is the common stratum map to X. -/
  projection_comp : ∀ (k : Fin strata.n) (j : Fin r),
    projection k j ≫ ((D.strata j (p j)).immersion (factor k j) ≫
      (D.opens j (p j)).ι) = strata.immersion k ≫ (D.commonOpen p).ι
  /-- Every restriction on the common strata is locally constant of finite type. -/
  locallyConstant : ∀ (k : Fin strata.n) (j : Fin r),
    SheafOfModules.IsFiniteTypeLocallyConstant
      (adicStratificationModelTopology pro (strata.domain k)) R
      ((adicStratificationPullback pro R (strata.immersion k ≫ (D.commonOpen p).ι)).obj
        (D.sheaf j))
  /-- Every chosen covering sieve pulls back to the actual base-changed covering. -/
  coverings : ∀ (k : Fin strata.n) (j : Fin r)
    (W : adicStratificationModel pro ((D.strata j (p j)).domain (factor k j)))
    (S : Sieve W), S ∈ adicStratificationModelTopology pro _ W →
      S.functorPushforward (adicStratificationModelBaseChange pro (projection k j)) ∈
        adicStratificationModelTopology pro (strata.domain k)
          ((adicStratificationModelBaseChange pro (projection k j)).obj W)
  /-- Every chosen local trivialization pulls back with exactly the same finite module;
  the equation in the predicate fixes its constant-ring and composition identifications. -/
  trivializations : ∀ (k : Fin strata.n) (j : Fin r)
    (V : adicStratificationModel pro ((D.strata j (p j)).domain (factor k j)))
    (M : ModuleCat.{u + 1} R), Module.Finite R M →
    ∀ e : (((adicStratificationPullback pro R
      ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)).obj
        (D.sheaf j)).over V) ≅
      ((SheafOfModules.strictPerfectConstantSheaf
        (adicStratificationModelTopology pro ((D.strata j (p j)).domain (factor k j))) R).obj
          M).over V,
      AdicStratificationTrivializationCompatibility pro R (projection k j)
        ((adicStratificationPullback pro R
          ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)).obj (D.sheaf j))
        ((adicStratificationPullback pro R (strata.immersion k ≫ (D.commonOpen p).ι)).obj
          (D.sheaf j))
        (adicStratificationProjectionComparison pro R (projection k j)
          ((D.strata j (p j)).immersion (factor k j) ≫ (D.opens j (p j)).ι)
          (strata.immersion k ≫ (D.commonOpen p).ι) (projection_comp k j) (D.sheaf j)) V M e

end AdicStratificationInput


private instance adicModelHasFiniteLimits (pro : Bool) (X : Scheme.{u}) :
    HasFiniteLimits (adicStratificationModel pro X) := by
  have : HasFiniteLimits (adicStratificationSite pro X) := by
    cases pro
    · exact inferInstanceAs (HasFiniteLimits X.Etale)
    · exact inferInstanceAs (HasFiniteLimits X.ProEt)
  infer_instance

private instance adicModelBaseChangePreservesFiniteLimits (pro : Bool)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (adicStratificationModelBaseChange pro f) := by
  have : PreservesFiniteLimits (adicStratificationBaseChange pro f) := by
    cases pro
    · exact inferInstanceAs
        (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
    · exact proEtaleBaseChange_preservesFiniteLimits f
  have : PreservesFiniteLimits
      (AsSmall.down : adicStratificationModel pro Y ⥤ adicStratificationSite pro Y) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro Y)).inverse)
  have : PreservesFiniteLimits
      (AsSmall.up : adicStratificationSite pro X ⥤ adicStratificationModel pro X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv (C := adicStratificationSite pro X)).functor)
  exact inferInstanceAs (PreservesFiniteLimits
    (AsSmall.down ⋙ adicStratificationBaseChange pro f ⋙ AsSmall.up))

set_option maxHeartbeats 100000 in
-- The dependent refinement checks the scalar restrictions on all its projection maps.
/-- Finite families have common finite constructible stratifications on exactly the
intersection cover, with actual finite fibre products and canonical transport of every
chosen local trivialization over an arbitrary coefficient ring, on either site.
Source: Stacks 093R; finite-reductions Step 6.
(blueprint: lem-sfb-adic-finite-stratification-pullback).

Proof:
1. For r=0 use X and its identity stratum, including X empty. For r>0 the intersections
of members of the finitely many given open covers cover X, by choosing a member through
each point for each input cover.
2. Restrict each input stratification to an intersection U by scheme fibre products
(lemma-constructible-pullback-stratification). Images are constructible by
lem-pur-scheme-constructible-preimage, without any quasi-compactness hypothesis on U.
3. Inductively pull back the next partition to each current stratum. Composition of
immersions is an immersion (lem-weil-pbc-proper-fp-permanence). Its image is the
intersection of the two images, since immersions are injective on underlying points.
The resulting finite partition is disjoint and covers U.
4. Finite intersections remain constructible. Remove empty products when r>0; the
fibre-product universal property gives all actual projection maps and their equations.
5. The coefficient comparison is adjoint to constant sections. It is invertible by
lem-pe-constant-left-module-inverse-image, and agrees with the specified scalar map
because both adjuncts fix constants. Etale inverse image uses its algebraic-structure
lift; pro-etale inverse image uses the recorded geometric inverse image.
6. Pull each chosen covering back along each actual projection. Etale covering base
change and weakly etale/fpqc base change prove it is a covering on the chosen site.
Localize the ringed-site morphism (lem-weil-pbc-localize-ringed-site-morphism) and
apply lem-sfb-geometric-inverse-image-constant-module to the given trivialization.
Its model is the same R-module M with the same finite generating list.
7. The constant comparison is fixed on every generator m. Direct comparison and
two successive comparisons therefore agree under the canonical composition mate.
The normalization equation in AdicStratificationTrivializationCompatibility expresses
exactly this compatibility, with uniqueness by the localized module adjunction.
8. Apply these constructions to all strata and sheaves. The covering-sieve definition
of IsFiniteTypeLocallyConstant gives the asserted common locally constant restrictions.
Neither R nor its underlying set needs to be finite, and no Noetherian assumption enters.
-/
theorem adic_finite_stratification_pullback
    (pro : Bool) (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) (r : ℕ)
    (D : AdicStratificationInput.{u, v} pro R X r) :
    (⨆ p : (∀ j : Fin r, D.coverIndex j), D.commonOpen p) = ⊤ ∧
      ∀ p : (∀ j : Fin r, D.coverIndex j), Nonempty (D.CommonRefinement p) := by
  classical
  constructor
  · apply top_unique
    intro x hx
    have h (j : Fin r) : ∃ a, x ∈ D.opens j a := by
      apply TopologicalSpace.Opens.mem_iSup.mp
      rw [D.covers j]
      trivial
    choose a ha using h
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨a, ?_⟩
    change x ∈ ((⨅ j, D.opens j (a j) : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr ha
  · intro p
    obtain ⟨T, a, c, hp, hto, hl, hn, he⟩ := finite_stratification_wide_pullback r
      (D.commonOpen p) (fun j ↦ D.opens j (p j)) (fun j ↦ D.strata j (p j))
        (fun j ↦ iInf_le (fun j ↦ D.opens j (p j)) j)
    let h (k : Fin T.n) (j : Fin r) :
        T.domain k ⟶ (D.strata j (p j)).domain (a k j) :=
      eqToHom (hp k).symm ≫ (c k).π (some j)
    have hw (k : Fin T.n) (j : Fin r) :
        h k j ≫ ((D.strata j (p j)).immersion (a k j) ≫ (D.opens j (p j)).ι) =
          T.immersion k ≫ (D.commonOpen p).ι := by
      dsimp only [h]
      erw [Category.assoc, (c k).condition (some j), ← (c k).condition none,
        ← Category.assoc, hto]
      rfl
    let b (k : Fin T.n) (j : Fin r) := adicStratificationProjectionComparison pro R
      (h k j) ((D.strata j (p j)).immersion (a k j) ≫ (D.opens j (p j)).ι)
      (T.immersion k ≫ (D.commonOpen p).ι) (hw k j) (D.sheaf j)
    let cm {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : ModuleCat.{u + 1} R) :=
      @asIso _ _ _ _ (adicStratificationConstantMap pro R f M)
        (adicStratificationConstantMap_isIso pro R f M)
    refine ⟨{ strata := T, factor := a, cone := c, point := hp, toOpen := hto
              isLimit := fun k ↦ (hl k).some
              nonempty := hn, emptyFamily := he, projection := h
              projection_eq := fun _ _ ↦ rfl, projection_comp := hw
              locallyConstant := ?_, coverings := ?_, trivializations := ?_ }⟩
    · intro k j
      exact SheafOfModules.finite_type_constant_module_pullback
        (adicStratificationModelTopology pro _) (adicStratificationModelTopology pro _)
        (adicStratificationModelBaseChange pro (h k j))
        (CoverPreserving.of_isContinuous _ _ _) R (adicStratificationRho pro R (h k j))
        (cm (h k j)) _ _ (b k j) (D.locallyConstant j (p j) (a k j))
    · intro k j W S hS
      exact (CoverPreserving.of_isContinuous (adicStratificationModelBaseChange pro (h k j))
        _ _).cover_preserve hS
    · intro k j V M _ e
      exact SheafOfModules.normalized_local_module_pullback
        (adicStratificationModelTopology pro _) (adicStratificationModelTopology pro _)
        (adicStratificationModelBaseChange pro (h k j)) (adicStratificationRho pro R (h k j))
        _ _ _ _ (cm (h k j) M) (b k j) V e

end AlgebraicGeometry.Scheme
