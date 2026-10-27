/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.CategoryTheory.RingedToposMorphism
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The big fppf ringed comparison of an algebraic space

Source: Stacks Project, More on Cohomology of Spaces, section Comparing fppf and
étale topologies: modules, Tag 0DGN(1),(3)
(blueprint: def-sfb-space-fppf-ringed-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A chosen small presentation of the big fppf site, including all spaces in the
fixed bound up to isomorphism. Coverings are exactly the chartwise fppf families.
Source: Stacks, section-fppf-etale-modules and Tag 03Y8
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
structure SpaceFppfSite (W : AlgebraicSpace S) where
  C : Type (u + 1)
  [category : SmallCategory C]
  inclusion : C ⥤ Over W
  fullyFaithful : inclusion.FullyFaithful
  essSurj : inclusion.EssSurj
  precoverage : Precoverage C
  coverings_iff (T : C) (R : Presieve T) :
    R ∈ precoverage T ↔
      IsFppfCover (fun a : R.uncurry ↦ (inclusion.map a.1.2).left)
  etaleInclusion : W.EtaleSite ⥤ C
  etaleIso : etaleInclusion ⋙ inclusion ≅
    enlargedSchemeInclusion W ⋙ ObjectProperty.ι _

attribute [instance] SpaceFppfSite.category

/-- The big fppf topology in the chosen small presentation.
Source: Stacks, Tag 03Y8 (blueprint: def-sfb-space-fppf-ringed-comparison). -/
abbrev SpaceFppfSite.topology {W : AlgebraicSpace S} (B : SpaceFppfSite W) :=
  B.precoverage.toGrothendieck

/-- Compatible regular functions on every small étale chart of a space.
This is the usual global-section type of the existing structure sheaf.
Source: Stacks, Tags 03H7 and 0DGN
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
abbrev spaceRegularSections (V : AlgebraicSpace S) :=
  (V.structureSheaf.obj ⋙ forget RingCat).sections

/-- A normalized ring sheaf on the big site. The displayed bijections specify its
sections as compatible regular functions, including every ring operation and restriction.
The restriction formula is tested on ALL commuting scheme charts, hence determines
restriction uniquely by étale descent. Its small-étale restriction is the existing ring.
Source: Stacks, section-fppf-etale-modules, Tag 0DGN
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
structure SpaceFppfRings {W : AlgebraicSpace S} (B : SpaceFppfSite W) where
  rings : Sheaf B.topology RingCat.{u + 1}
  sections (T : B.C) : rings.obj.obj (op T) ≃
    spaceRegularSections (B.inclusion.obj T).left
  zero (T : B.C) (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T 0).val (op A) = 0
  one (T : B.C) (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T 1).val (op A) = 1
  add (T : B.C) (r s : rings.obj.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T (r + s)).val (op A) =
      (sections T r).val (op A) + (sections T s).val (op A)
  mul (T : B.C) (r s : rings.obj.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T (r * s)).val (op A) =
      (sections T r).val (op A) * (sections T s).val (op A)
  restriction {V T : B.C} (h : V ⟶ T) (r : rings.obj.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite)
      (q : ModuleChart (B.inclusion.map h).left A) :
    (sections V (rings.obj.map h.op r)).val (op q.left) =
      moduleChartScalar (B.inclusion.map h).left A q ((sections T r).val (op A))
  continuous : B.etaleInclusion.IsContinuous W.etaleTopology B.topology
  smallRings : Sheaf W.etaleTopology RingCat.{u + 1}
  smallSections (A : W.EtaleSite) : smallRings.obj.obj (op A) ≃+*
    ULift.{u + 1} (W.structureSheaf.obj.obj (op A))
  smallRestriction {A A' : W.EtaleSite} (h : A ⟶ A')
      (r : smallRings.obj.obj (op A')) :
    (smallSections A (smallRings.obj.map h.op r)).down =
      W.structureSheaf.obj.map h.op (smallSections A' r).down
  ringRestriction : smallRings ≅
    (@Functor.sheafPushforwardContinuous _ _ _ _ B.etaleInclusion RingCat.{u + 1} _
      W.etaleTopology B.topology continuous).obj rings
  geometric : GeometricMorphism (Sheaf B.topology (Type (u + 1)))
    (Sheaf W.etaleTopology (Type (u + 1)))
  geometric_direct : geometric.direct =
    @Functor.sheafPushforwardContinuous _ _ _ _ B.etaleInclusion (Type (u + 1)) _
      W.etaleTopology B.topology continuous
  normalization (A : W.EtaleSite) (r : smallRings.obj.obj (op A))
      (T : (B.inclusion.obj (B.etaleInclusion.obj A)).left.EtaleSite)
      (g : T.obj.left ⟶ A.obj.left)
      (hg : T.obj.hom ≫ (B.etaleIso.hom.app A).left.hom.hom = yoneda.map g) :
    (sections (B.etaleInclusion.obj A)
      (ringRestriction.hom.hom.app (op A) r)).val (op T) =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map g.left.op)
          (smallSections A r).down

/-- Module direct image is restriction with the specified structural-ring isomorphism.
Source: Stacks, section-fppf-etale-modules
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
def SpaceFppfRings.directImage {W : AlgebraicSpace S} {B : SpaceFppfSite W}
    (R : SpaceFppfRings B) :
    SheafOfModules.{u + 1} R.rings ⥤ SheafOfModules.{u + 1} R.smallRings :=
  letI := R.continuous
  SheafOfModules.pushforward R.ringRestriction.hom

/-- The section extension is normalized on all charts and restrictions. The last
identity is precisely tensor pullback of sections, followed by the canonical composition
isomorphism; the slice triangle supplies the necessary equality of structure maps.
Source: Stacks, Tag 0DGN(1),(3)
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
structure IsSpaceFppfSectionExtension {W : AlgebraicSpace S} {B : SpaceFppfSite W}
    (R : SpaceFppfRings B) (M : W.Modules) (F : SheafOfModules.{u + 1} R.rings) where
  sections (T : B.C) : F.val.obj (op T) ≃
    ((moduleTensorPullback (B.inclusion.obj T).hom).obj M).sections
  zero (T : B.C) (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T 0).val (op A) = 0
  add (T : B.C) (s t : F.val.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T (s + t)).val (op A) =
      (sections T s).val (op A) + (sections T t).val (op A)
  smul (T : B.C) (r : R.rings.obj.obj (op T)) (s : F.val.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite) :
    (sections T (r • s)).val (op A) =
      @id ((B.inclusion.obj T).left.structureSheaf.obj.obj (op A))
        ((R.sections T r).val (op A)) •
        @id (((moduleTensorPullback (B.inclusion.obj T).hom).obj M).val.obj (op A))
          ((sections T s).val (op A))
  restriction {V T : B.C} (h : V ⟶ T) (s : F.val.obj (op T))
      (A : (B.inclusion.obj T).left.EtaleSite)
      (q : ModuleChart (B.inclusion.map h).left A) :
    (eqToHom (congrArg (fun f ↦ (moduleTensorPullback f).obj M)
      (Over.w (B.inclusion.map h)).symm)).val.app (op q.left)
        ((sections V (F.val.map h.op s)).val (op q.left)) =
      ((moduleTensorComposition (B.inclusion.map h).left (B.inclusion.obj T).hom).hom.app
        M).val.app (op q.left)
          (moduleTensorSection (B.inclusion.map h).left
            ((moduleTensorPullback (B.inclusion.obj T).hom).obj M) A q 1
              ((sections T s).val (op A)))

/-- Restriction of module maps preserves their sectionwise addition.
Source: Stacks, section-fppf-etale-modules
(blueprint: def-sfb-space-fppf-ringed-comparison).
Proof: on each étale object, both sides are the sum of the same two linear maps;
the structural-ring transport changes only the scalar action, not addition. -/
@[instance] theorem SpaceFppfRings.directImage_additive {W : AlgebraicSpace S}
    {B : SpaceFppfSite W} (R : SpaceFppfRings B) : R.directImage.Additive := by
  sorry

/-- The small big-site module category has enough injectives by its Grothendieck
abelian structure. No geometric finiteness assumption is involved.
Source: Stacks, Modules on Sites, Tag 03DA; Injectives, Tag 079Q
(blueprint: def-sfb-space-fppf-ringed-comparison). -/
noncomputable instance SpaceFppfRings.enoughInjectives {W : AlgebraicSpace S}
    {B : SpaceFppfSite W} (R : SpaceFppfRings B) :
    EnoughInjectives (SheafOfModules.{u + 1} R.rings) :=
  @IsGrothendieckAbelian.enoughInjectives _ _ _
    (SheafOfModules.isGrothendieckAbelian R.rings)

end AlgebraicGeometry.AlgebraicSpace
