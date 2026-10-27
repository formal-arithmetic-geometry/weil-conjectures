/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProperSchemeDeformationData
public import Sheaf.AlgebraicGeometry.SchemeLiftClassificationData
public import Sheaf.AlgebraicGeometry.SchemeCoefficientExtensionProblems
public import Sheaf.AlgebraicGeometry.SchemeCotangentOpenRestriction
public import Sheaf.AlgebraicGeometry.ProperSchemeCoherentExtFinite
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Separation.Basic

/-! # Normalized tangent identifications for proper scheme deformation hulls

Source: Stacks Project, examples-defos.tex, Tags 0DY9, 0DYW, 0DZM and 0DYV;
Deformation Theory, Tags 0GPZ and 0GQ1
(blueprint: def-sfb-proper-scheme-tangent-data).
## Main definitions

- `dualDirectionRing`.
- `dualRingIso`.
- `dualSpecIso`.
- `IsTangentTransport`.
- `coefficientUnit`.
- `TangentExt`.
- `extModule`.
- `TangentIdentification`.
- `TangentNaturality`.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution
namespace AlgebraicGeometry.ProperSchemeDeformation
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  {k : Type u} [Field k] {X : Scheme.{u}}

/-- The ring of split directions with exactly the recorded coefficient instances.
Source: Stacks 0GPZ (blueprint: def-sfb-proper-scheme-tangent-data). -/
def dualDirectionRing (k : Type u) [Field k] : CommRingCat.{u} :=
  letI : AddCommGroup (ModuleCat.of k k) := (ModuleCat.of k k).isAddCommGroup
  letI : Module k (ModuleCat.of k k) := (ModuleCat.of k k).isModule
  letI : Module kᵐᵒᵖ (ModuleCat.of k k) :=
    SchemeDeformation.directionOppositeModule k (ModuleCat.of k k)
  letI : IsCentralScalar k (ModuleCat.of k k) :=
    SchemeDeformation.directionCentralScalar k (ModuleCat.of k k)
  CommRingCat.of (TrivSqZeroExt k (ModuleCat.of k k))

/-- Coordinate identity between the two recorded models of dual numbers. It retains
both scalar actions explicitly. Source: Stacks 06IG and 0DY9
(blueprint: def-sfb-proper-scheme-tangent-data). -/
def dualRingIso : CommRingCat.of
    (ArtinDeformation.ring (ArtinDeformation.squareZeroTest (R := k) (k := k) k)) ≅
    dualDirectionRing k :=
  @RingEquiv.toCommRingCatIso
    (ArtinDeformation.ring (ArtinDeformation.squareZeroTest (R := k) (k := k) k))
    (dualDirectionRing k) (inferInstanceAs (CommRing (ArtinDeformation.ring
      (ArtinDeformation.squareZeroTest (R := k) (k := k) k))))
    (inferInstanceAs (CommRing (dualDirectionRing k)))
    { toFun := fun a ↦ ⟨a.fst, a.snd⟩
      invFun := fun a ↦ ⟨a.fst, a.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · rfl
        · rfl
      map_add' := fun _ _ ↦ rfl }

/-- The corresponding coordinate identity of dual-number spectra. Source: Stacks 06IG
(blueprint: def-sfb-proper-scheme-tangent-data). -/
def dualSpecIso : Spec (dualDirectionRing k) ≅
    Spec (.of (ArtinDeformation.ring
      (ArtinDeformation.squareZeroTest (R := k) (k := k) k))) :=
  Scheme.Spec.mapIso (dualRingIso (k := k)).op

/-- The actual transport of tangent representatives between the recorded dual-number
models, with their markings. Source: Stacks 0DY9
(blueprint: def-sfb-proper-scheme-tangent-data). -/
structure IsTangentTransport (f : X ⟶ Spec (.of k))
    (Y : Deformation f (ArtinDeformation.squareZeroTest (R := k) (k := k) k))
    (Z : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))) where
  coordinate : Z.space ≅ Y.obj.space
  projection : coordinate.hom ≫ Y.obj.projection =
    Z.projection ≫ (dualSpecIso (k := k)).hom
  marking : Z.marking ≫ coordinate.hom = Y.obj.marking

/-- `O_X tensor_k k → O_X` is the pinned tensor pullback of the unit.
Source: Stacks 0096 (blueprint: def-sfb-proper-scheme-tangent-data). -/
def coefficientUnit (f : X ⟶ Spec (.of k)) :
    SchemeDeformation.directionModule f (ModuleCat.of k k) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  Scheme.Modules.tensorPullbackObjUnitToUnit f

/-- The target Ext-one uses the structure sheaf, not a replacement coefficient.
Source: Stacks 0DY9 (blueprint: def-sfb-proper-scheme-tangent-data). -/
abbrev TangentExt (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) :=
  SchemeDeformation.Ext C D f (SheafOfModules.unit X.ringCatSheaf) 1

/-- The canonical field action on Ext is restriction of the derived sectionwise
scalar action along the scheme structure morphism. Source: Stacks 0DYA
(blueprint: def-sfb-proper-scheme-tangent-data). -/
@[instance_reducible]
def extModule (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) : Module k (TangentExt C D f) :=
  f.coherentExtModule (DerivedCategory.Q.obj (SchemeDeformation.cotangentComplex C D f))
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1

/-- The ordinary tangent identification, pinned to the actual sheaf extension class
of every split lift, with section-normalized coefficients and conormal representatives.
The vector-operation laws alone do not determine this class map.
Source: Stacks 0DY9, 0GPZ and 08UW
(blueprint: def-sfb-proper-scheme-tangent-data). -/
structure TangentIdentification (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) where
  split : SchemeDeformation.SplitClassification C D k f
  sheaf : TopCat.SquareZeroSheaf.Classification C D
  kernel : ∀ (M : ModuleCat.{u} k)
    (Y : SchemeDeformation.Lift f (SchemeDeformation.directionReduction k M)),
    SchemeDeformation.LiftKernel Y
  coefficient : ∀ M : ModuleCat.{u} k,
    SchemeDeformation.coefficient f (SchemeDeformation.directionReduction k M) ≅
      SchemeDeformation.directionModule f M
  coefficient_sections : ∀ (M : ModuleCat.{u} k) (m : M)
    (g : Γ((SchemeDeformation.directionReduction k M).ker.toModules, ⊤)) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ ((SchemeDeformation.directionReduction k M) ⁻¹ᵁ ⊤))
    (h' : W ≤ f ⁻¹ᵁ ⊤),
    (SchemeDeformation.directionReduction k M).ker.toModulesι.app ⊤ g =
      (Scheme.ΓSpecIso (.of (TrivSqZeroExt k M))).inv (TrivSqZeroExt.inr m) →
    (coefficient M).hom.app W
      ((SchemeDeformation.coefficient f (SchemeDeformation.directionReduction k M)).val.map
        (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection f _
          ((SchemeDeformation.directionReduction k M) ⁻¹ᵁ ⊤)
          (Scheme.Modules.tensorPullbackSection
            (SchemeDeformation.directionReduction k M) _ ⊤ g))) =
      (SchemeDeformation.directionModule f M).val.map (homOfLE h').op
        (Scheme.Modules.tensorPullbackSection f _ ⊤ (tilde.toOpen (R := .of k) M ⊤ m))
  extension : ∀ (M : ModuleCat.{u} k)
    (Y : SchemeDeformation.Lift f (SchemeDeformation.directionReduction k M)),
    SchemeDeformation.SplitLiftExtension Y (kernel M Y) (coefficient M)
  split_normalization : ∀ (M : ModuleCat.{u} k) (hM : FiniteDimensional k M)
    (Y : SchemeDeformation.Lift f (SchemeDeformation.directionReduction k M))
    (a : TopCat.SquareZeroSheaf.ConormalClass C D (extension M Y).extension
      (sheaf.standardPresentation _) (sheaf.projection _)
      (sheaf.extensionPresentation (extension M Y).extension)
      (sheaf.cl _ _ (extension M Y).extension)),
    split.classes M hM Y.class =
      SchemeDeformation.extensionClass sheaf (extension M Y).extension a
  group : AddCommGroup (SchemeDeformation.Classes f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k)))
  module : @Module k (SchemeDeformation.Classes f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k))) _ group.toAddCommMonoid
  identify : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
    (SchemeDeformation.Classes f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))) (TangentExt C D f)
    group.toAddCommMonoid _ module (extModule C D f)
  normalization : ∀ Y : SchemeDeformation.Lift f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k)),
    identify Y.class = SchemeDeformation.extMap C D f (coefficientUnit f) 1
      (split.classes (ModuleCat.of k k) inferInstance Y.class)

/-- Simultaneous global and open tangent identifications, with the actual restriction
map characterized on every marked lift. Source: Stacks 0DYW and 0GQ1
(blueprint: def-sfb-proper-scheme-tangent-data). -/
structure TangentNaturality (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) where
  global : TangentIdentification C D f
  opens : ∀ U : X.Opens, TangentIdentification C D (U.ι ≫ f)
  cotangent : ∀ U : X.Opens, SchemeDeformation.OpenComparison C D f U
  restrict : ∀ U : X.Opens, SchemeDeformation.Classes f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k)) →
      SchemeDeformation.Classes (U.ι ≫ f)
        (SchemeDeformation.directionReduction k (ModuleCat.of k k))
  restrict_exists : ∀ (U : X.Opens) (Y : SchemeDeformation.Lift f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k))),
    ∃ (Z : SchemeDeformation.Lift (U.ι ≫ f)
      (SchemeDeformation.directionReduction k (ModuleCat.of k k)))
      (q : Z.space ⟶ Y.space), SchemeDeformation.IsRestriction U.ι Y Z q
  restrict_class : ∀ (U : X.Opens) (Y : SchemeDeformation.Lift f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k)))
    (Z : SchemeDeformation.Lift (U.ι ≫ f)
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))) (q : Z.space ⟶ Y.space),
    SchemeDeformation.IsRestriction U.ι Y Z q → restrict U Y.class = Z.class
  commutes : ∀ (U : X.Opens) (x : SchemeDeformation.Classes f
    (SchemeDeformation.directionReduction k (ModuleCat.of k k))),
    (opens U).identify (restrict U x) =
      SchemeDeformation.extMap C D (U.ι ≫ f) (coefficientUnit (U.ι ≫ f)) 1
        (SchemeDeformation.extMap C D (U.ι ≫ f)
          (SchemeDeformation.directionRestriction f (ModuleCat.of k k) U).hom 1
          ((cotangent U).ext _ 1
            ((global.split.classes (ModuleCat.of k k) inferInstance) x)))

end AlgebraicGeometry.ProperSchemeDeformation
