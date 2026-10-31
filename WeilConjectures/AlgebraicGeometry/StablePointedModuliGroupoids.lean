/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedCurve
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
public import WeilConjectures.SixFunctors.GeometricInverseImageConstantModuleSupplement
public import WeilConjectures.TraceFormula.ProjectiveBundleProper

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.StablePointedCurveBaseChange
import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Stable pointed moduli groupoids and abelian level structures

Source: Pikaart--de Jong (1995), §§1.1 and 2.3.3--2.3.7; Stacks, Tags 003T,
003R, 026F and 025Y (blueprint: def-sfb-stable-pointed-moduli-groupoids).

Objects are families, not their isomorphism classes. Cartesian squares encode the
specified isomorphisms to fibre products, with composition by pasting. Fixed-ring
module sheaves use the equivalent sheaves-with-values-in-ModuleCat encoding already
used by the proper base change interface. The coefficient lift changes size only.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A stable ordered family of specified geometric arithmetic genus. The base is an
actual `S`-scheme; the sections retain their labels, including the empty label set.
Source: Pikaart--de Jong §1.1 and the stable pointed convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
structure StablePointedModuli (S : Scheme.{u}) (g r : ℕ) where
  genus_at_least_two : 2 ≤ g
  base : Over S
  curve : Scheme.{u}
  projection : curve ⟶ base.left
  sections : Fin r → (base.left ⟶ curve)
  section_projection : ∀ i, sections i ≫ projection = 𝟙 base.left
  stable : IsStablePointedCurve projection sections section_projection
  genus : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ base.left),
    Module.finrank Ω
      ((ModuleCat.restrictScalars
        (((Scheme.ΓSpecIso (.of Ω)).inv ≫ (pullback.snd projection a).appTop).hom)).obj
          ((RingedSpace.moduleCohomology (pullback projection a).toRingedSpace 1).obj
            (SheafOfModules.unit (moduleRings (pullback projection a).toRingedSpace)))) = g

namespace StablePointedModuli

/-- Arrows over a base arrow are labelled cartesian squares, equivalently isomorphisms
to the indicated fibre product over the new base.
Source: Pikaart--de Jong §2.3.3; Stacks 003T
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
@[ext]
structure Hom {S : Scheme.{u}} {g r : ℕ} (X Y : StablePointedModuli S g r) where
  base : X.base ⟶ Y.base
  map : X.curve ⟶ Y.curve
  square : IsPullback map X.projection Y.projection base.left
  markings : ∀ i, X.sections i ≫ map = base.left ≫ Y.sections i

/-- Identity and pasting preserve the labelled cartesian-square condition.
Source: Stacks 003T, uniqueness of fibre products
(blueprint: def-sfb-stable-pointed-moduli-groupoids).
Proof: the identity square is cartesian; paste the two cartesian squares. Compose the
marking equations and use associativity. These operations are precisely composition
through the canonical associativity isomorphism of fibre products. -/
theorem hom_operations {S : Scheme.{u}} {g r : ℕ} :
    (∀ X : StablePointedModuli S g r,
      IsPullback (𝟙 X.curve) X.projection X.projection (𝟙 X.base.left) ∧
        ∀ i, X.sections i ≫ 𝟙 X.curve = (𝟙 X.base.left) ≫ X.sections i) ∧
    (∀ {X Y Z : StablePointedModuli S g r} (a : Hom X Y) (b : Hom Y Z),
      IsPullback (a.map ≫ b.map) X.projection Z.projection (a.base ≫ b.base).left ∧
        ∀ i, X.sections i ≫ (a.map ≫ b.map) = (a.base ≫ b.base).left ≫ Z.sections i) := by
  constructor
  · intro X
    exact ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun i ↦ by simp⟩
  · intro X Y Z a b
    refine ⟨a.square.paste_horiz b.square, fun i ↦ ?_⟩
    change X.sections i ≫ (a.map ≫ b.map) = (a.base.left ≫ b.base.left) ≫ Z.sections i
    rw [← Category.assoc, a.markings, Category.assoc, b.markings, Category.assoc]

/-- The total category of stable ordered pointed families, with actual cartesian arrows.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
instance {S : Scheme.{u}} {g r : ℕ} : Category (StablePointedModuli S g r) where
  Hom := Hom
  id X := ⟨𝟙 X.base, 𝟙 X.curve, (hom_operations.1 X).1, (hom_operations.1 X).2⟩
  comp a b := ⟨a.base ≫ b.base, a.map ≫ b.map,
    (hom_operations.2 a b).1, (hom_operations.2 a b).2⟩
  id_comp _a := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _a := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _a _b _c := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Projection to `Sch/S` remembers the actual base arrow.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def forget (S : Scheme.{u}) (g r : ℕ) : StablePointedModuli S g r ⥤ Over S where
  obj X := X.base
  map a := a.base

/-- The fibre groupoid has labelled isomorphisms and retains automorphisms.
Source: Pikaart--de Jong §1.1 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev Fiber (S : Scheme.{u}) (g r : ℕ) (T : Over S) :=
  Core (CategoryTheory.Functor.Fiber (forget S g r) T)

/-- The smooth-family full subcategory of the total category.
Source: Pikaart--de Jong §1.1 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev Smooth (S : Scheme.{u}) (g r : ℕ) :=
  ObjectProperty.FullSubcategory
    (fun X : StablePointedModuli S g r ↦ AlgebraicGeometry.Smooth X.projection)

/-- Stability and geometric genus are preserved by the specified fibre product.
Source: stable pointed base change, Pikaart--de Jong §2.3.3
(blueprint: def-sfb-stable-pointed-moduli-groupoids).
Proof: projectivity, flatness, finite presentation, nodality, disjoint markings and their
smooth-locus condition are stable under base change. A geometric fibre of the pullback
is the same geometric curve over an algebraically closed extension. Its component genera,
special points and arithmetic genus are unchanged. This also covers an empty base. -/
theorem pullback_properties {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedModuli S g r) (T : Over S) (a : T ⟶ X.base) :
    IsStablePointedCurve (pullback.snd X.projection a.left)
      (fun i ↦ X.projection.baseChangeSection (X.sections i) (X.section_projection i) a.left)
      (fun i ↦ X.projection.baseChangeSection_snd
        (X.sections i) (X.section_projection i) a.left) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T.left),
      Module.finrank Ω
        ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of Ω)).inv ≫
          (pullback.snd (pullback.snd X.projection a.left) b).appTop).hom)).obj
            ((RingedSpace.moduleCohomology
              (pullback (pullback.snd X.projection a.left) b).toRingedSpace 1).obj
                (SheafOfModules.unit
                  (moduleRings
                    (pullback (pullback.snd X.projection a.left) b).toRingedSpace)))) = g := by
  refine ⟨isStablePointedCurve_baseChange X.projection X.sections X.section_projection
    X.stable a.left, ?_⟩
  intro Ω _ _ b
  let e := pullbackLeftPullbackSndIso X.projection a.left b
  have hc := finrank_structureSheafCohomology_iso e
    (pullback.snd (pullback.snd X.projection a.left) b)
    (pullback.snd X.projection (b ≫ a.left))
    (pullbackLeftPullbackSndIso_hom_snd X.projection a.left b) 1
  exact hc.trans (X.genus Ω (b ≫ a.left))

/-- Pullback uses the actual scheme fibre product and the labelled paired sections.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def pullback {S : Scheme.{u}} {g r : ℕ} (X : StablePointedModuli S g r)
    (T : Over S) (a : T ⟶ X.base) : StablePointedModuli S g r where
  genus_at_least_two := X.genus_at_least_two
  base := T
  curve := Limits.pullback X.projection a.left
  projection := Limits.pullback.snd X.projection a.left
  sections i := X.projection.baseChangeSection (X.sections i) (X.section_projection i) a.left
  section_projection i := X.projection.baseChangeSection_snd
    (X.sections i) (X.section_projection i) a.left
  stable := (pullback_properties X T a).1
  genus := (pullback_properties X T a).2

/-- The cartesian pullback arrow has first projection on curves and the specified
base arrow; its marking equations are the paired-section projection equations.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def pullbackArrow {S : Scheme.{u}} {g r : ℕ} (X : StablePointedModuli S g r)
    (T : Over S) (a : T ⟶ X.base) : X.pullback T a ⟶ X where
  base := a
  map := Limits.pullback.fst X.projection a.left
  square := IsPullback.of_hasPullback X.projection a.left
  markings i := X.projection.baseChangeSection_fst
    (X.sections i) (X.section_projection i) a.left

end StablePointedModuli

/-- Admissible abelian levels: prime at least three, invertible in every local ring.
Source: Pikaart--de Jong §§1.1 and 2.3.3--2.3.7
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev AbelianLevelPrime (S : Scheme.{u}) :=
  {ℓ : ℕ // ℓ.Prime ∧ 3 ≤ ℓ ∧ ∀ x : S, IsUnit (ℓ : S.presheaf.stalk x)}

/-- Degree-one direct image of the constant coefficient module. `ULift` is the
coefficient-size convention, and does not alter the ring `ℤ/ℓℤ`.
Source: Pikaart--de Jong §2.3.3, Stacks 03Q8
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def abelianLevelCohomology {X T : Scheme.{u}} (f : X ⟶ T) (ℓ : ℕ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).rightDerived 1).obj
    ((constantSheaf X.smallEtaleTopology _).obj
      (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ))))

/-- The constant rank-`2g` module sheaf, without a pairing or symplectic condition.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def abelianLevelConstant (T : Scheme.{u}) (g ℓ : ℕ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) :=
  (constantSheaf T.smallEtaleTopology _).obj
    (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (Fin (2 * g) → ULift.{u + 1} (ZMod ℓ)))

/-- The degree-one canonical exchange map, followed by the canonical constant-coefficient
comparison. It is defined for every commutative square, before any invertibility claim.
Source: proper base change, Stacks 0DDE; Pikaart--de Jong §2.3.3
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def abelianLevelBaseChange {X' X T' T : Scheme.{u}} {h : X' ⟶ X}
    {f' : X' ⟶ T'} {f : X ⟶ T} {a : T' ⟶ T}
    (sq : CommSq h f' f a) (ℓ : ℕ) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) a).obj
        (abelianLevelCohomology f ℓ) ⟶ abelianLevelCohomology f' ℓ :=
  (Etale.upperStar _ a).map
      ((Etale.lowerStar _ f).homologyRightDerivedFunctorPlusObjSingleFunctorIso _ 1).inv ≫
    ((Etale.upperStar _ a).mapDerivedCategoryPlusHomologyFunctorIso 1).hom.app _ ≫
    (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((Etale.derivedBaseChangeMapPlus _ sq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology _).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ)))))) ≫
    (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((Etale.lowerStar _ f').rightDerivedFunctorPlus.map
        (((Etale.upperStar _ h).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Scheme.upperStarConstantSheafIso _ h).hom.app
              (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ)))))) ≫
    ((Etale.lowerStar _ f').homologyRightDerivedFunctorPlusObjSingleFunctorIso _ 1).hom

/-- A level family is a smooth unpointed family with an actual module-sheaf frame.
No polarization or symplectic form is part of its data.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
structure AbelianLevelModuli (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) where
  family : StablePointedModuli.Smooth S g 0
  frame : abelianLevelConstant family.obj.base.left g ℓ.val ≅
    abelianLevelCohomology family.obj.projection ℓ.val

namespace AbelianLevelModuli

/-- Frame-preserving arrows use the canonical exchange of the cartesian family square.
For an identity base arrow this is precisely `α* λY = λX`.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def HomCondition {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S}
    (X Y : AbelianLevelModuli S g ℓ) (a : X.family ⟶ Y.family) : Prop :=
  (Etale.upperStar _ a.hom.base.left).map Y.frame.hom ≫
      abelianLevelBaseChange a.hom.square.toCommSq ℓ.val =
    ((Scheme.upperStarConstantSheafIso _ a.hom.base.left).hom.app
      (ModuleCat.of (ULift.{u + 1} (ZMod ℓ.val))
        (Fin (2 * g) → ULift.{u + 1} (ZMod ℓ.val)))) ≫ X.frame.hom

/-- The frame condition is closed under identity and composition, using canonical
constant and exchange coherence, rather than an arbitrary identification.
Source: Pikaart--de Jong §2.3.3, functoriality of proper base change
(blueprint: def-sfb-stable-pointed-moduli-groupoids).
Proof: for identities the exchange and constant comparisons are the unit comparisons.
For a pasted square the exchange is the composite of the two exchanges, conjugated by
the composition comparison for inverse image. Substitute the two frame equations and
use naturality and the constant-comparison composition equation. -/
theorem hom_operations {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S} :
    (∀ X : AbelianLevelModuli S g ℓ, HomCondition X X (𝟙 X.family)) ∧
    (∀ {X Y Z : AbelianLevelModuli S g ℓ} (a : X.family ⟶ Y.family)
      (b : Y.family ⟶ Z.family), HomCondition X Y a → HomCondition Y Z b →
        HomCondition X Z (a ≫ b)) := by
  sorry

/-- The total level category retains precisely frame-preserving family arrows.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
instance {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S} :
    Category (AbelianLevelModuli S g ℓ) where
  Hom X Y := {a : X.family ⟶ Y.family // HomCondition X Y a}
  id X := ⟨𝟙 X.family, hom_operations.1 X⟩
  comp a b := ⟨a.val ≫ b.val, hom_operations.2 a.val b.val a.property b.property⟩
  id_comp _a := Subtype.ext (Category.id_comp _)
  comp_id _a := Subtype.ext (Category.comp_id _)
  assoc _a _b _c := Subtype.ext (Category.assoc _ _ _)

/-- Projection of the level category to `Sch/S`.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def forget (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) :
    AbelianLevelModuli S g ℓ ⥤ Over S where
  obj X := X.family.obj.base
  map a := a.val.hom.base

/-- The level fibre is the groupoid of framed families, not a set of coarse points.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev Fiber (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) (T : Over S) :=
  Core (CategoryTheory.Functor.Fiber (forget S g ℓ) T)

end AbelianLevelModuli

/-- The canonical frame exchange is invertible for a proper cartesian family square.
Source: Stacks 0DDE, degree one of proper base change
(blueprint: def-sfb-stable-pointed-moduli-groupoids).
Proof: the constant coefficient module is killed by the nonzero integer ℓ. Apply proper
base change to that constant sheaf in degree zero, then degree-one homology. Exact
inverse image commutes with homology and with single complexes; the remaining constant
coefficient comparison is an isomorphism. Each comparison is the one used in the map. -/
theorem abelianLevelBaseChange_isIso {X' X T' T : Scheme.{u}} {h : X' ⟶ X}
    {f' : X' ⟶ T'} {f : X ⟶ T} {a : T' ⟶ T} [IsProper f]
    (sq : IsPullback h f' f a) (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    IsIso (abelianLevelBaseChange sq.toCommSq ℓ) := by
  let : NeZero ℓ := ⟨hℓ⟩
  have : IsIso (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      sq.toCommSq) :=
    Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring _ isAddTorsion_of_finite sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  unfold abelianLevelBaseChange
  infer_instance

namespace AbelianLevelModuli

/-- Pullback of a level family uses the specified constant comparison, pulled-back frame,
and degree-one proper base change, in that order.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def pullback {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S}
    (X : AbelianLevelModuli S g ℓ) (T : Over S) (a : T ⟶ X.family.obj.base) :
    AbelianLevelModuli S g ℓ :=
  letI : AlgebraicGeometry.Smooth X.family.obj.projection := X.family.property
  letI : IsProper X.family.obj.projection :=
    projectiveBundle_proper _ X.family.obj.stable.1
  letI : IsIso (abelianLevelBaseChange
      (IsPullback.of_hasPullback X.family.obj.projection a.left).toCommSq ℓ.val) :=
    abelianLevelBaseChange_isIso (IsPullback.of_hasPullback _ _) ℓ.val ℓ.property.1.ne_zero
  { family := ⟨X.family.obj.pullback T a,
      inferInstanceAs (AlgebraicGeometry.Smooth
        (Limits.pullback.snd X.family.obj.projection a.left))⟩
    frame := ((Scheme.upperStarConstantSheafIso _ a.left).app
        (ModuleCat.of (ULift.{u + 1} (ZMod ℓ.val))
          (Fin (2 * g) → ULift.{u + 1} (ZMod ℓ.val)))).symm ≪≫
      (Etale.upperStar _ a.left).mapIso X.frame ≪≫
      asIso (abelianLevelBaseChange
        (IsPullback.of_hasPullback X.family.obj.projection a.left).toCommSq ℓ.val) }

/-- The explicitly pulled-back frame is preserved by the cartesian pullback arrow.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids).
Proof: unfold the frame as constant comparison inverse, inverse image of the old frame,
and degree-one exchange. The inverse constant comparison cancels the constant
comparison in the arrow condition. The remaining exchange is the very same map. -/
theorem pullback_frame_condition {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S}
    (X : AbelianLevelModuli S g ℓ) (T : Over S) (a : T ⟶ X.family.obj.base) :
    HomCondition (X.pullback T a) X
      (ObjectProperty.homMk (X.family.obj.pullbackArrow T a)) := by
  dsimp [HomCondition, pullback, StablePointedModuli.pullbackArrow,
    abelianLevelConstant]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The pullback arrow of a framed family, including its actual family isomorphism.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def pullbackArrow {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S}
    (X : AbelianLevelModuli S g ℓ) (T : Over S) (a : T ⟶ X.family.obj.base) :
    X.pullback T a ⟶ X :=
  ⟨ObjectProperty.homMk (X.family.obj.pullbackArrow T a), pullback_frame_condition X T a⟩

end AbelianLevelModuli

end AlgebraicGeometry

namespace CategoryTheory

universe v₁ v₂ v₃ w₁ w₂ w₃

/-- Total-category version of fibred in groupoids: every base arrow lifts and every
arrow has the strong cartesian universal property, including its uniqueness clause.
This reuses Mathlib's fibre and strong cartesian predicates.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsFibredInGroupoids {B : Type w} [Category.{v} B]
    (F : BasedCategory.{v₁, w₁} B) : Prop :=
  F.p.IsFibered ∧ ∀ {x y : F.obj} (a : x ⟶ y), F.p.IsStronglyCartesian (F.p.map a) a

/-- 2-morphisms are natural isomorphisms whose components lie over identities.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev ModuliTwoIso {B : Type w} [Category.{v} B]
    {F : BasedCategory.{v₁, w₁} B} {G : BasedCategory.{v₂, w₂} B}
    (f g : BasedFunctor F G) :=
  {e : f.toFunctor ≅ g.toFunctor //
    ∀ x : F.obj, G.p.IsHomLift (𝟙 (F.p.obj x)) (e.hom.app x)}

/-- The ordinary 2-fibre product of groupoids is the iso-comma category. Its arrows
are precisely the pairs satisfying the comma square; no isomorphism classes are taken.
Source: Stacks 003R (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
abbrev GroupoidTwoFiberProduct {A : Type w₁} {B : Type w₂} {C : Type w₃}
    [Groupoid.{v₁} A] [Groupoid.{v₂} B] [Groupoid.{v₃} C] (f : A ⥤ C) (g : B ⥤ C) :=
  Core (Comma f g)

/-- For categories over a base, the comparison is an isomorphism in one fibre.
The full comma subcategory gives the induced pullbacks and their natural arrows.
Source: Stacks 003R (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def moduliTwoFiberProduct {B : Type w} [Category.{v} B]
    {F : BasedCategory.{v₁, w₁} B} {G : BasedCategory.{v₂, w₂} B}
    {H : BasedCategory.{v₃, w₃} B} (f : BasedFunctor F H) (g : BasedFunctor G H) :
    BasedCategory B :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (fun x : Comma f.toFunctor g.toFunctor ↦
      IsIso x.hom ∧ H.p.IsHomLift (𝟙 (F.p.obj x.left)) x.hom) ⋙
        Comma.fst f.toFunctor g.toFunctor ⋙ F.p)

/-- Projection from the total 2-fibre product to its first factor.
Source: Stacks 003R (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def moduliTwoFiberFst {B : Type w} [Category.{v} B]
    {F : BasedCategory.{v₁, w₁} B} {G : BasedCategory.{v₂, w₂} B}
    {H : BasedCategory.{v₃, w₃} B} (f : BasedFunctor F H) (g : BasedFunctor G H) :
    BasedFunctor (moduliTwoFiberProduct f g) F where
  toFunctor := ObjectProperty.ι _ ⋙ Comma.fst f.toFunctor g.toFunctor
  w := rfl

/-- A set-valued presheaf as a discrete fibred groupoid. Objects over `T` are maps
`h_T → P`; their equivalence with `P(T)` is Yoneda. The projection has discrete fibres.
Source: Stacks 003T and 025Y (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def discreteModuli {S : AlgebraicGeometry.Scheme.{u}}
    (P : (Over S)ᵒᵖ ⥤ Type u) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (CostructuredArrow.proj yoneda P)

/-- A map of presheaves induces a functor of discrete fibred groupoids.
Source: Stacks 003T and 025Y (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def discreteModuliMap {S : AlgebraicGeometry.Scheme.{u}}
    {P Q : (Over S)ᵒᵖ ⥤ Type u} (a : P ⟶ Q) :
    BasedFunctor (discreteModuli P) (discreteModuli Q) where
  toFunctor := CostructuredArrow.map a
  w := rfl

/-- Representation means equivalence over `Sch/S`, retaining all automorphisms.
Source: Pikaart--de Jong §2.3.3 (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsRepresentedByScheme {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (Q : Over S) : Prop :=
  ∃ e : BasedFunctor (discreteModuli (yoneda.obj Q)) F, e.toFunctor.IsEquivalence

/-- A functor over the base induces the actual functor on fibres.
Source: Stacks 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def moduliFiberMap {B : Type w} [Category.{v} B]
    {F : BasedCategory.{v₁, w₁} B} {G : BasedCategory.{v₂, w₂} B}
    (f : BasedFunctor F G) (T : B) : Functor.Fiber F.p T ⥤ Functor.Fiber G.p T :=
  Functor.Fiber.inducedFunctor
    (F := Functor.Fiber.fiberInclusion (p := F.p) (S := T) ⋙ f.toFunctor)
    (p := G.p) (S := T)
    ((congrArg (fun k ↦ Functor.Fiber.fiberInclusion (p := F.p) (S := T) ⋙ k) f.w).trans
      (Functor.Fiber.fiberInclusion_comp_eq_const (p := F.p) (S := T)))

/-- The universal property for maps into every algebraic space, together with the
bijection on geometric isomorphism classes. The quotient is Mathlib's skeleton; its
map is induced by the actual functor on fibres, not an unrelated point bijection.
Source: Pikaart--de Jong §§2.3.4--2.3.7; Stacks coarse moduli convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsCoarseModuliScheme {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (Q : Over S)
    (π : BasedFunctor F (discreteModuli (yoneda.obj Q))) : Prop :=
  (∀ Z : AlgebraicGeometry.AlgebraicSpace S,
    Function.Bijective (fun a : yoneda.obj Q ⟶ Z.obj.obj ↦
      π.comp (discreteModuliMap a))) ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : AlgebraicGeometry.Spec (.of Ω) ⟶ S),
    Function.Bijective ((moduliFiberMap π (Over.mk a)).mapSkeleton.obj)

/-- Stack descent in the total-category formulation. A descent datum is a cartesian
section over a covering sieve. A gluing is a cocone over its canonical base cocone;
being colimiting expresses unique gluing of isomorphisms as well as effectiveness.
For a category fibred in groupoids this is equivalent to the usual equivalence with
the category of descent data (Mathlib's pseudofunctor `IsStack`).
Source: Stacks 026F and 003T (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsModuliStack {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  IsFibredInGroupoids F ∧
  ∀ (T : Over S) (R : Sieve T), R ∈ (AlgebraicGeometry.Scheme.etaleTopology.over S) T →
    ∀ (D : R.arrows.category ⥤ F.obj) (hD : D ⋙ F.p = R.arrows.diagram),
      ∃ (c : Cocone D) (hc : F.p.obj c.pt = T), Nonempty (IsColimit c) ∧
        ∀ i : R.arrows.category,
          F.p.map (c.ι.app i) ≫ eqToHom hc =
            eqToHom (Functor.congr_obj hD i) ≫ i.obj.hom

/-- An algebraic-space presentation of a particular 2-base change, compatible with
its map to the test scheme. The projection is part of the presentation, so atlas
properties below are tested on the specified morphism.
Source: Stacks 003R and 025Y (blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def HasSpaceBaseChange {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) (T : Over S)
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
    (Z : AlgebraicGeometry.AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∃ e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct t f),
    e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t f)) (discreteModuliMap a))

/-- Representability by algebraic spaces is tested on every scheme 2-base change.
Source: Stacks 025Y and the DM convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsRepresentableByAlgebraicSpaces {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z a

/-- The diagonal's representability, tested by fibre products of two scheme maps.
These are precisely the scheme tests for the diagonal over the product of the two schemes.
Source: Stacks DM diagonal criterion, 003R and 025Y
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def HasAlgebraicSpaceDiagonal {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∀ (T U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
      (b : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S),
      ∃ e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct a b),
        e.toFunctor.IsEquivalence

/-- Étaleness of a map from an algebraic space to a scheme is checked on all its
étale scheme charts, using the recorded algebraic-space definition and scheme étaleness.
Source: Stacks 025Y and DM atlas convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def SpaceMapIsEtale {S : AlgebraicGeometry.Scheme.{u}}
    (Z : AlgebraicGeometry.AlgebraicSpace S) (T : Over S) (a : Z.obj.obj ⟶ yoneda.obj T) :
    Prop :=
  ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicGeometry.AlgebraicSpace.IsEtale b →
    AlgebraicGeometry.Etale ((yoneda.preimage (b ≫ a)).left)

/-- Surjectivity is joint surjectivity on the points of étale scheme charts.
Source: Stacks 025Y and DM atlas convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def SpaceMapIsSurjective {S : AlgebraicGeometry.Scheme.{u}}
    (Z : AlgebraicGeometry.AlgebraicSpace S) (T : Over S) (a : Z.obj.obj ⟶ yoneda.obj T) :
    Prop :=
  ∀ x : T.left, ∃ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj),
    AlgebraicGeometry.AlgebraicSpace.IsEtale b ∧
      ∃ y : U.left, (yoneda.preimage (b ≫ a)).left y = x

/-- A DM stack is a stack with algebraic-space diagonal and a surjective étale
scheme atlas. Every atlas base change is compared with its actual algebraic-space
projection; no existence of an atlas for a particular moduli groupoid is asserted.
Source: Pikaart--de Jong §1.1; Stacks DM convention
(blueprint: def-sfb-stable-pointed-moduli-groupoids). -/
def IsDeligneMumfordModuliStack {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  IsModuliStack F ∧ HasAlgebraicSpaceDiagonal F ∧
    ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p

end CategoryTheory
