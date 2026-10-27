/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.StableFiberCurve
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Ring.Pi

/-! # Effective stable deformation charts and their full level covers

Source: Pikaart--de Jong, Moduli of curves with non-abelian level structure,
§§2.3.3 and 2.3.6, printed pp.10--11
(blueprint: def-sfb-stable-versal-level-chart).

The formal-chart condition uses marked deformations over arbitrary affine nilpotent
thickenings. This is the local presentation of completion along the residual gerbe:
forgetting the marking takes its quotient by the actual automorphism group of C.
The generic algebra is the product of the residue fields at ALL generic points,
with the structural diagonal map from the power series ring. Normalization is its
actual integral closure. No existence or freeness is asserted by these definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.StableVersalLevel

/-- The actual equal-characteristic deformation ring, with all `3g-3` variables.
Source: Pikaart--de Jong §2.3.6, equal-characteristic fibre
(blueprint: def-sfb-stable-versal-level-chart). -/
abbrev Ring (Ω : Type u) (g : ℕ) := MvPowerSeries (Fin (3 * g - 3)) Ω

/-- The structure morphism of the affine power series base.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def base (Ω : Type u) [Field Ω] (g : ℕ) : Over (Spec (.of Ω)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω (Ring Ω g))))

/-- The closed section is the constant-coefficient quotient, rather than a chosen point.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def closed (Ω : Type u) [Field Ω] (g : ℕ) : Spec (.of Ω) ⟶ (base Ω g).left :=
  Spec.map (CommRingCat.ofHom MvPowerSeries.constantCoeff)

/-- The ordered node parameters give the discriminant product; for no nodes it is one.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def discriminant (Ω : Type u) [Field Ω] (g d : ℕ) (hd : d ≤ 3 * g - 3) : Ring Ω g :=
  ∏ i : Fin d, MvPowerSeries.X (Fin.castLE hd i)

/-- The smooth-base principal open, canonically `Spec A[1/(t₁⋯t_d)]`.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def smoothOpen (Ω : Type u) [Field Ω] (g d : ℕ) (hd : d ≤ 3 * g - 3) :
    (base Ω g).left.Opens :=
  PrimeSpectrum.basicOpen (discriminant Ω g d hd)

/-- The product of the function fields of every generic component of a scheme.
At generic points of a reduced scheme these are exactly its component function fields.
Source: Pikaart--de Jong §2.3.6, normalization of the finite etale cover
(blueprint: def-sfb-stable-versal-level-chart). -/
abbrev genericRing (E : Scheme.{u}) := ∀ x : genericPoints E, E.residueField x.val

/-- The structural diagonal map to the generic fields, obtained by global evaluation.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def genericMap {A : Type u} [CommRing A] {E : Scheme.{u}}
    (p : E ⟶ Spec (.of A)) : A →+* genericRing E :=
  RingHom.pi fun x ↦ ((Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop ≫
    E.Γevaluation x.val).hom

/-- The base algebra on the product is the specified structural diagonal algebra.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
abbrev genericAlgebra {A : Type u} [CommRing A] {E : Scheme.{u}}
    (p : E ⟶ Spec (.of A)) : Algebra A (genericRing E) :=
  (genericMap p).toAlgebra

/-- The actual integral closure, with integrality measured over the diagonal base ring.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def branchRing {A : Type u} [CommRing A] {E : Scheme.{u}}
    (p : E ⟶ Spec (.of A)) :=
  @integralClosure A (genericRing E) _ _ (genericAlgebra p)

/-- The structural morphism of the specified integral closure.
Source: Pikaart--de Jong §2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
def branchProjection {A : Type u} [CommRing A] {E : Scheme.{u}}
    (p : E ⟶ Spec (.of A)) : Spec (.of (branchRing p)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (branchRing p)))


/-- Marked universality on every affine nilpotent thickening. The unique pair is the
classifying map and the unique marking-preserving isomorphism. The displayed equation
uses the canonical closed-fibre inclusions. Thus this is a natural formal chart,
including its arrows, rather than a pointwise bijection on isomorphism classes.
Etale locally an object of the residual gerbe is the constant curve C. Its markings
form its actual Aut(C)-torsor; forgetting the marking therefore gives the formal
quotient. Testing every nilpotent ideal, rather than only rational Artinian tests,
also retains torsors on nonlocal bases and arbitrary residue extensions.
Source: Pikaart--de Jong §2.3.6; Deligne--Mumford §1
(blueprint: def-sfb-stable-versal-level-chart). -/
def IsFormalChart (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : ℕ)
    (C : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (Over.mk (𝟙 _)))
    (D : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (base Ω g))
    (e : (Over.pullback (closed Ω g)).obj (StablePointedModuli.fiberCurve D) ≅
      StablePointedModuli.fiberCurve C) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra Ω R] (I : Ideal R),
    (∃ n : ℕ, I ^ n = ⊥) →
    ∀ (X : StablePointedModuli.Fiber (Spec (.of Ω)) g 0
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω R)))))
      (i : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
          (StablePointedModuli.fiberCurve X) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Ω (R ⧸ I))))).obj
          (StablePointedModuli.fiberCurve C)),
      ∃! q : Σ a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω R))) ⟶ base Ω g,
          StablePointedModuli.fiberCurve X ≅
            (Over.pullback a.left).obj (StablePointedModuli.fiberCurve D),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ q.1.left =
          Spec.map (CommRingCat.ofHom (algebraMap Ω (R ⧸ I))) ≫ closed Ω g ∧
        i.inv.left ≫ pullback.fst (StablePointedModuli.fiberCurve X).hom
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ q.2.hom.left ≫
            pullback.fst (StablePointedModuli.fiberCurve D).hom q.1.left =
          pullback.fst (StablePointedModuli.fiberCurve C).hom
              (Spec.map (CommRingCat.ofHom (algebraMap Ω (R ⧸ I)))) ≫
            e.inv.left ≫ pullback.fst (StablePointedModuli.fiberCurve D).hom (closed Ω g)

/-- A full frame is represented by a universal frame on the actual pulled-back family.
The classifying map is unique and its frame condition uses canonical inverse image,
constant comparison and degree-one proper base change from the recorded moduli module.
Source: Pikaart--de Jong §2.3.3
(blueprint: def-sfb-stable-versal-level-chart). -/
def IsFullFrameCover {X A U E : Scheme.{u}} (f : X ⟶ A) (j : U ⟶ A)
    (p : E ⟶ U) (g ℓ : ℕ)
    (frame : abelianLevelConstant E g ℓ ≅
      abelianLevelCohomology (pullback.snd f (p ≫ j)) ℓ) : Prop :=
  ∀ (T : Scheme.{u}) (a : T ⟶ U)
    (α : abelianLevelConstant T g ℓ ≅
      abelianLevelCohomology (pullback.snd f (a ≫ j)) ℓ),
    ∃! b : T ⟶ E, b ≫ p = a ∧
      ∃ (q : pullback f (a ≫ j) ⟶ pullback f (p ≫ j))
        (sq : IsPullback q (pullback.snd f (a ≫ j)) (pullback.snd f (p ≫ j)) b),
        q ≫ pullback.fst f (p ≫ j) = pullback.fst f (a ≫ j) ∧
        (Etale.upperStar _ b).map frame.hom ≫ abelianLevelBaseChange sq.toCommSq ℓ =
          ((Scheme.upperStarConstantSheafIso _ b).hom.app
            (ModuleCat.of (ULift.{u + 1} (ZMod ℓ))
              (Fin (2 * g) → ULift.{u + 1} (ZMod ℓ)))) ≫ α.hom

/-- An effective equivariant stable chart with its full frame cover and its specified
normalization. The conditions do not assert existence. In particular no freeness is
built into this notion: that is the separate theorem about these data.

The `formal` field retains every special-fibre marking and all isomorphisms.
Together with `specialAction` this identifies the formal quotient with completion
along the residual gerbe. `smoothLocus` is tested on every base change and so states
the full discriminant equality. `frameAction` requires the natural action on frames:
the constant labels have trivial action. `normalGeneric` fixes the inclusion of the
integral closure into the actual generic product, precluding an arbitrary normalization.
Source: Pikaart--de Jong §§2.3.3 and 2.3.6
(blueprint: def-sfb-stable-versal-level-chart). -/
structure Chart (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g d ℓ : ℕ)
    (C : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (Over.mk (𝟙 _))) where
  nodeBound : d ≤ 3 * g - 3
  deformation : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (base Ω g)
  special : (Over.pullback (closed Ω g)).obj
    (StablePointedModuli.fiberCurve deformation) ≅ StablePointedModuli.fiberCurve C
  formal : IsFormalChart Ω g C deformation special
  baseAction : Aut (StablePointedModuli.fiberCurve C) →* Aut (base Ω g)
  curveAction : Aut (StablePointedModuli.fiberCurve C) →*
    Aut ((Over.map (base Ω g).hom).obj (StablePointedModuli.fiberCurve deformation))
  fixesClosed : ∀ h, closed Ω g ≫ (baseAction h).hom.left = closed Ω g
  equivariant : ∀ h, (curveAction h).hom.left ≫
    (StablePointedModuli.fiberCurve deformation).hom =
      (StablePointedModuli.fiberCurve deformation).hom ≫ (baseAction h).hom.left
  specialAction : ∀ h, special.inv.left ≫
      pullback.fst (StablePointedModuli.fiberCurve deformation).hom (closed Ω g) ≫
      (curveAction h).hom.left =
    h.hom.left ≫ special.inv.left ≫
      pullback.fst (StablePointedModuli.fiberCurve deformation).hom (closed Ω g)
  smoothLocus : ∀ (T : Scheme.{u}) (a : T ⟶ (base Ω g).left),
    Smooth (pullback.snd (StablePointedModuli.fiberCurve deformation).hom a) ↔
      Set.range a ⊆ (smoothOpen Ω g d nodeBound : Set (base Ω g).left)
  cover : Scheme.{u}
  coverMap : cover ⟶ (smoothOpen Ω g d nodeBound).toScheme
  finite : IsFinite coverMap
  etale : Etale coverMap
  frame : abelianLevelConstant cover g ℓ ≅
    abelianLevelCohomology (pullback.snd (StablePointedModuli.fiberCurve deformation).hom
      (coverMap ≫ (smoothOpen Ω g d nodeBound).ι)) ℓ
  represents : IsFullFrameCover (StablePointedModuli.fiberCurve deformation).hom
    (smoothOpen Ω g d nodeBound).ι coverMap g ℓ frame
  coverAction : Aut (StablePointedModuli.fiberCurve C) →*
    Aut (Over.mk (coverMap ≫ (smoothOpen Ω g d nodeBound).ι ≫ (base Ω g).hom))
  coverEquivariant : ∀ h,
    (coverAction h).hom.left ≫ coverMap ≫ (smoothOpen Ω g d nodeBound).ι =
      coverMap ≫ (smoothOpen Ω g d nodeBound).ι ≫ (baseAction h).hom.left
  frameAction : ∀ h,
    ∃ (q : pullback (StablePointedModuli.fiberCurve deformation).hom
          (coverMap ≫ (smoothOpen Ω g d nodeBound).ι) ⟶
        pullback (StablePointedModuli.fiberCurve deformation).hom
          (coverMap ≫ (smoothOpen Ω g d nodeBound).ι))
      (sq : IsPullback q (pullback.snd _ _) (pullback.snd _ _)
        (coverAction h).hom.left),
      q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (curveAction h).hom.left ∧
      (Etale.upperStar _ (coverAction h).hom.left).map frame.hom ≫
          abelianLevelBaseChange sq.toCommSq ℓ =
        ((Scheme.upperStarConstantSheafIso _ (coverAction h).hom.left).hom.app
          (ModuleCat.of (ULift.{u + 1} (ZMod ℓ))
            (Fin (2 * g) → ULift.{u + 1} (ZMod ℓ)))) ≫ frame.hom
  normalOpen : cover ⟶ Spec (.of (branchRing
    (coverMap ≫ (smoothOpen Ω g d nodeBound).ι)))
  normalSquare : IsPullback normalOpen coverMap
    (branchProjection (coverMap ≫ (smoothOpen Ω g d nodeBound).ι))
    (smoothOpen Ω g d nodeBound).ι
  normalGeneric : ∀ (z : branchRing (coverMap ≫ (smoothOpen Ω g d nodeBound).ι))
    (x : genericPoints cover),
    cover.Γevaluation x.val (normalOpen.appTop
      ((Scheme.ΓSpecIso (.of (branchRing
        (coverMap ≫ (smoothOpen Ω g d nodeBound).ι)))).inv z)) = z.val x
  normalAction : Aut (StablePointedModuli.fiberCurve C) →*
    Aut (Over.mk (branchProjection (coverMap ≫ (smoothOpen Ω g d nodeBound).ι) ≫
      (base Ω g).hom))
  normalEquivariant : ∀ h, (normalAction h).hom.left ≫
      branchProjection (coverMap ≫ (smoothOpen Ω g d nodeBound).ι) =
    branchProjection (coverMap ≫ (smoothOpen Ω g d nodeBound).ι) ≫
      (baseAction h).hom.left
  extendsCoverAction : ∀ h,
    normalOpen ≫ (normalAction h).hom.left = (coverAction h).hom.left ≫ normalOpen

end AlgebraicGeometry.StableVersalLevel
