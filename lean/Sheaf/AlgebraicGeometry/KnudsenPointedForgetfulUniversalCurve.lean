/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.StablePointedCurve
import Sheaf.TraceFormula.ProjectiveBundleProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen

/-! # Knudsen's forgetful morphism and the universal stable curve

Source: Knudsen, The projectivity of the moduli space of stable curves II (1983),
§2, Corollary 2.6 and Theorem 2.7; Knudsen, A closer look at the stacks of stable
pointed curves, Introduction and §5
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve).

The auxiliary category is the paper's `C_{g,r}`: a stable ordered family and an
arbitrary extra section. No smoothness or avoidance condition is imposed on that
section. Schemes are moduli groupoids through the recorded `discreteModuli (yoneda.obj Q)`.
The representing equivalence is normalized by the contraction's actual extra section.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The universal curve category: stable labelled families with one arbitrary section.
Source: Knudsen, A closer look, Introduction, `C_{g,n}`
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
structure StablePointedUniversalCurve (S : Scheme.{u}) (g r : ℕ) where
  family : StablePointedModuli S g r
  extra : family.base.left ⟶ family.curve
  extra_projection : extra ≫ family.projection = 𝟙 family.base.left

namespace StablePointedUniversalCurve

/-- Cartesian labelled arrows must also preserve the arbitrary extra section.
Source: Knudsen, A closer look, Introduction
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev Hom {S : Scheme.{u}} {g r : ℕ} (X Y : StablePointedUniversalCurve S g r) :=
  {a : X.family ⟶ Y.family // X.extra ≫ a.map = a.base.left ≫ Y.extra}

/-- The total category uses the same cartesian arrows as the recorded moduli definition.
Source: Knudsen, A closer look, Introduction
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
instance {S : Scheme.{u}} {g r : ℕ} : Category (StablePointedUniversalCurve S g r) where
  Hom := Hom
  id X := ⟨𝟙 X.family, by change X.extra ≫ 𝟙 _ = 𝟙 _ ≫ X.extra; simp⟩
  comp a b := ⟨a.val ≫ b.val, by
    change _ ≫ (a.val.map ≫ b.val.map) = (a.val.base.left ≫ b.val.base.left) ≫ _
    rw [← Category.assoc, a.property, Category.assoc, b.property, Category.assoc]⟩
  id_comp a := Subtype.ext (Category.id_comp a.val)
  comp_id a := Subtype.ext (Category.comp_id a.val)
  assoc a b c := Subtype.ext (Category.assoc a.val b.val c.val)

/-- The universal-curve projection forgets only the arbitrary section.
Source: Knudsen, A closer look, Introduction, `σ_n`
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev projection (S : Scheme.{u}) (g r : ℕ) :
    StablePointedUniversalCurve S g r ⥤ StablePointedModuli S g r where
  obj X := X.family
  map a := a.val

/-- Projection to schemes over the original base.
Source: Knudsen, A closer look, Introduction
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev forget (S : Scheme.{u}) (g r : ℕ) :
    StablePointedUniversalCurve S g r ⥤ Over S :=
  projection S g r ⋙ StablePointedModuli.forget S g r

/-- The universal-curve category as an actual category over schemes.
Source: Knudsen, A closer look, Introduction
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev based (S : Scheme.{u}) (g r : ℕ) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forget S g r)

end StablePointedUniversalCurve

namespace StablePointedModuli

/-- Stable moduli as a category over schemes, using the recorded cartesian arrows.
Source: Knudsen II §2 (blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev based (S : Scheme.{u}) (g r : ℕ) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forget S g r)

/-- The curve map between the two specified pullbacks along an arrow of test schemes.
Source: the scheme fibre-product universal property; Knudsen II §2
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def pullbackCurveMap {S : Scheme.{u}} {g r : ℕ} (X : StablePointedModuli S g r)
    {A B : Over S} {a : A ⟶ X.base} {b : B ⟶ X.base} (h : A ⟶ B) (w : h ≫ b = a) :
    (X.pullback A a).curve ⟶ (X.pullback B b).curve :=
  pullback.lift (pullback.fst X.projection a.left)
    (pullback.snd X.projection a.left ≫ h.left) (by
      rw [Category.assoc, ← Over.comp_left, w]
      exact pullback.condition)

/-- The canonical pullback map is cartesian and preserves each ordered marking.
Source: the scheme fibre-product universal property; Knudsen II §2
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve).
Proof: the two pullback squares defining the source and target have common first
projection. The universal property, or cancellation of the target square, gives the
cartesian square over `h`. The two projections of each marking equation agree by
the paired-section equations and `h ≫ b = a`; pullback uniqueness
therefore proves the marking equation. This includes empty bases and zero markings. -/
theorem pullbackCurveMap_properties {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedModuli S g r) {A B : Over S} {a : A ⟶ X.base} {b : B ⟶ X.base}
    (h : A ⟶ B) (w : h ≫ b = a) :
    IsPullback (pullbackCurveMap X h w) (X.pullback A a).projection
      (X.pullback B b).projection h.left ∧
    ∀ i : Fin r,
      (X.pullback A a).sections i ≫ pullbackCurveMap X h w =
        h.left ≫ (X.pullback B b).sections i := by
  sorry

/-- The map from the scheme `X.base`, as the recorded discrete moduli groupoid
`discreteModuli (yoneda.obj X.base)`, to moduli, classifying `X`. A test object is a
Yoneda map `h_A → h_{X.base}`, i.e. the arrow `yoneda.preimage A.hom`; it is sent to the
actual recorded fibre product along that arrow, with its paired markings.
Source: Knudsen, A closer look, Introduction, the displayed cartesian square
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev familyMap {S : Scheme.{u}} {g r : ℕ} (X : StablePointedModuli S g r) :
    BasedFunctor (discreteModuli (yoneda.obj X.base)) (based S g r) where
  obj A := X.pullback A.left (yoneda.preimage A.hom)
  map {A B} h :=
    have w : h.left ≫ yoneda.preimage B.hom = yoneda.preimage A.hom :=
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
        exact CostructuredArrow.w h)
    ⟨h.left, pullbackCurveMap X h.left w,
      (pullbackCurveMap_properties X h.left w).1, (pullbackCurveMap_properties X h.left w).2⟩
  map_id A := by
    refine StablePointedModuli.Hom.ext rfl ?_
    have hi : ∀ P : StablePointedModuli S g r, (𝟙 P : P ⟶ P).map = 𝟙 P.curve := fun _ ↦ rfl
    rw [hi]
    dsimp only
    apply pullback.hom_ext
    · simp [pullbackCurveMap]
    · simp only [pullbackCurveMap, pullback.lift_snd, Category.id_comp]
      rfl
  map_comp h k := by
    refine StablePointedModuli.Hom.ext rfl ?_
    have hc : ∀ {P Q R : StablePointedModuli S g r} (a : P ⟶ Q) (b : Q ⟶ R),
        (a ≫ b).map = a.map ≫ b.map := fun _ _ ↦ rfl
    rw [hc]
    dsimp only
    apply pullback.hom_ext
    · simp [pullbackCurveMap]
    · simp only [pullbackCurveMap, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc]
      rfl
  w := rfl

/-- The old family's total scheme, retaining its map to `S`.
Source: Knudsen II Corollary 2.6
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def totalScheme {S : Scheme.{u}} {g r : ℕ} (X : StablePointedModuli S g r) : Over S :=
  Over.mk (X.projection ≫ X.base.hom)

end StablePointedModuli

namespace StablePointedUniversalCurve

/-- The projection `C_{g,r} → Mbar_{g,r}` as a morphism over schemes.
Source: Knudsen, A closer look, Introduction, `σ_n`
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev basedProjection (S : Scheme.{u}) (g r : ℕ) :
    BasedFunctor (based S g r) (StablePointedModuli.based S g r) where
  toFunctor := projection S g r
  w := rfl

/-- The forgetful-and-stabilizing map attached to a contraction functor.
Source: Knudsen II Corollary 2.6, `π_{n+1} = σ_n c`
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
abbrev forgetful {S : Scheme.{u}} {g r : ℕ}
    (c : BasedFunctor (StablePointedModuli.based S g (r + 1)) (based S g r)) :
    BasedFunctor (StablePointedModuli.based S g (r + 1))
      (StablePointedModuli.based S g r) :=
  c.comp (basedProjection S g r)

/-- The specified comparison of a scheme-test object with its contracted family.
Source: Knudsen II Corollary 2.6, unwinding the 2-fibre product
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def comparisonIso {S : Scheme.{u}} {g r : ℕ}
    (c : BasedFunctor (StablePointedModuli.based S g (r + 1)) (based S g r))
    (X : StablePointedModuli S g r)
    (Z : (moduliTwoFiberProduct X.familyMap (forgetful c)).obj) :
    X.familyMap.obj Z.obj.left ≅ (forgetful c).obj Z.obj.right :=
  @asIso _ _ _ _ Z.obj.hom Z.property.1

/-- The represented point is the contracted extra section transported back by the
specified comparison, then projected from `X_U` to `X`. In particular the comparison
is retained, so automorphisms of `X` have not been quotiented out.
Source: Knudsen II Corollary 2.6; Knudsen, A closer look, Introduction
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def representedPoint {S : Scheme.{u}} {g r : ℕ}
    (c : BasedFunctor (StablePointedModuli.based S g (r + 1)) (based S g r))
    (X : StablePointedModuli S g r)
    (Z : (moduliTwoFiberProduct X.familyMap (forgetful c)).obj) :
    Z.obj.left.left.left ⟶ X.curve :=
  (comparisonIso c X Z).hom.base.left ≫ (c.obj Z.obj.right).extra ≫
    (comparisonIso c X Z).inv.map ≫
      (X.pullbackArrow Z.obj.left.left (yoneda.preimage Z.obj.left.hom)).map

/-- The contraction on a geometric fibre, formed by the actual scheme pullback map.
Source: Knudsen II §2, contraction and stabilization
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def fiberContraction {S : Scheme.{u}} {g r : ℕ}
    (Y : StablePointedModuli S g (r + 1)) (X : StablePointedUniversalCurve S g r)
    (b : Y.base.left ⟶ X.family.base.left) (q : Y.curve ⟶ X.family.curve)
    (hq : q ≫ X.family.projection = Y.projection ≫ b)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ Y.base.left) :
    pullback Y.projection a ⟶ pullback X.family.projection (a ≫ b) :=
  pullback.map Y.projection a X.family.projection (a ≫ b) q (𝟙 _) b
    hq.symm (by simp)

/-- The extra section on the specified geometric fibre of the contracted family.
Source: Knudsen II §2 (blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def fiberExtra {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedUniversalCurve S g r)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ X.family.base.left) :
    Spec (.of Ω) ⟶ pullback X.family.projection a :=
  X.family.projection.baseChangeSection X.extra X.extra_projection a

/-- A smooth extra point different from all the old markings on a geometric fibre.
Source: Knudsen II Definition 2.3 and Theorem 2.4
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def IsGoodExtra {S : Scheme.{u}} {g r : ℕ} (X : StablePointedUniversalCurve S g r)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ X.family.base.left) : Prop :=
  letI : LocallyOfFinitePresentation X.family.projection := X.family.stable.2.2.choose
  Set.range (fiberExtra X a) ⊆ (pullback.snd X.family.projection a).smoothLocus ∧
  ∀ i : Fin r, Disjoint (Set.range (fiberExtra X a))
    (Set.range (X.family.projection.baseChangeSection
      (X.family.sections i) (X.family.section_projection i) a))

/-- Fibrewise stabilization geometry: the map is unchanged off the extra point;
a good extra point needs no component, while a collision or node has precisely one
projective line over it. Since both curves are stable nodal labelled curves, these
are the inserted rational tail and bridge, respectively.
Source: Knudsen II Theorem 2.4; Knudsen, A closer look, §5
(blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve). -/
def HasFiberGeometry {S : Scheme.{u}} {g r : ℕ}
    (Y : StablePointedModuli S g (r + 1)) (X : StablePointedUniversalCurve S g r)
    (b : Y.base.left ⟶ X.family.base.left) (q : Y.curve ⟶ X.family.curve)
    (hq : q ≫ X.family.projection = Y.projection ≫ b) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ Y.base.left),
    (∀ U : (pullback X.family.projection (a ≫ b)).Opens,
      Disjoint (U : Set ↥(pullback (C := Scheme.{u}) X.family.projection (a ≫ b)))
        (Set.range (fiberExtra X (a ≫ b))) →
      IsIso (pullback.snd (fiberContraction Y X b q hq a) U.ι)) ∧
    (IsGoodExtra X (a ≫ b) → IsIso (fiberContraction Y X b q hq a)) ∧
    (¬ IsGoodExtra X (a ≫ b) →
      ∃ e : pullback (fiberContraction Y X b q hq a) (fiberExtra X (a ≫ b)) ≅
          ProjectiveLine (Spec (.of Ω)),
        e.hom ≫ (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) =
          pullback.snd (fiberContraction Y X b q hq a) (fiberExtra X (a ≫ b)))

end StablePointedUniversalCurve

/-- Contraction and stabilization are mutually inverse over schemes. The resulting
forgetful map is represented, over every ordered family `X`, by its total scheme.
The representing functor sends an actual 2-fibre-product object to the contracted
extra section, not just to an unrelated point with the same isomorphism class.

Source: Knudsen II §2, Corollary 2.6 and Theorem 2.7; Knudsen, A closer look,
Introduction and §5 (blueprint: lem-sfb-knudsen-pointed-forgetful-universal-curve).

Proof: First use the projective-bundle properness lemma, proper base change and
semistable marked base change to retain the stable convention under every pullback;
the component degrees of the log canonical module are positive and its section
algebra gives projectivity. For an `(r+1)`-pointed curve delete the last marking and
apply lem-sfb-log-canonical-deletion-algebra. Only the component containing that
marking can have degree zero. It is a smooth rational component: a self-nodal
rational component or a genus-one zero component would be the entire connected
fibre of genus one, excluded by `2 ≤ g`. The evaluation contraction gives the
`r`-pointed family and the image of the last marking, naturally in all cartesian
arrows. Conversely lem-sfb-section-ideal-proj-expansion inserts its specified
symmetric-Proj rational tail or bridge at a collision or node. Its three special
points give stability; the positive-degree log canonical lemma gives projectivity.
The contraction of this expansion is canonically the original curve with its extra
section, by uniqueness of the contraction. In the other direction apply
lem-sfb-elementary-contraction-evaluation, including its divisor twist, and the
projective-bundle quotient geometry to construct the canonical comparison. It is
an isomorphism on geometric fibres and hence globally by the universal-isomorphism
open lemma. This also proves uniqueness of arrows over a fixed contracted object.
These comparisons are natural under arbitrary base change and give the two
isomorphisms over schemes. In the 2-fibre product retain the comparison from `X_U`
to the contracted family and transport the extra section by its inverse. This is
`representedPoint`; the comparisons just constructed give the inverse on objects and
unique arrows, proving equivalence to the discrete groupoid `h_X` of maps into `X`.
The projection is `X.projection`, projective, flat and finitely presented by
stability. On smooth disjoint families the expansion projection is a fibrewise
isomorphism; the same universal-isomorphism open lemma makes it an isomorphism over
the whole base, with every old marking and the appended last marking preserved. -/
theorem exists_knudsen_pointed_forgetful_universal_curve (S : Scheme.{u})
    (g r : ℕ) (hg : 2 ≤ g) :
    ∃ (c : BasedFunctor (StablePointedModuli.based S g (r + 1))
          (StablePointedUniversalCurve.based S g r))
      (s : BasedFunctor (StablePointedUniversalCurve.based S g r)
          (StablePointedModuli.based S g (r + 1)))
      (η : ModuliTwoIso (BasedFunctor.id (StablePointedModuli.based S g (r + 1)))
          (c.comp s))
      (ε : ModuliTwoIso (s.comp c)
          (BasedFunctor.id (StablePointedUniversalCurve.based S g r)))
      (q : ∀ Y : StablePointedModuli S g (r + 1), Y.curve ⟶ (c.obj Y).family.curve)
      (hq : ∀ Y : StablePointedModuli S g (r + 1),
        q Y ≫ (c.obj Y).family.projection =
          Y.projection ≫ eqToHom (congrArg Over.left (c.w_obj Y).symm)),
      (∀ {Y Z : StablePointedModuli S g (r + 1)} (h : Y ⟶ Z),
        h.map ≫ q Z = q Y ≫ (c.map h).val.map) ∧
      (∀ (Y : StablePointedModuli S g (r + 1)) (i : Fin r),
        Y.sections i.castSucc ≫ q Y =
          eqToHom (congrArg Over.left (c.w_obj Y).symm) ≫ (c.obj Y).family.sections i) ∧
      (∀ Y : StablePointedModuli S g (r + 1),
        Y.sections (Fin.last r) ≫ q Y =
          eqToHom (congrArg Over.left (c.w_obj Y).symm) ≫ (c.obj Y).extra) ∧
      (∀ Y : StablePointedModuli S g (r + 1),
        StablePointedUniversalCurve.HasFiberGeometry Y (c.obj Y)
          (eqToHom (congrArg Over.left (c.w_obj Y).symm)) (q Y) (hq Y)) ∧
      (∀ X : StablePointedModuli S g r,
        ∃ R : BasedFunctor
            (moduliTwoFiberProduct X.familyMap (StablePointedUniversalCurve.forgetful c))
            (discreteModuli (yoneda.obj X.totalScheme)),
          R.toFunctor.IsEquivalence ∧
          (∀ Z, (yoneda.preimage (R.obj Z).hom).left =
            eqToHom (congrArg Over.left (R.w_obj Z)) ≫
              StablePointedUniversalCurve.representedPoint c X Z) ∧
          (∀ Z, (yoneda.preimage (R.obj Z).hom).left ≫ X.projection =
            eqToHom (congrArg Over.left (R.w_obj Z)) ≫
              (yoneda.preimage Z.obj.left.hom).left) ∧
          IsProjectiveBundle X.projection ∧ Flat X.projection ∧
            LocallyOfFinitePresentation X.projection ∧ QuasiCompact X.projection ∧
            QuasiSeparated X.projection) ∧
      (∀ X : StablePointedUniversalCurve S g r,
        Smooth X.family.projection →
        (∀ i : Fin r, Disjoint (Set.range X.extra) (Set.range (X.family.sections i))) →
        IsIso (q (s.obj X) ≫ (ε.val.hom.app X).val.map)) ∧
      (∀ (X : StablePointedModuli S g r) (T : Over S) (a : T ⟶ X.base),
        IsStablePointedCurve (X.pullback T a).projection (X.pullback T a).sections
          (X.pullback T a).section_projection) := by
  sorry

end AlgebraicGeometry
