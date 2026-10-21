/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.Paper.GlobalGeometricFrobenius

/-! # Canonical compact-cohomology comparison for constant extension

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-p-dl-general-relative-line/lem-zl-affine-curve-hc2-purity.proof.md,
second paragraph (blueprint: def-zl-constant-extension-compact-comparison).

The comparison is normalized before cohomology by the whole-system proper/open mates,
then by literal rational localization and the prescribed common-stage realization.
Existence of the normalized package is part of weil_constant_extension_frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open FrobeniusExchange CategoryTheory.Functor

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-normalized pullback compositor for a general square.
Source: blueprint cited paragraph; Stacks 0D6D
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionSystemSquare {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : a ≫ f = f' ≫ b) :
    integralComparisonDerivedSequencePullback l E b ⋙
        integralComparisonDerivedSequencePullback l E f' ≅
      integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequencePullback l E a :=
  (integralComparisonSystemComposition l E f' b).symm ≪≫
    eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) w.symm) ≪≫
      integralComparisonSystemComposition l E a f

/-- The inverse open comparison is exactly the left adjunction mate.
Source: blueprint cited paragraph; SGA 4 XVII, 5--6
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionSystemOpenInv {X X' B B' : Scheme.{u}}
    (j : X ⟶ B) (j' : X' ⟶ B') [IsOpenImmersion j] [IsOpenImmersion j']
    (a : X' ⟶ X) (b : B' ⟶ B) (w : a ≫ j = j' ≫ b) :
    integralComparisonDerivedSequencePullback l E a ⋙ systemDerivedOpen l E j' ⟶
      systemDerivedOpen l E j ⋙ integralComparisonDerivedSequencePullback l E b :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j)
    (systemDerivedOpenAdjunction l E j')).symm
      (TwoSquare.mk _ _ _ _ (constantExtensionSystemSquare l E j j' a b w).inv)).natTrans

/-- Proper exchange is the right mate, with the prescribed point identity unitor.
Source: blueprint cited paragraph; SGA 4 XVII, 5--6
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionSystemProper {B B' S : Scheme.{u}}
    (p : B ⟶ S) (p' : B' ⟶ S) (b : B' ⟶ B) (w : b ≫ p = p') :
    systemDirect l E p ⟶
      integralComparisonDerivedSequencePullback l E b ⋙ systemDirect l E p' :=
  whiskerLeft (systemDirect l E p) (integralComparisonSystemUnit l E S).inv ≫
    (mateEquiv (systemAdjunction l E p) (systemAdjunction l E p')
      (TwoSquare.mk _ _ _ _
        (constantExtensionSystemSquare l E p p' b (𝟙 S)
          (w.trans (Category.comp_id p').symm)).hom)).natTrans

/-- The actual proper/open composite, formed before taking total inverse limits.
Source: blueprint cited paragraph; SGA 4 XVII, 5--6
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionSystemCompact {X X' S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (c : Compactification f) (c' : Compactification f')
    (a : X' ⟶ X) (b : c'.Z ⟶ c.Z)
    (wp : b ≫ c.g = c'.g) (wj : a ≫ c.i = c'.i ≫ b)
    (h : IsIso (constantExtensionSystemOpenInv l E c.i c'.i a b wj)) :
    systemDerivedOpen l E c.i ⋙ systemDirect l E c.g ⟶
      integralComparisonDerivedSequencePullback l E a ⋙
        (systemDerivedOpen l E c'.i ⋙ systemDirect l E c'.g) :=
  whiskerLeft (systemDerivedOpen l E c.i)
      (constantExtensionSystemProper l E c.g c'.g b wp) ≫
    whiskerRight (@asIso _ _ _ _
      (constantExtensionSystemOpenInv l E c.i c'.i a b wj) h).inv
      (systemDirect l E c'.g)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The existing integral operation with its uniquely projection-normalized realization.
Source: blueprint cited paragraph; Bhatt--Scholze 6.7.6
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionIntegralRecipe (c : Compactification X₀.hom) :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  letI : (D.geometricFiber X₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  (sfCompactSupportFiniteIntegralFunctor l D.k (zlClosurePrimeUnit D l hl)
      (frobeniusCohomologyCompactification D X₀ c) E,
    compactRealization l E D.k (zlClosurePrimeUnit D l hl) (D.geometricFiber X₀).hom
      (frobeniusCohomologyCompactification D X₀ c))

variable (e : ℕ) (he : 1 ≤ e)

/-- The retained compactification after actual finite constant base change.
Source: blueprint cited paragraph
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionModelCompactification (c : Compactification X₀.hom) :
    Compactification (constantExtensionModel D e he X₀).hom :=
  c.baseChange (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))

/-- Separatedness follows from the base-change instance, without an extra assumption.
Source: blueprint cited paragraph
(blueprint: def-zl-constant-extension-compact-comparison). -/
instance constantExtensionModelSeparated :
    IsSeparated (constantExtensionModel D e he X₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))))

/-- The geometric middle map of the retained compactifications.
Source: blueprint cited paragraph, associativity of base change
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionCompactMiddle (c : Compactification X₀.hom) :=
  letI : IsProper c.g := c.isProper
  letI : IsSeparated
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c).hom :=
    inferInstanceAs (IsSeparated (c.g ≫ 𝟙 _))
  (constantExtensionFiberIso D e he
    (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X₀) c)).hom

/-- A normalized proper/open comparison at a finite integral coefficient field.
The two commutativities and the inverse open mate are retained as proof fields,
so the arrow is constructed before rationalization and is never arbitrary.
Source: blueprint cited paragraph; SGA 4 XVII, 5--6
(blueprint: def-zl-constant-extension-compact-comparison). -/
structure ConstantExtensionIntegralComparison (c : Compactification X₀.hom) where
  /-- Commutativity of the proper square over the identical Spec k. -/
  proper_square : constantExtensionCompactMiddle D X₀ e he c ≫
      (frobeniusCohomologyCompactification D X₀ c).g =
    (frobeniusCohomologyCompactification (constantExtensionDatum D e he)
      (constantExtensionModel D e he X₀)
      (constantExtensionModelCompactification D X₀ e he c)).g
  /-- Commutativity of the canonical open square. -/
  open_square : (constantExtensionFiberIso D e he X₀).hom ≫
      (frobeniusCohomologyCompactification D X₀ c).i =
    (frobeniusCohomologyCompactification (constantExtensionDatum D e he)
      (constantExtensionModel D e he X₀)
      (constantExtensionModelCompactification D X₀ e he c)).i ≫
      constantExtensionCompactMiddle D X₀ e he c
  /-- The open comparison is inverted with this proof, not replaced by an input map. -/
  open_isIso : IsIso (constantExtensionSystemOpenInv l E
    (frobeniusCohomologyCompactification D X₀ c).i
    (frobeniusCohomologyCompactification (constantExtensionDatum D e he)
      (constantExtensionModel D e he X₀)
      (constantExtensionModelCompactification D X₀ e he c)).i
    (constantExtensionFiberIso D e he X₀).hom
    (constantExtensionCompactMiddle D X₀ e he c) open_square)

/-- The specified integral arrow, obtained from the actual proper/open system mate,
its reduction counit, and the projection-normalized realization of compact support.
Source: blueprint cited paragraph; Stacks 099N, 0941
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionIntegralComparisonMap (c : Compactification X₀.hom)
    (P : ConstantExtensionIntegralComparison l E D X₀ e he c)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    ((constantExtensionIntegralRecipe l E D hl X₀ c).1.obj K).obj ⟶
      ((constantExtensionIntegralRecipe l E (constantExtensionDatum D e he) hl
        (constantExtensionModel D e he X₀)
        (constantExtensionModelCompactification D X₀ e he c)).1.obj
          ((@constructibleIntegralPullback l _ E _ _ _ _ _
            (constantExtensionFiberIso D e he X₀).hom
            (sfWeilPrimeInvertible (constantExtensionDatum D e he) l hl
              (constantExtensionModel D e he X₀))
            (sfWeilPrimeInvertible D l hl X₀)).obj K)).obj := by
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible (constantExtensionDatum D e he) l hl
    (constantExtensionModel D e he X₀)
  let a := (constantExtensionFiberIso D e he X₀).hom
  let c' := constantExtensionModelCompactification D X₀ e he c
  let g := frobeniusCohomologyCompactification D X₀ c
  let g' := frobeniusCohomologyCompactification (constantExtensionDatum D e he)
    (constantExtensionModel D e he X₀) c'
  let H' := systemDerivedOpen l E g'.i ⋙ systemDirect l E g'.g
  let β := integralComparisonPullbackCounit l E a
    ((models l E).system (D.geometricFiber X₀).left)
    ((models l E).system ((constantExtensionDatum D e he).geometricFiber
      (constantExtensionModel D e he X₀)).left)
    ((models l E).roos _) ((models l E).pullback a)
  letI : IsIso (β.app K.obj) := (models l E).effective a K
  exact (constantExtensionIntegralRecipe l E D hl X₀ c).2.hom.app K ≫
    (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((constantExtensionSystemCompact l E g g' a
        (constantExtensionCompactMiddle D X₀ e he c)
        P.proper_square P.open_square P.open_isIso).app
        ((reduction l E (D.geometricFiber X₀).left).obj K.obj)) ≫
    (H' ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).map (asIso (β.app K.obj)).inv ≫
    (constantExtensionIntegralRecipe l E (constantExtensionDatum D e he) hl
      (constantExtensionModel D e he X₀) c').2.inv.app
        ((constructibleIntegralPullback l E a).obj K)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Realization of integral coefficients at the geometric point, using exactly the
published rational point fibre and the canonical small-coefficient embedding.
Source: blueprint cited paragraph and Deligne, Weil II (1.1.14)
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionPointRealization (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (Spec (.of D.k)) ⥤
      @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _) :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (Spec (.of D.k)) ⋙
    pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) ⋙
    (DerivedCategory.pointFiniteDimensional
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).ι ⋙
    frobeniusCohomologyCoefficientExtension.{u, v}
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)

/-- Source integral value in the specified coefficient realization.
Source: blueprint cited paragraph
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionComparisonSource (c : Compactification X₀.hom)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :=
  (constantExtensionPointRealization l D hl Ω M.stage).obj
    ((constantExtensionIntegralRecipe l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage) D hl X₀ c).1.obj M.obj.obj)

/-- Target integral value, with actual inverse image along the fibre isomorphism.
Source: blueprint cited paragraph
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionComparisonTarget (c : Compactification X₀.hom)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :=
  (constantExtensionPointRealization l D hl Ω M.stage).obj
    ((constantExtensionIntegralRecipe l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      (constantExtensionDatum D e he) hl (constantExtensionModel D e he X₀)
      (constantExtensionModelCompactification D X₀ e he c)).1.obj
        ((@constructibleIntegralPullback l _
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage) _ _ _ _ _
          (constantExtensionFiberIso D e he X₀).hom
          (sfWeilPrimeInvertible (constantExtensionDatum D e he) l hl
            (constantExtensionModel D e he X₀))
          (sfWeilPrimeInvertible D l hl X₀)).obj M.obj.obj))

/-- Literal rationalization and coefficient realization of the specified integral map.
Source: blueprint cited paragraph; Deligne, Weil II (1.1.14)
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionRealizedComparisonMap (c : Compactification X₀.hom)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      ConstantExtensionIntegralComparison l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D X₀ e he c)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    constantExtensionComparisonSource l D hl X₀ Ω c M ⟶
      constantExtensionComparisonTarget l D hl X₀ e he Ω c M :=
  (constantExtensionPointRealization l D hl Ω M.stage).map
    (ObjectProperty.homMk (constantExtensionIntegralComparisonMap l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      D hl X₀ e he c (P M.stage) M.obj.obj))

/-- The canonical coefficient comparison is fixed by its actual integral proper/open
mate on every object's own representative. The endpoint equalities are the published
object formulas, including the literal rational pullback formula and the identity
comparison at Spec k. They are proof fields, not arbitrary maps or automorphisms.
Source: blueprint cited paragraph; Deligne, Weil II (1.1.14)
(blueprint: def-zl-constant-extension-compact-comparison). -/
structure ConstantExtensionCompactComparison (c : Compactification X₀.hom) where
  /-- The canonical integral construction at every finite coefficient stage. -/
  integral : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ConstantExtensionIntegralComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D X₀ e he c
  /-- Underlying compact-coefficient comparison induced by the fibre isomorphism. -/
  comparison : frobeniusCohomologyQbarFunctor D l hl X₀ Ω c true ≅
    constantExtensionFiberPull D e he X₀ l hl Ω ⋙
      frobeniusCohomologyQbarFunctor (constantExtensionDatum D e he) l hl
        (constantExtensionModel D e he X₀) Ω
        (constantExtensionModelCompactification D X₀ e he c) true
  /-- Exact source object formula at the retained representative. -/
  source_eq : ∀ M, (frobeniusCohomologyQbarFunctor D l hl X₀ Ω c true).obj M =
    constantExtensionComparisonSource l D hl X₀ Ω c M
  /-- Exact target formula, including the normalized identity point comparison. -/
  target_eq : ∀ M,
    (frobeniusCohomologyQbarFunctor (constantExtensionDatum D e he) l hl
      (constantExtensionModel D e he X₀) Ω
      (constantExtensionModelCompactification D X₀ e he c) true).obj
        ((constantExtensionFiberPull D e he X₀ l hl Ω).obj M) =
      constantExtensionComparisonTarget l D hl X₀ e he Ω c M
  /-- This equation fixes every comparison arrow to the canonical constructed map. -/
  normalization : ∀ M, comparison.hom.app M =
    eqToHom (source_eq M) ≫
      constantExtensionRealizedComparisonMap l D hl X₀ e he Ω c integral M ≫
      eqToHom (target_eq M).symm

/-- The coefficient-cohomology identification induced by the canonical fibre map
and the very underlying-object isomorphism retained by the restriction specification.
It contains no choice of a cohomology map and no Frobenius equation in its data.
Source: blueprint cited paragraph, identity on the common geometric fibre
(blueprint: def-zl-constant-extension-compact-comparison). -/
def constantExtensionCompactCohomologyComparison (c : Compactification X₀.hom)
    (C : ConstantExtensionCompactComparison l D hl X₀ e he Ω c)
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D e he) l hl
        (constantExtensionModel D e he X₀) Ω)
    (hR : ConstantExtensionRestrictionSpec D e he X₀ l hl Ω R)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) (r : ℤ) :
    (globalGeometricFrobeniusQbarCohomology D l hl X₀ Ω c F.obj true r).a ≅
      (globalGeometricFrobeniusQbarCohomology (constantExtensionDatum D e he) l hl
        (constantExtensionModel D e he X₀) Ω
        (constantExtensionModelCompactification D X₀ e he c) (R.obj F).obj true r).a :=
  (@DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) _ _
    (HasDerivedCategory.standard _) r).mapIso
      (C.comparison.app F.obj.carrier ≪≫
        (frobeniusCohomologyQbarFunctor (constantExtensionDatum D e he) l hl
          (constantExtensionModel D e he X₀) Ω
          (constantExtensionModelCompactification D X₀ e he c) true).mapIso
            ((Classical.choose hR).app F).symm)

end WeilConjectures
