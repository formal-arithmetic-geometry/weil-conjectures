/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceDivisorDefinitions
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations

/-! # Local equations and normalized pullback of divisors and rational sections

Source: Stacks Project, Spaces Divisors, Tags 0EN9, 0EN7 and 0EPQ;
Divisors, Tags 0BE3 and 0AGA (blueprint: def-sfb-space-divisor-operations).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The actual scheme over the base underlying a small affine étale basis object.
Source: Stacks, Tag 03ED (blueprint: def-sfb-space-divisor-operations). -/
abbrev divisorBasisChart (X : AlgebraicSpace S) (U : X.SmallEtaleModel) : Over S :=
  (X.smallEtaleInclusion.obj U).obj.left

/-- Fractions as meromorphic sheaf sections, via the sheafification unit.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-divisor-operations). -/
def divisorFractionValue (X : AlgebraicSpace S) (U : X.SmallEtaleModel) :
    chartTotalFractionRing X U →+* (spaceTotalFractionSheaf X).obj.obj (op U) :=
  ((toSheafify X.smallEtaleModelTopology (spaceTotalFractionPresheaf X)).app (op U)).hom

/-- Unit fractions as meromorphic units on the same chart.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-divisor-operations). -/
def divisorFractionUnit (X : AlgebraicSpace S) (U : X.SmallEtaleModel) :=
  Units.map (divisorFractionValue X U).toMonoidHom

/-- The normalized valuation of a chart fraction, computed by lengths in the local DVR.
The value is length(O_y/(a)) minus length(O_y/(b)) for an actual a/b presentation.
Source: Stacks, Tags 02MD and 0BE3 (blueprint: def-sfb-space-divisor-operations). -/
def divisorChartOrder (X : AlgebraicSpace S) (U : X.SmallEtaleModel)
    (y : (divisorBasisChart X U).left) (g : chartTotalFractionRing X U) : ℤ :=
  ((Ring.ord ((divisorBasisChart X U).left.presheaf.stalk y)
    ((divisorBasisChart X U).left.presheaf.germ ⊤ y trivial
      (IsLocalization.sec (nonZeroDivisors (fractionChartRing X U)) g).1)).toNat : ℤ) -
  ((Ring.ord ((divisorBasisChart X U).left.presheaf.stalk y)
    ((divisorBasisChart X U).left.presheaf.germ ⊤ y trivial
      (IsLocalization.sec (nonZeroDivisors (fractionChartRing X U)) g).2.val)).toNat : ℤ)

/-- The Weil divisor attached to Cartier equations has precisely their local DVR orders.
Every chart and every local equation is tested, so this is a normalized order map.
Source: Stacks, Tags 0BE3 and 0AGA (blueprint: def-sfb-space-divisor-operations). -/
def SpaceCartierDivisor.HasWeilDivisor (X : AlgebraicSpace S)
    (D : SpaceCartierDivisor X) (W : SpaceWeilDivisor X) : Prop :=
  ∀ (U : X.SmallEtaleModel) (g : (chartTotalFractionRing X U)ˣ),
    SpaceCartierDivisor.HasEquation X D U (divisorFractionUnit X U g) →
    ∀ (y : (divisorBasisChart X U).left)
      (hy : ringKrullDim ((divisorBasisChart X U).left.presheaf.stalk y) = 1),
      W ⟨schemePointMap (X.smallEtaleInclusion.obj U).obj.hom y,
        ⟨X.smallEtaleInclusion.obj U, y, rfl, hy⟩⟩ = divisorChartOrder X U y g.val

/-- The associated rationally trivialized line is the inverse-equation subsheaf of K.
The embedding sends a local regular frame to g⁻¹, while s=g e; thus s maps to 1.
This records the sign convention and the actual local construction, rather than merely
an abstract isomorphism class.
Source: Stacks, Tag 0AGA and Spaces Divisors, Tag 0EN7
(blueprint: def-sfb-space-divisor-operations). -/
def SpaceCartierDivisor.IsAssociated (X : AlgebraicSpace S)
    (D : SpaceCartierDivisor X) (L : X.Modules) (s : SpaceRationalSection X L) : Prop :=
  ∃ i : X.smallModuleRestriction.obj L ⟶
      (SheafOfModules.restrictScalars (spaceToTotalFractions X)).obj
        (SheafOfModules.unit (spaceTotalFractionRings X)),
    Mono i ∧ ∀ U : X.SmallEtaleModel,
      ∃ R : Sieve U, R ∈ X.smallEtaleModelTopology U ∧
        ∀ (V : X.SmallEtaleModel) (f : V ⟶ U), R f →
          ∃ (g : (spaceTotalFractionSheaf X |>.obj.obj (op V))ˣ)
            (e : SheafOfModules.unit (X.smallStructureRings.over V) ≅
              (SheafOfModules.overFunctor X.smallStructureRings V).obj
                (X.smallModuleRestriction.obj L)),
            SpaceCartierDivisor.HasEquation X D V g ∧
            s.value X V = (g.val : (spaceTotalFractionRings X).obj.obj (op V)) •
              spaceLocalizeSection X (X.smallModuleRestriction.obj L) V
                (e.hom.val.app (op (Over.mk (𝟙 V)))
                  (1 : X.smallStructureRings.obj.obj (op V))) ∧
            i.val.app (op V) (e.hom.val.app (op (Over.mk (𝟙 V)))
              (1 : X.smallStructureRings.obj.obj (op V))) = g.inv

/-- A compatible map between the actual affine étale scheme charts of a space map.
Source: Stacks, Tag 03M8 (blueprint: def-sfb-space-divisor-operations). -/
def DivisorChartOver (q : X ⟶ Y) (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V) : Prop :=
  (X.smallEtaleInclusion.obj U).obj.hom ≫ q.hom.hom =
    yoneda.map h ≫ (Y.smallEtaleInclusion.obj V).obj.hom

/-- The actual pullback homomorphism of affine coordinate rings.
Source: Stacks, Tag 03G7 (blueprint: def-sfb-space-divisor-operations). -/
def divisorChartScalar (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V) :
    fractionChartRing Y V →+* fractionChartRing X U :=
  (Scheme.Γ.map h.left.op).hom

/-- Flat compatible chart maps preserve non-zero-divisors of the coordinate rings.
Source: Stacks, Tag 0EN9 (blueprint: def-sfb-space-divisor-operations).
Proof: the chart definition of flatness gives flatness of h. Tensoring the injection
A→A given by multiplication by a regular element with the flat algebra B shows that
its image remains a non-zero-divisor. The empty target chart is included. -/
theorem divisorChart_nonZeroDivisors (q : X ⟶ Y) (hq : MapIsFlat q)
    (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V) (hh : DivisorChartOver q U V h) :
    nonZeroDivisors (fractionChartRing Y V) ≤
      (nonZeroDivisors (fractionChartRing X U)).comap (divisorChartScalar U V h) := by
  sorry

/-- Pullback of a fraction is the homomorphism a/b ↦ q(a)/q(b).
Source: Stacks, Tag 0EN9 (blueprint: def-sfb-space-divisor-operations). -/
def divisorChartPullback (q : X ⟶ Y) (hq : MapIsFlat q)
    (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V) (hh : DivisorChartOver q U V h) :
    chartTotalFractionRing Y V →+* chartTotalFractionRing X U :=
  IsLocalization.map (chartTotalFractionRing X U) (divisorChartScalar U V h)
    (divisorChart_nonZeroDivisors q hq U V h hh)

/-- Cartier pullback is prescribed by pullback of every local unit equation.
It does not use cycle pullback with a relative dimension assumption.
Source: Stacks, Tag 0EN9 (blueprint: def-sfb-space-divisor-operations). -/
def SpaceCartierDivisor.IsFlatPullback (q : X ⟶ Y) (hq : MapIsFlat q)
    (D : SpaceCartierDivisor Y) (E : SpaceCartierDivisor X) : Prop :=
  ∀ (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V)
    (hh : DivisorChartOver q U V h) (g : (chartTotalFractionRing Y V)ˣ),
    SpaceCartierDivisor.HasEquation Y D V (divisorFractionUnit Y V g) →
      SpaceCartierDivisor.HasEquation X E U (divisorFractionUnit X U
        (Units.map (divisorChartPullback q hq U V h hh).toMonoidHom g))

/-- Local tensor of a regular section along the given chart triangle.
Source: Stacks, Tags 03LV and 0EN9 (blueprint: def-sfb-space-divisor-operations). -/
def divisorPullbackRegularSection (q : X ⟶ Y)
    (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V)
    (hh : DivisorChartOver q U V h) (L : Y.Modules)
    (m : (Y.smallModuleRestriction.obj L).val.obj (op V)) :
    (X.smallModuleRestriction.obj ((moduleTensorPullback q).obj L)).val.obj (op U) :=
  moduleTensorSection q L (Y.smallEtaleInclusion.obj V)
    (CostructuredArrow.mk (Y := X.smallEtaleInclusion.obj U)
      (CostructuredArrow.homMk h hh.symm)) 1 m

/-- Pullback of a rational generator is specified on local tensors:
if s=(a/b)e in a regular frame, its pullback is (q(a)/q(b))(1⊗e).
This retains the actual tensor-pullback functor and its fixed adjunction unit.
Source: Stacks, Tag 0EN9 and lemma-meromorphic-sections-pullback
(blueprint: def-sfb-space-divisor-operations). -/
def SpaceRationalSection.IsFlatPullback (q : X ⟶ Y) (hq : MapIsFlat q)
    {L : Y.Modules} (s : SpaceRationalSection Y L)
    (t : SpaceRationalSection X ((moduleTensorPullback q).obj L)) : Prop :=
  ∀ (U : X.SmallEtaleModel) (V : Y.SmallEtaleModel)
    (h : divisorBasisChart X U ⟶ divisorBasisChart Y V)
    (hh : DivisorChartOver q U V h) (g : (chartTotalFractionRing Y V)ˣ)
    (e : SheafOfModules.unit (Y.smallStructureRings.over V) ≅
      (SheafOfModules.overFunctor Y.smallStructureRings V).obj
        (Y.smallModuleRestriction.obj L)),
    s.value Y V = ((divisorFractionUnit Y V g).val :
      (spaceTotalFractionRings Y).obj.obj (op V)) •
        spaceLocalizeSection Y (Y.smallModuleRestriction.obj L) V
          (e.hom.val.app (op (Over.mk (𝟙 V)))
            (1 : Y.smallStructureRings.obj.obj (op V))) →
    t.value X U = ((divisorFractionUnit X U
      (Units.map (divisorChartPullback q hq U V h hh).toMonoidHom g)).val :
        (spaceTotalFractionRings X).obj.obj (op U)) •
      spaceLocalizeSection X
        (X.smallModuleRestriction.obj ((moduleTensorPullback q).obj L)) U
        (divisorPullbackRegularSection q U V h hh L
          (e.hom.val.app (op (Over.mk (𝟙 V)))
            (1 : Y.smallStructureRings.obj.obj (op V))))

end AlgebraicGeometry.AlgebraicSpace
