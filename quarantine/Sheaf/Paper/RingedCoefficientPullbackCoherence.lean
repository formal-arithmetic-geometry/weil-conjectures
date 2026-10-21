/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData

/-! # Normalized coefficient comparisons for inverse image

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) pY)
  (nX : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := K) pX)
  (e : Comparisons g nY nX)

/-- The balanced comparison square and scalar unit equation for inverse image.
These involve only left functors, before taking any direct-image mates.
Source: Stacks 0D6D (blueprint: lem-pur-coefficient-pullback-coherence). -/
structure PullbackCoherence (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) : Prop where
  composition : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (N : D J R),
    (g.left T).map ((nY.derived a b).hom.app N) ≫ (e.derived (a ≫ b)).hom.app N =
      (e.derived b).hom.app ((pY a).derived.obj N) ≫
        (pX (g.rings.map b)).derived.map ((e.derived a).hom.app N) ≫
        (targetAssociator g nX a b).hom.app ((g.left R).obj N)
  unit : ∀ (R : Sheaf J CommRingCat.{r}) (N : D J R),
    (e.derived (𝟙 R)).hom.app N ≫
        (eqToIso (congrArg (fun f ↦ (pX f).derived) (g.rings.map_id R)) ≪≫
          uX.derived (g.rings.obj R)).hom.app ((g.left R).obj N) =
      (g.left R).map ((uY.derived R).hom.app N)

/-- Counit-normalized scalar shifts and shift compatibility of the inverse-image
comparisons, balanced associators, and scalar units, before taking mates.
Source: Stacks 07A6; signed cochain calculation for degree-zero scalar factors
(blueprint: lem-pur-coefficient-pullback-coherence). -/
structure PullbackShifts (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX)) where
  [scalarY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S), (pX a).derived.CommShift ℤ]
  canonicalY : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pY a).counit ℤ
  canonicalX : ∀ {R S : Sheaf K CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (pX a).counit ℤ
  inverseScalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (e.derived a).hom ℤ
  associatorY : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nY.derived a b).hom ℤ
  associatorX : ∀ {R S T : Sheaf K CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    NatTrans.CommShift (nX.derived a b).hom ℤ
  unitY : ∀ R : Sheaf J CommRingCat.{r}, NatTrans.CommShift (uY.derived R).hom ℤ
  unitX : ∀ R : Sheaf K CommRingCat.{r}, NatTrans.CommShift (uX.derived R).hom ℤ

variable (uY : ScalarUnits (p := pY)) (uX : ScalarUnits (p := pX))

/-- The canonical pullback comparisons respect scalar composition and multiplication
units. This is a coherence assertion about already constructed tensor comparisons;
it asserts no projection mate law.

Source: Stacks Project, Cohomology on Sites, Tag 0D6D
(lemma-derived-pullback-composition); the explicit balanced tensor calculation
in its proof
(blueprint: lem-pur-coefficient-pullback-coherence).

Proof:
1. Compute all functors on a common flat-term K-flat representative P. The
canonical computation maps in the two coefficient normalizations are invertible
there. Pullback preserves K-flat flat-term representatives, so its computation
may use the same P and its inverse-image complex.
2. The ordinary comparison is pinned by scalar insertion. Tensor balancing and
sheafification uniqueness imply that it is the inverse-image balanced tensor
map. On a double tensor, both composites with the recorded scalar associators
send t tensor (s tensor x) to b(s)t tensor x. Thus they are equal chain maps.
The representative equations for e and n identify this equality with the
composition equation. Cancel the invertible computation maps and use a K-flat
resolution of each derived object to obtain PullbackCoherence.composition.
3. The two ordinary scalar unitors are multiplication, by ScalarUnits.multiplication.
The insertion-normalized comparison for an identity coefficient map has the
same multiplication equation. Transport this equality through the representative
formulas of e and the units and cancel the computation maps. This proves
PullbackCoherence.unit, including the rings.map_id transport.
The source and target unit identifications are multiplication, rather than
arbitrary choices of an equivalence with the identity. No projection-mate law
is included in this left tensor square. -/
theorem coefficientPullbackCoherence [PreservesFiniteLimits uInv] :
    PullbackCoherence g nY nX e uY uX := by
  sorry

end SheafOfModules.RingedCoefficientProjection
