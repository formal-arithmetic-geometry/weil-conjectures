/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralBasicOperationShift
public import Sheaf.Paper.ShiftedTensorMorphismCalculus
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Shift squares for the primitive strict-system comparisons

Source: main-20261015, sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md,
maps-used sentence; Stacks 0FNG and 0FPT
(blueprint: lem-pur-system-primitive-comparison-shift).

Only the explicitly listed primitive maps are indexed below. Slot contexts merely
specify their sources, targets and the already published cochain shift comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Inclusion of the published flat-term resolving category into all K-flat complexes.
Source: Stacks 06YU (blueprint: lem-pur-system-primitive-comparison-shift). -/
def primitiveResolvingInclusion (W : Scheme.{u}) :
    (SheafOfModules.shiftedTensorResolving.{u + 1, u}
      (coefficientSequenceCommRingSheaf l E W)).FullSubcategory ⥤
    ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W)) where
  obj P := ⟨P.obj, P.property.1⟩
  map f := ⟨f.hom⟩

/-- Restrict the existing K-flat presentation to its flat-term resolving subcategory.
No new tensor is chosen. Source: Stacks 06YU and 0FNG
(blueprint: lem-pur-system-primitive-comparison-shift). -/
def primitiveTensorModel (W : Scheme.{u}) :
    SheafOfModules.ShiftedTensorModel.{u + 1, u, u + 2}
      (coefficientSequenceCommRingSheaf l E W) where
  tensor := (calculus l E W).systemClosed.tensor
  representative := by
    exact Functor.isoWhiskerLeft
      ((primitiveResolvingInclusion l E W).prod (primitiveResolvingInclusion l E W))
      (calculus l E W).systemTensorModel.comparison

/-- The published derived Koszul symmetry on this very system tensor presentation.
Source: Stacks 0FNG, 0FPT (blueprint: lem-pur-system-primitive-comparison-shift). -/
def primitiveSystemSymmetry (W : Scheme.{u}) :=
  SheafOfModules.derivedTensorSymmetry (coefficientSequenceCommRingSheaf l E W)
    (primitiveTensorModel l E W)

/-- Finite-type schemes over the fixed geometric field, as a full subcategory of Over.
Source: blueprint fix-prop-coherence, maps-used sentence
(blueprint: lem-pur-system-primitive-comparison-shift). -/
abbrev PrimitiveSystemScheme (D : FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (fun W : Over (Spec (.of D.k)) ↦
    LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom)

/-- The separated finite-type condition on the arrows in the primitive list.
Source: blueprint fix-prop-coherence, maps-used sentence
(blueprint: lem-pur-system-primitive-comparison-shift). -/
def PrimitiveSystemArrow {B : Scheme.{u}} {U V : Over B} (f : U ⟶ V) : Prop :=
  IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left

/-- Restriction of extension along k=s b to b is extension along s. The inverse open
unit fixes the section normalization. Source: Stacks 0F7B, 03DI
(blueprint: lem-pur-system-primitive-comparison-shift). -/
def primitiveSystemRestriction (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U V W : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k] (h : s ≫ b = k) :
    Operations.shriek l E o k ⋙ pull l E b ≅ Operations.shriek l E o s :=
  Functor.isoWhiskerRight
    ((c.openComp l E s b) ≪≫ openCongr l E o h).symm (pull l E b) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (Operations.shriek l E o s) (a.unit l E o c b).symm ≪≫
  Functor.rightUnitor _

/-- The intrinsic clopen component projection in the realization presentation, obtained
from the actual direct-image unit and the inverse open-to-direct-image comparison.
Source: Stacks 09AE; lem-sf-semilinear-proper-open-mate-pasting, pi
(blueprint: lem-pur-system-primitive-comparison-shift). -/
def primitiveSystemProjection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {U V : Scheme.{u}} (s : U ⟶ V)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (System l E V) ⟶ pull l E s ⋙ Operations.shriek l E o s :=
  (o.direct s).adj.unit ≫ Functor.whiskerLeft (pull l E s) (a.clopen s).inv

/-- The finite list of primitive comparison families, indexed by their actual maps.
Each tensor constructor selects exactly one input occurrence. There is no constructor
for arbitrary maps, outer contexts, projection formula or exchange.
Source: blueprint fix-prop-coherence, maps-used sentence; Stacks 0FNG and 0FPT
(blueprint: lem-pur-system-primitive-comparison-shift). -/
inductive PrimitiveSystemComparison (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) :
    {A W : PrimitiveSystemScheme D} →
    (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj) →
    (∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M) → Prop where
  | pullComp {U V W : PrimitiveSystemScheme D} (f : U.obj ⟶ V.obj)
      (g : V.obj ⟶ W.obj) (_hf : PrimitiveSystemArrow f) (_hg : PrimitiveSystemArrow g) :
    PrimitiveSystemComparison D o c a (.pull (f ≫ g) .input)
      (.pull f (.pull g .input)) (fun M ↦ (c.pullComp f.left g.left).hom.app M)
  | square {U V W Z : PrimitiveSystemScheme D}
      (k : U.obj ⟶ V.obj) (r : U.obj ⟶ W.obj)
      (p : V.obj ⟶ Z.obj) (i : W.obj ⟶ Z.obj)
      (_hk : PrimitiveSystemArrow k) (_hr : PrimitiveSystemArrow r)
      (_hp : PrimitiveSystemArrow p) (_hi : PrimitiveSystemArrow i)
      (h : k.left ≫ p.left = r.left ≫ i.left) :
    PrimitiveSystemComparison D o c a (.pull r (.pull i .input))
      (.pull k (.pull p .input)) (fun M ↦ (c.square l E k.left r.left p.left i.left h).hom.app M)
  | tensorPullLeft {U V : PrimitiveSystemScheme D} (f : U.obj ⟶ V.obj)
      (_hf : PrimitiveSystemArrow f) (N : System l E V.obj.left) :
    PrimitiveSystemComparison D o c a (.pull f (.tensorLeft .input N))
      (.tensorLeft (.pull f .input) ((pull l E f.left).obj N))
      (fun M ↦ (pullbackTensorSystemComparison l E f.left).hom.app (M, N))
  | tensorPullRight {U V : PrimitiveSystemScheme D} (f : U.obj ⟶ V.obj)
      (_hf : PrimitiveSystemArrow f) (M : System l E V.obj.left) :
    PrimitiveSystemComparison D o c a (.pull f (.tensorRight M .input))
      (.tensorRight ((pull l E f.left).obj M) (.pull f .input))
      (fun N ↦ (pullbackTensorSystemComparison l E f.left).hom.app (M, N))
  | assocFirst {W : PrimitiveSystemScheme D} (N L : System l E W.obj.left) :
    PrimitiveSystemComparison D o c a (.tensorLeft (.tensorLeft .input N) L)
      (.tensorLeft .input ((calculus l E W.obj.left).systemClosed.tensor.obj (N, L)))
      (fun M ↦ ((calculus l E W.obj.left).systemClosed.monoidal.associator M N L).hom)
  | assocMiddle {W : PrimitiveSystemScheme D} (M L : System l E W.obj.left) :
    PrimitiveSystemComparison D o c a (.tensorLeft (.tensorRight M .input) L)
      (.tensorRight M (.tensorLeft .input L))
      (fun N ↦ ((calculus l E W.obj.left).systemClosed.monoidal.associator M N L).hom)
  | assocLast {W : PrimitiveSystemScheme D} (M N : System l E W.obj.left) :
    PrimitiveSystemComparison D o c a
      (.tensorRight ((calculus l E W.obj.left).systemClosed.tensor.obj (M, N)) .input)
      (.tensorRight M (.tensorRight N .input))
      (fun L ↦ ((calculus l E W.obj.left).systemClosed.monoidal.associator M N L).hom)
  | leftUnitor {W : PrimitiveSystemScheme D} :
    PrimitiveSystemComparison D o c a
      (.tensorRight (calculus l E W.obj.left).systemClosed.monoidal.tensorUnit .input) .input
      (fun M ↦ ((calculus l E W.obj.left).systemClosed.monoidal.leftUnitor M).hom)
  | rightUnitor {W : PrimitiveSystemScheme D} :
    PrimitiveSystemComparison D o c a
      (.tensorLeft .input (calculus l E W.obj.left).systemClosed.monoidal.tensorUnit) .input
      (fun M ↦ ((calculus l E W.obj.left).systemClosed.monoidal.rightUnitor M).hom)
  | symmetryLeft {W : PrimitiveSystemScheme D} (N : System l E W.obj.left) :
    PrimitiveSystemComparison D o c a (.tensorLeft .input N) (.tensorRight N .input)
      (fun M ↦ (primitiveSystemSymmetry l E W.obj.left).hom.app (M, N))
  | symmetryRight {W : PrimitiveSystemScheme D} (M : System l E W.obj.left) :
    PrimitiveSystemComparison D o c a (.tensorRight M .input) (.tensorLeft .input M)
      (fun N ↦ (primitiveSystemSymmetry l E W.obj.left).hom.app (M, N))
  | openComp {U V W : PrimitiveSystemScheme D} (j : U.obj ⟶ V.obj)
      (k : V.obj ⟶ W.obj) [hj : IsOpenImmersion j.left] [hk : IsOpenImmersion k.left]
      (qj : QuasiCompact j.left) (qk : QuasiCompact k.left)
      (qjk : QuasiCompact (j ≫ k).left) :
    PrimitiveSystemComparison D o c a (.shriek k hk qk (.shriek j hj qj .input))
      (.shriek (j ≫ k) (inferInstance : IsOpenImmersion (j.left ≫ k.left)) qjk .input)
      (fun M ↦ (c.openComp l E j.left k.left).hom.app M)
  | restriction {U V W : PrimitiveSystemScheme D} (s : U.obj ⟶ V.obj)
      (b : V.obj ⟶ W.obj) (k : U.obj ⟶ W.obj)
      [hs : IsOpenImmersion s.left] [IsOpenImmersion b.left] [hk : IsOpenImmersion k.left]
      (qs : QuasiCompact s.left) (_qb : QuasiCompact b.left) (qk : QuasiCompact k.left)
      (h : s.left ≫ b.left = k.left) :
    PrimitiveSystemComparison D o c a (.pull b (.shriek k hk qk .input))
      (.shriek s hs qs .input)
      (fun M ↦ (primitiveSystemRestriction l E o c a s.left b.left k.left h).hom.app M)
  | clopen {U V : PrimitiveSystemScheme D} (s : U.obj ⟶ V.obj)
      [hs : IsOpenImmersion s.left] [IsClosedImmersion s.left]
      (qs : QuasiCompact s.left) (hp : IsProper s.left) :
    PrimitiveSystemComparison D o c a (.shriek s hs qs .input) (.push s hp .input)
      (fun M ↦ (a.clopen s.left).hom.app M)
  | projection {U V : PrimitiveSystemScheme D} (s : U.obj ⟶ V.obj)
      [hs : IsOpenImmersion s.left] [IsClosedImmersion s.left] (qs : QuasiCompact s.left) :
    PrimitiveSystemComparison D o c a .input (.shriek s hs qs (.pull s .input))
      (fun M ↦ (primitiveSystemProjection l E o c a s.left).app M)

/-- Every listed primitive map commutes with the published slotwise system shifts.
Source: main-20261015, fix-prop-coherence.proof.md, maps-used sentence;
Stacks 0FNG, 0FPT (blueprint: lem-pur-system-primitive-comparison-shift).

Proof:
1. Work on the simultaneous ringed diagram sites of
lem-sf-integral-compactification-system-realization. Pullback compositors and
scheme-square identifications are induced by degree-zero resolution maps.
Reindexing and the shift differential sign commute with these maps, including
all quotient-linear transitions. Use the fixed shifts of
lem-pur-integral-basic-operation-shift, not comparisons chosen from the endpoints.
2. On K-flat models the pullback/tensor map preserves bidegrees (p,q).
The factor (-1)^(bp) in t_(a,b) is therefore the same on both routes, in either
slot. Apply lem-pur-shifted-tensor-morphism-calculus and descend the equality.
3. Reassociation and unit insertion/removal are degree-zero total-complex maps.
For symmetry follow the shifted occurrence to the permuted slot. The two sign
exponents differ by 2bp; the two-shift formula includes (-1)^(ab). With only one
slot shifted this is exactly the displayed square, without an extra scalar.
The same signed tensor calculus descends all three associator slots and both unitors.
4. Open extension is exact termwise extension by zero. Its compositor is identity
on the composite open and zero outside; shift does not change that map. The
normalizations are those of lem-sf-open-tensor-normalization, also on diagram sites.
5. The restriction identification is the inverse open compositor, equality transport
for k=s b, and the inverse open unit. All are degree-zero section identifications;
reindexing gives the same maps. The open unit is identity on the localized sections.
6. For clopen s, split into s(U) and its open complement. The comparison J_s to S_s
is identity on the first component, and the component projection is (x,y) to (x,0).
Shift preserves both components, identity and zero, so both squares commute with
systemPushShift's adjunction-mate normalization. These are the intrinsic maps of
lem-sf-semilinear-proper-open-mate-pasting, transported by its canonical bridge.
7. Each equation holds inside the derived system category before evaluation or
scalar restriction, since the calculations use the same simultaneous models.
Naturality is inherited from the canonical maps and their published shift
comparisons. No faithfulness of evaluation is used. -/
theorem systemPrimitiveComparisonShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
    {A W : PrimitiveSystemScheme D}
    (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj)
    (τ : ∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M)
    (_hτ : PrimitiveSystemComparison l E D o c a e t τ)
    (M : System l E A.obj.left) (r : ℤ) :
    τ (M⟦r⟧) ≫ (t.shift (systemShifts l E o) r M).hom =
      (e.shift (systemShifts l E o) r M).hom ≫ (τ M)⟦r⟧' := by
  sorry

end WeilConjectures.IntegralSystemRealization
