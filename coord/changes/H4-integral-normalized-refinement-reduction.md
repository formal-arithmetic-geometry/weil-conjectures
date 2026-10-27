# WeilConjectures.IntegralSystemRealization.integralNormalizedRefinementPasting

## Reason

Separate the existing normalized-refinement constructions from their final theorem so that
its missing reverse-map realization step is an independently provable module. The ten data
declarations below move verbatim to IntegralNormalizedRefinementData and are publicly
reexported by the item. Their names, types, bodies and instance status are unchanged.
The final theorem's complete signature is unchanged. No target definition or statement changes.
A declaration-scoped `linter.unusedVariables false` suppresses the warning for the
original lambda index used only implicitly by typeclass inference; it has no logical
or downstream elaboration effect.
No existing module other than the claimed item is edited.

The current server queue lists a proof item with one hole. Its old rework/build-error record
is a historical upstream-import quarantine; the present source and its original single-file
compile are available and clean apart from that hole.

## Old

The item imported:

```lean
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility
public import Sheaf.SixFunctors.CompletedShriekCompositionLaws
public import Sheaf.SixFunctors.AmbientProperOpenPasting
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
public import Sheaf.SixFunctors.GeneratorReductionStatement
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
```

These declarations lived in the item:

```lean
/-- The one-input compactification word B_c=S_p J_j, with its actual scheme indices.
Source: blueprint extracted normalized coefficient argument, step 10
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def normalizedRefinementWord {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    (c : Compactification f.left) : Expression B (ULift.{u} Unit) (fun _ ↦ X) Y :=
  .compactSupport f c (.var ⟨()⟩)

/-- The finite-type geometric proof for the actual one-input compactification word.
Source: blueprint step 10, finite-type domain
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
abbrev normalizedRefinementGeometric {B : Scheme.{u}} {X Y : Over B}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) : (normalizedRefinementWord f c).geometric :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, True.intro⟩

/-- The inverse of the existing reverse system refinement, wherever it is invertible.
The total inverse-or-zero convention is the recorded GeneratorReduction convention;
the theorem below asserts invertibility, so its zero branch is never used there.
Source: blueprint step 10, inversion of intrinsic system pasting
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def normalizedRefinementSystemMap {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (M : System l E X) :
    (completedShriekF l E o c).obj M ⟶ (completedShriekF l E o d).obj M :=
  GeneratorReduction.inverseOrZero ((completedShriekRefinement l E R r).app M)

/-- Finite outer proper/open factors in a refinement diagram, retaining their order.
This is notation for the whiskering clause, not additional geometric data.
Source: blueprint step 10; Stacks 0F7C, 0F7D
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
inductive NormalizedRefinementContext (B : Scheme.{u}) (V : Over B) : Over B →
    Type (u + 1) where
  | hole : NormalizedRefinementContext B V V
  | push {U W : Over B} (f : U ⟶ W) (hf : IsProper f.left)
      (q : NormalizedRefinementContext B V U) : NormalizedRefinementContext B V W
  | shriek {U W : Over B} (j : U ⟶ W) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) (q : NormalizedRefinementContext B V U) :
      NormalizedRefinementContext B V W

/-- Substitute the compactification expression into the same outer proper/open word.
Source: blueprint step 10, permitted whiskering
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.plug {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W) {I : Type u} {X : I → Over B}
    (e : Expression B I X V) : Expression B I X W :=
  match q with
  | .hole => e
  | .push f hf q => .push f hf (q.plug e)
  | .shriek j hj hq q => .shriek j hj hq (q.plug e)

/-- Interpret the outside factors as the actual composite functor in either calculus.
Source: blueprint step 10, whiskering before evaluation
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.evaluate {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W)
    {C : Scheme.{u} → Type v} [∀ T, Category.{w} (C T)]
    (d : Interpretation C) : C V.left ⥤ C W.left :=
  match q with
  | .hole => 𝟭 _
  | .push f _ q => q.evaluate d ⋙ d.push f.left
  | .shriek j hj _ q =>
    letI := hj
    q.evaluate d ⋙ d.shriek j.left

/-- Canonical associators identify substitution with application of the outer functor.
Source: blueprint step 10, identical outside factors
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.evaluationIso {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W)
    {C : Scheme.{u} → Type v} [∀ T, Category.{w} (C T)] (d : Interpretation C)
    {I : Type u} {X : I → Over B} (e : Expression B I X V) :
    (q.plug e).evaluate d ≅ e.evaluate d ⋙ q.evaluate d :=
  match q with
  | .hole => (Functor.rightUnitor (e.evaluate d)).symm
  | .push f _ q =>
    Functor.isoWhiskerRight (q.evaluationIso d e) (d.push f.left) ≪≫
      Functor.associator _ _ _
  | .shriek j hj _ q =>
    letI := hj
    Functor.isoWhiskerRight (q.evaluationIso d e) (d.shriek j.left) ≪≫
      Functor.associator _ _ _

/-- The prescribed realization in outside-factor coordinates, using only associators.
Source: blueprint step 10, whiskered realization
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.realization {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {V W : Over (Spec (CommRingCat.of D.k))}
    (q : NormalizedRefinementContext _ V W) (e : Expression _ I X V)
    (g : (q.plug e).geometric) (K : ∀ i, Integral l E (X i).left)
    (h : (q.plug e).domain l E o K) :
    (coefficientSequenceLimit l E W.left).obj
        ((q.evaluate (systemInterpretation l E o)).obj
          (e.systemObj l E o ((inputReduction l E X).obj K))) ≅
      (q.evaluate (integralInterpretation l E)).obj
        ((e.evaluate (integralInterpretation l E)).obj K) :=
  ((coefficientSequenceLimit l E W.left).mapIso
    ((q.evaluationIso (systemInterpretation l E o) e).app
      ((inputReduction l E X).obj K))).symm ≪≫
    (R.comparison (q.plug e) g).app ⟨K, h⟩ ≪≫
    (q.evaluationIso (integralInterpretation l E) e).app K

/-- Transport the bundled finite-type structure to the same typeclass structure map.
Source: blueprint finite-type convention
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
instance normalizedRefinementFiniteType {B : Scheme.{u}} (X : Over B)
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (X.left ↘ B) :=
  inferInstanceAs (LocallyOfFiniteType X.hom)

/-- Transport quasi-compactness to the same bundled structure morphism.
Source: blueprint finite-type convention
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
instance normalizedRefinementQuasiCompact {B : Scheme.{u}} (X : Over B)
    [QuasiCompact X.hom] : QuasiCompact (X.left ↘ B) :=
  inferInstanceAs (QuasiCompact X.hom)

```

The final theorem's proof was `by sorry`.

## New

The item imports:

```lean
public import Sheaf.SixFunctors.IntegralNormalizedRefinementData
public import Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility
public import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SixFunctors.IntegralRefinementTransposeRealization
```

IntegralNormalizedRefinementData publicly imports CompletedShriekCompositionLaws and
GeneratorReductionData and contains exactly the definitions printed above, verbatim.
IntegralRefinementTransposeRealization publicly imports that data and the existing
IntegralRefinementDiagramAdmissibility; its one named theorem compares only an actual
reverse refinement with the normalized integral proper/open mate, including outside factors.
It contains no auxiliary compact-support functors, rho or r, and no identity or composition
conclusion. This is original proof step 2 together with its realization-whiskering clause.

The item's proof now explicitly inverts that square, proves the forward system identity
and composition equations from completedShriekRefinementLaws, transports them through total
limit, cancels realization and compact-support isomorphisms, and uses faithfulness and
extensionality to recover the actual integral laws. The final outside-factor equality is
proved by the same inversion followed by the supplied rho normalization.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | H4 | Same public names and theorem signature; data reexported; proof reduced. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementData | H4, new | Owns the ten unchanged data declarations. |
| Sheaf.SixFunctors.IntegralRefinementTransposeRealization | H4, new | Uses only the extracted data and existing diagram domains. |
| Sheaf.Paper.IntegralNormalizedRingRefinementLaws | unclaimed in snapshot | DAG parent only; it does not yet import the item; unchanged interface remains available. |

An exact import search in both lean/ and quarantine/ found no current direct importer of
the item. No additional existing Lean module requires an adaptation. All moved declarations
remain accessible by importing the original module. The new comparison deliberately has
no absolute separatedness hypothesis and no finite-evaluation detection hypothesis.

## Status

landed 20261027T180638-L-3885595 2026-10-27 (merge of deliver/H4/Sheaf.SixFunctors.IntegralNormalizedRefinementPasting)
