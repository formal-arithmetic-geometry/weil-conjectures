## What changed

Replaced the item's sole sorry by a strong support-dimension induction and a complete
boundary-presentation/composition argument, keeping its theorem statement and every public
import unchanged. Added two public induction reductions, each in its own module:
`FlatteningSmoothAffineReduction` and `FlatteningSmoothSupportInduction`.

The first reduction uses etale devissage to replace general modules of fibre-support
dimension < d by affine smooth geometrically integral families of relative dimension n < d.
The second uses generic-rank reduction and universally exact free subtraction to reduce a
smooth family of relative dimension n to arbitrary modules of fibre-support dimension < n.
The main proof combines them by `Nat.strong_induction_on`, including d = 0. The existing
uniform scheme-fibre dimension bound starts the induction with d + 1.

The final argument is implemented in the item: restrict the strict-transform quotient over
the preserved open, transport finite presentation through the open-square pullback comparison,
apply the existing boundary-presentation theorem, construct admissible data for the composite
centre using its support formula, and transport flatness and finite presentation back across
the calculus's two isomorphisms. Private helpers prove the finite-type ideal conversion,
presentation preservation on the open, and transport across an isomorphism square.
No data definition is chosen from an unproved existence theorem.

Read Stacks `flat.tex` theorem-flatten-module (Tag 0815), its complete proof, and
lemma-flatten-module-etale-localize (Tag 0814), and checked the tag table. Read all ten
current parent proof dependencies and their Lean signatures, including the four 2026-10-24
assembly helpers missing from the old item's imports. LeanFinder/Loogle/grep found no
existing full flattening theorem; separate LeanSearch/LeanFinder/grep searches for both
new induction reductions are logged and copied into their nodes. The closest existing
project lemmas give the geometric transfer and free-sequence data, not the quantified
induction reductions. Read the current blueprint locality node and its unit: these changes
stay within the existing 0815 tool branch and change no unit statement or step.

Validation: both new theorem modules compiled cleanly through `lcompile.py --all`
(20.5 s and 21.9 s); the complete main item then compiled cleanly through `lcompile.py`
(34.5 s). All files are under 60 s. Checked unchanged original theorem signature and
public imports, unchanged parent DAG statement and statement dependencies, all line widths,
new-node Lean statements against their files, and every dependency reference. No other
existing module or node changed, so no downstream interface adaptation is required.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup`.
There are zero sorry tokens left in the item. All three private helpers are proved.

Added two holes, both genuine parts of the support-dimension induction:

- `AlgebraicGeometry.Scheme.Modules.exists_flat_moduleStrictTransform_of_smooth_affine`
  (`lem-trf-flattening-smooth-affine-reduction`). It proves the general-to-smooth etale
  reduction under an explicit universal smooth-family premise, with a strict dimension bound.
- `AlgebraicGeometry.Scheme.Modules.exists_flat_moduleStrictTransform_smooth_of_lower_support`
  (`lem-trf-flattening-smooth-support-induction`). It treats only affine smooth geometrically
  integral families and assumes the smaller-support assertion, used on the generic-rank
  reduction cokernels.

This is a decomposition, not a sorry-free proof: one old hole closed, two new holes added,
net -1 holes. The main theorem's induction and boundary/composition assembly are complete
Lean proofs from these and the existing declared dependencies. The new reductions do not
assert finite presentation after blowup, and neither is the original theorem renamed.

Edge cases: d = 0 in the first reduction has an empty range of smooth premises and all
fibre supports empty; n = 0 in the second uses the d = 0 hypothesis for its zero cokernels.
Zero rank, empty affine charts, empty schemes, U empty and U equal to S are allowed.
No assumption of a nonempty support, positive dimension, Noetherian base or nonzero rank
was introduced. The bound is a strict inequality in `WithBot ℕ∞`, so empty support is bottom.

## No longer needed

Removed the following direct proof imports from the item. Their lower arguments still
needed by the reductions remain imported there through the existing supporting statements;
removal of a direct import alone is not claimed as pruning its module:

- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType`
- `Mathlib.RingTheory.FiniteStability`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
- `Mathlib.RingTheory.FinitePresentation`
- `Mathlib.RingTheory.Finiteness.ModuleFinitePresentation`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Mathlib.RingTheory.Smooth.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.RingTheory.Unramified.Basic`
- `Mathlib.RingTheory.Unramified.Finite`
- `WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `WeilConjectures.AlgebraicGeometry.DimensionBaseChange`
- `Mathlib.RingTheory.Spectrum.Prime.Chevalley`
- `WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel`
- `Sheaf.AlgebraicGeometry.GenericFreeBlowup`
- `Sheaf.AlgebraicGeometry.ModuleStrictTransformAffinePushforward`
- `Sheaf.AlgebraicGeometry.ModuleStrictTransformUniversalExact`
- `Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Sheaf.RingTheory.FreeSubtractionFlatness`
- `Sheaf.TraceFormula.ElementaryModuleDevissage`
- `Sheaf.TraceFormula.EtaleFlatteningDescent`
- `Sheaf.TraceFormula.FlatFiniteTypeDensePresentation`
- `Sheaf.Paper.DerivedHomMayerVietoris`

The following seven modules leave this item's import closure after these changes (this is
local pruning, with no claim that another target or consumer stops using them). No source
module or declaration is withdrawn or edited:

- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `WeilConjectures.AlgebraicGeometry.BaseChangeField`
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`
- `WeilConjectures.AlgebraicGeometry.Dimension`
- `WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover`
- `WeilConjectures.AlgebraicGeometry.DimensionBaseChange`
- `WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers`

Corresponding node attachments no longer used by this item:

- `def-pc-curve` (`WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`)
- `def-pc-dimension` (`WeilConjectures.AlgebraicGeometry.Dimension`)
- `def-pc-smooth-projective-curve` (`WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`)
- `def-weil-unramified-morphism` (`Sheaf.AlgebraicGeometry.UnramifiedMorphism`)
- `lem-pc-dim-base-change` (`WeilConjectures.AlgebraicGeometry.DimensionBaseChange`)
- `lem-pc-dim-base-change-affine-covers` (`WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers`)
- `lem-pc-dimension-affine-open-cover` (`WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover`)
- `lem-pc-scheme-dimension-local-rings` (`WeilConjectures.AlgebraicGeometry.Dimension`)

The parent's proof dependencies now name the two reductions, the fibre bound, the actual
boundary/composition lemmas and the finite-presentation/relative-flatness transport APIs.
The old generic-free, devissage, pushforward, free-subtraction and universal-exactness
arguments remain required below the reductions; they were not mathematically bypassed.
Removed obsolete parent `tool_uses` entries (their previous approvals are unnecessary at
this assembly node; no approval was added or reordered):

- `lem-weil-pbc-support-pullback-finite-type`
- `lem-pc-f3-finite-pushforward-finite-type`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `sbc-lem-smooth-criterion`
- `lem-weil-pbc-finite-presentation-over-finite-type-algebra`
- `lem-weil-pbc-finite-algebra-presentation-module-presentation`
- `lem-pc-module-finite-presentation-transitive`
- `lem-weil-pbc-etale-algebra-flat`
- `def-weil-etale-morphism`
- `def-weil-unramified-morphism`
- `lem-weil-pbc-formally-unramified-ring-iff-kahler-zero`
- `lem-sc-unramified-flat-of-base-flat`
- `lem-pc-affine-chart-relative-flat-criterion`
- `lem-pc-proper-base-change`
- `lem-pc-dim-base-change`
- `lem-weil-pbc-flat-finite-presentation-open`
- `lem-weil-pbc-module-finite-presentation-cokernel`
- `det-nagata-boundary-divisor-cartier`
- `lemma-nagata-qc-open-complement-ideal-exists`

## Where the brief, the DAG or earlier work was wrong

The assigned Lean file still described the old thirteen-step plan and imported its entire
lower argument, while the current DAG has a five-step assembly using devissage transfer,
smooth generic-rank reduction, free-sequence transform flatness and boundary presentation.
The new proof follows the current DAG and makes its induction quantifiers and strict bounds
explicit. The old docstring is retained as source documentation; the updated node describes
the actual Lean proof. No theorem statement or underlying mathematical definition changed.

The latest blueprint locality text has evolved beyond the inherited semistable-alteration
prose in this branch's ancestry. This delivery does not withdraw or reroute that branch;
it carries out the currently assigned module-flattening argument below it.

A read-only DAG cycle audit encountered the pre-existing cycle
`prop-nagata-relative-proj-functoriality` → `lem-nagata-affine-proj-scalar-extension` →
`prop-nagata-relative-proj-functoriality` below the blowup definitions. Both edges are
already present in the shared baseline. No existing dependency of either new reduction
reaches this item or either new reduction; the delivery introduces no such cycle.
This unrelated metadata issue was not changed in the packet.

## New nodes

`lem-trf-flattening-smooth-affine-reduction`, in
`dag/nodes/sec-trace-formula/lem-trf-flattening-smooth-affine-reduction.json`, records the
etale devissage reduction, including zero-support neighbourhoods and empty-source diagrams
needed to cover the base. It cites the existing devissage, finite-type support and etale
descent declarations, and has the same chapter/unit as the item.

`lem-trf-flattening-smooth-support-induction`, in
`dag/nodes/sec-trace-formula/lem-trf-flattening-smooth-support-induction.json`, records the
smooth-family induction step using the existing generic-rank, free-sequence and blowup
calculus declarations. Its universal lower-support hypothesis is precisely the strong
induction hypothesis supplied by the parent. Both new nodes retain the inherited blueprint
ancestor and identify their exact paragraphs of Stacks 0815. No change record is needed:
only the item's proof, its node, and the two new theorem modules and nodes changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
