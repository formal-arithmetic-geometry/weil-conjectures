## What changed

Filled `AlgebraicGeometry.ProEtale.SpCompositionFactors.tower_orientation_evaluation`
without changing its signature or any existing definition. The proof uses the supplied
purity records directly. It proves invertibility of the actual rho by cancelling the
invertible tensor-orientation factor from `af.purity_iso` at omega_g. It extracts the
three finite orientation records from their `finite_levels` fields, using the source
library's identity for the single/unit comparison.

Private proved helpers paste word-comparison squares and transport them through
pullback. The separate `TensorWordComparison` intermediate theorem supplies the
remaining tensor transport square. The site tensor calculation is natural in both variables; it
uses the actual derived tensor comparison, rather than choosing endpoint maps.
The splitting composed with tensor of the two given orientation isomorphisms gives
an isomorphism to W. Homology and evaluation transport concentration and local rank
along it. Both reduction squares are applications of the given calculus's reduction
naturality to the inverse-realization image of the actual morphism.

Added four modules with remaining public intermediate theorems and their own DAG nodes:
`TowerTateSplitNormalized`, `TowerMuEvaluation`, `OrderedTateTowerCohomology`, and
`TensorWordComparison`.
The main proof composes the mu square with H's orientation square for Phi, and the
pullback/tensor orientation square with the normalized splitting square for Psi.
The proof locally prioritizes the source's cached derived-category instances and
keeps the large derived-functor implementations irreducible during elaboration.
The instance priorities and irreducibility settings are local. The header also
disables the generic essentially-small sheafification candidate and the two diagonal
Abelian instances, matching the supplied level-word definitions. No source-library
instance or definition is edited.
All new imports in the item are private proof imports. No shared module or target
statement was changed. The original unit's orientation/tensor-comparison route is kept.

The additional module `TowerOrientationWordNormalization` proves the unit-normalization
step with no holes. Profiling found the full extraction proof alone took about 48 s;
its categorical word-change and unit calculation are now checked independently.
The item extracts the finite data and invokes that proved lemma. The remaining
tensor-word square was attempted by pasting site naturality, tc.derived naturality,
tensor of the input squares, and tensorEvaluation naturality. Concrete and generic
versions exceeded the checking limit despite cached instances, local irreducibility,
minimal imports and a separate-module attempt. Its true, smaller conclusion is
therefore stated as the fourth intermediate theorem; no checking limit is raised.

Validation: all six packet modules compiled successfully together through
`lcompile.py --all` (result `1980335e37bfebc1ac229a9d`, exit code 0), including
the complete main assembly against the actual intermediate declarations. A text
audit verifies all seven original public definitions/structure and the target
theorem signature are unchanged. Node dependency unions and new Lean signatures
match; no Lean line exceeds 100 characters. Delivery preflight runs next.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpCompositionFactors.tower_orientation_evaluation`
(node `lem-sp-tower-orientation-evaluation`). Its proof is an assembly from strictly
smaller statements, so this delivery is a decomposition, not a sorry-free proof of
the complete mathematical result.

The proved helper `AlgebraicGeometry.ProEtale.SpCompositionFactors.
tower_orientation_word_normalized` adds no hole.

Added these four holes, and no others:

- `AlgebraicGeometry.ProEtale.SpCompositionFactors.tower_tate_split_normalized`
  (`lem-sp-tower-tate-split-normalized`): construction of the normalized shifted Tate
  splitting alone; no orientation composite, concentration, or mu evaluation.
- `AlgebraicGeometry.ProEtale.SpCompositionFactors.tower_mu_evaluation`
  (`lem-sp-tower-mu-evaluation`): finite evaluation of mu before composing with the
  h orientation; no splitting, concentration, or Psi assertion.
- `AlgebraicGeometry.ProEtale.SpCompositionFactors.ordered_tate_tower_cohomology`
  (`lem-sp-ordered-tate-tower-cohomology`): cohomology and finite local rank of a
  single ordered coefficient line, independent of all exceptional compositors.

- `AlgebraicGeometry.ProEtale.SpCompositionFactors.tensor_word_comparison`
  (`lem-sp-tensor-word-comparison`): tensor functoriality for arbitrary pairs of
  finite level-word squares, independent of purity and exceptional-composition data.

Original item: 1 hole closed out of 1; 0 holes left in the item. New modules: 4 holes.
Packet total: 1 original hole replaced by 4 smaller holes (net holes closed minus
added = -3 before any independent downstream pruning). Every remaining hole is the
entire proof of its named public theorem, with its source and complete proof in words.
No definition contains a hole or selects an arbitrary witness from an unproved theorem.

## No longer needed

Removed the item's following direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: no smoothness-of-composition instance
  is constructed in the assembly; the three purity records are already supplied.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing`: its finite tensor invertibility and
  scalar orientation work belongs to the mu sublemma, not the assembly.
- `Sheaf.Paper.TwistedPullbackTowerDomain`: `af.tensor_mem` and `af.projection_iso`
  already supply the required witnesses.
- `Sheaf.Paper.TowerTensorTransposeEvaluation`: the remaining mu lemma contains this
  comparison argument; the assembly only composes its square.
- `Sheaf.Paper.SemilinearDerivedSections`: used to construct the splitting, which is
  now a separate obligation.
- `Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels`: the coherent even-shift
  splitting is isolated in the normalized splitting lemma.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: the splitting lemma owns the
  root/Tate pullback calculation.
- `Sheaf.Paper.PurTwistSheafLocallyFree`: the line cohomology and splitting lemmas own
  the local freeness and flatness calculations.

The parent node no longer directly calls `det-sp-tower-gamma` or `det-sp-tower-gluing`:
its hypotheses contain their Purity and adjunction-level data. It does not directly
use `lem-sbc-smooth-relative-dimension-permanence` or
`lem-weil-pbc-proper-fp-permanence`, since it constructs no new h purity record.
`lem-sp-twisted-pullback-tower-domain` is unnecessary for its rho argument: the given
purity record already has the tensor-domain, projection-isomorphism and gamma fields.

The original direct proof dependencies `det-sp-finite-general-ring`,
`lem-sp-tower-tensor-transpose-evaluation`, and `det-sp-composition-comparisons` move
into the mu lemma. `lem-coef-semilinear-derived-sections`,
`lem-pur-diagram-pullback-monoidal-shift-models`, and
`lem-asd-etale-finite-twist-pullback` move into the splitting lemma.
`def-coefficient-twists-detailed` and `lem-pur-twist-sheaf-locally-free` remain needed
by the splitting and cohomology lemmas; `det-sp-coefficient-towers-abelian` remains
needed by the cohomology lemma. These nodes are retained as dependencies there.

Removed the parent node's obsolete top-level `tool_uses` entries for the twelve
old tool citations: relative-dimension permanence, tower-gamma, tower-gluing,
finite-general-ring, twisted-pullback-tower-domain, tensor-transpose-evaluation,
semilinear-derived-sections, coefficient twists, diagram-pullback shift models,
finite-twist-pullback, coefficient-towers-abelian and twist-sheaf-locally-free.
Their mathematical work is either already in the hypotheses or retained in the
new statements as detailed above.

No module or node is withdrawn. Existing public imports and source-library declarations
are retained, so this is not a claim that their entire modules leave the targets'
import closure. The new cohomology module imports gamma data directly and does not
import the composition theorem.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original plan unnecessarily
reconstructs facts already present as fields of the three supplied purity records.
Its unit coefficient convention also needs the explicit source-library identity
`Etale.singleFunctorObjUnitIso_inv` when passing from `targetWord` to `dualizingWord`.
This is a proof-normalization detail; no statement or definition was repaired.

The statements include d=e=0 and r=0 (coefficient units and tensor unitors), n=0
(the positive exponent is n+1), empty schemes (vacuous local rank assertions), and
ramified E (ell-power quotients, not an unramified coefficient assumption).
No equality of arbitrary derived tower maps is inferred from their evaluations.

A read-only dependency check also found an existing cycle outside this packet:
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent` cite each other. Neither node is
changed here. None of the new dependencies reaches the parent orientation node.

## New nodes

`lem-sp-tower-tate-split-normalized`, in
`lean/Sheaf/Paper/TowerTateSplitNormalized.lean`, isolates step 4: a shifted Tate
splitting and exactly its prescribed finite comparison. Its proof in words constructs
the strict-system isomorphism from root pullback, tensor associativity and the coherent
even-shift models, including quotient transitions and zero-fold unitors.

`lem-sp-tower-mu-evaluation`, in `lean/Sheaf/Paper/TowerMuEvaluation.lean`, isolates
step 3 before any diagonal orientation is composed into mu. Its proof in words uses
tensor-transpose evaluation, uniqueness under the given composite-counit equation,
finite composition comparisons, and functoriality of inverses.

`lem-sp-ordered-tate-tower-cohomology`, in
`lean/Sheaf/Paper/OrderedTateTowerCohomology.lean`, isolates the coefficient-line part
of step 6. Its proof in words uses locally free finite Tate lines, levelwise exactness,
and induction on the ordered tensor, with the ramification-indexed coefficient levels.

`lem-sp-tower-orientation-word-normalization`, in
`lean/Sheaf/Paper/TowerOrientationWordNormalization.lean`, is a proved conversion
from the retained targetWord orientation square to the exact dualizingWord square.
It preserves both endpoint invertibilities and uses the source single/unit identity.
It adds no mathematical assumption and no hole.

`lem-sp-tensor-word-comparison`, in `lean/Sheaf/Paper/TensorWordComparison.lean`,
is the generic tensor-functoriality substep. It treats arbitrary pairs of level-word
comparison squares, independently of all purity and exceptional-composition data.
The four squares are site tensor naturality, derived realization naturality, tensor
of the two supplied squares, and inverse tensor-evaluation naturality.

All five cite the current blueprint composition-factors proof (1), tower paragraph,
and record LeanFinder, Loogle, grep and local library/DAG/Mathlib searches.
No existing public interface changed, so there is no change record or forced adaptation.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
