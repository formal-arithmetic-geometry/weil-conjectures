## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.CondensedRing.continuousFreeSheet_frames`
with a complete reduction, preserving its entire statement and existing public imports.
All edits are confined to the item, its node, two new statement modules and their nodes.
No existing shared interface or definition changes.

The item now proves the continuous matrix calculation directly. The private
`natural_linear_map_matrix` evaluates a natural linear map on the constant basis vectors
at the terminal pro-etale object. Expanding an arbitrary vector-valued continuous function
as the finite sum of its coordinate functions times these vectors proves the formula on
every test object. `natural_linear_equiv_matrices` applies this construction to the inverse
map too, and proves both rectangular matrix inverse identities.

`natural_linear_equiv_rank` evaluates at a point and applies invariant basis number over E.
The square matrices then give actual elements of GL, with continuous entries for both the
matrix and its inverse. This is independent of any discrete-lattice or locally constant
coset argument. The empty-base branch is proved separately: every test object is empty,
so `empty_presentation_rank` changes the integral presentation rank using the unique
additive equivalence between the relevant continuous-function spaces. Identity matrices
then suffice. Rank zero and zero sheets require no extra hypothesis.

The two remaining categorical arguments are separate statements: global frame comparison
with independent integral ranks, and restriction of a given coordinate equation to opens.
The final proof combines them with the proved matrix and rank arguments. Neither new
statement assumes or concludes the original simultaneous GL-chart assertion.

## Proved and sorry left

Original holes: 1. Item holes remaining: 0.

Closed `AlgebraicGeometry.ProEtale.CondensedRing.continuousFreeSheet_frames` by a complete
Lean proof from the two intermediate theorems and the proved private helpers above.

Added holes: 2, both entire named public theorem bodies in separate modules:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousFreeSheet_globalCoordinates`,
  node `lem-sfb-continuous-free-sheet-global-coordinates`, module
  `Sheaf.Paper.ContinuousFreeSheetGlobalCoordinates`. This supplies global presentations
  and natural rectangular E-linear coordinate equivalences, retaining independent ranks.
  It has no matrix, common-rank or open-restriction conclusion.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousSheet_coordinate_restriction`,
  node `lem-sfb-continuous-sheet-coordinate-restriction`, module
  `Sheaf.Paper.ContinuousSheetCoordinateRestriction`. This transports an already supplied
  coordinate equation. It has no freeness assumption and makes no invertibility,
  continuity or existence assertion about the supplied matrix functions.

This delivery is a decomposition: one original hole closed, two strictly smaller holes
added, net holes closed minus added = -1. The rank comparison, continuous matrix extraction,
inverse identities, GL packaging and empty-base treatment are proved without new holes.
`continuousIntegralVector` is an actual coordinatewise coercion construction; no definition
or private declaration contains `sorry`, and no data is defined by choosing a witness of
an admitted existence theorem.

Verification: `lcompile.py --all` succeeded for all three modules. The item compiled in
28.2 seconds; the two statement modules compiled in 9.3 and 12.9 seconds. A documentation
line-width warning was corrected afterward; every delivered Lean line is at most 100
characters. The new node signatures were compared against the actual Lean statements,
and the overlaid dependency graph has no missing nodes or reachable cycles. The delivery
tool performs the final exact-file compile and preflight checks.

## No longer needed

None. No original import or existing module is withdrawn, and no pruning is claimed.
The original encoding, scalar-extension and restriction dependencies remain needed in the
two new categorical statements. The item's direct proof dependencies now name those two
steps; the dependencies retained below them are recorded explicitly in their nodes.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect hypothesis was found. The original plan is mathematically
consistent, but its cited objectwise encoding isomorphisms do not by themselves expose
the sectionwise scalar-unit normalization and the naturality under open restriction of
the actual normalized sheet map. These are the precise two categorical arguments still
left as named statements. The common-rank and matrix parts of the plan are now proved.

The new statements were checked for an empty base, an empty open, rank zero and zero
sheets; neither requires p to be finite, etale or surjective, or the t_j to split a cover.
The original statement is byte-identical apart from whitespace before its proof.

## New nodes

`lem-sfb-continuous-free-sheet-global-coordinates`: global scalar-compatible frames before
rank identification and matrix extraction, following Local computation paragraphs 1--2
of the current blueprint trace proof. Its natural-language proof specifies finite free
frames, the regular scalar-extension unit equation, pullIso and upperStarComp, the
one-map mate normalization, and the continuous encoding. Its integral ranks are deliberately
independent; the parent proves their equality when the base has a point.

`lem-sfb-continuous-sheet-coordinate-restriction`: restriction of an existing global
coordinate equation along an open immersion, following the restriction part of that same
local computation. Its proof specifies continuousRing_module_restriction,
comapUpperStarIso composition coherence and upperStarComp. The matrices can be arbitrary,
so this step does not repeat the matrix construction or the original freeness claim.

LeanSearch, LeanFinder, Loogle, local Mathlib/source searches and blueprint searches were
performed; their results are recorded in both nodes. No exact declaration supplies these
normalizations. No change record is needed: existing statements and shared definitions
are unchanged.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
