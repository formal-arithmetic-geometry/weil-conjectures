## What changed

Proved `AlgebraicGeometry.ProEtale.finiteProper_classical_amplitude` in
`lean/Sheaf/SixFunctors/FiniteProperClassicalAmplitude.lean`. Its complete signature,
including both universe parameters, every hypothesis, all nine conjuncts and the
canonical coefficient lift, is unchanged. No other Lean module is modified.

The proof uses the canonical constant-ring derived adjunction for products, the
bounded-below/total comparison for the lower bound, and proper torsion vanishing
with faithful coefficient forgetting for the etale bound. The heart bound is
transported through the exact intrinsic/fixed-ring restriction equivalence and
the bounded-below etale/pro-etale comparison. Exact pro-etale products and the
existing sharp left-complete heart upper-bound theorem extend it to complexes
unbounded below. The finite-relative-dimension criterion gives etale coproducts.

The six private helpers are fully proved; the Grothendieck instance is proved
as well. `import all Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation`
reuses that file's already-proved private `intrinsicRestriction`, its equivalence
instances, `intrinsicHasDerivedCategory`, and `restrictionDerivedDirectImageIso`.
It adds no public dependency to a theorem signature. Explicit standard derived
models and an explicit product-preservation instance avoid localization-model
and dependent-instance inference ambiguity.

Updated only `proof`, `proof_deps`, `proof_origin` and the permitted deletions from
`tool_uses` in `lem-sfb-finite-proper-classical-amplitude.json`. The statement,
source, Lean attachment, unit and unit realization records are unchanged. No new
nodes, definition changes, statement repairs, forced adaptations or withdrawals.
The public-import pruning and file-local elaboration/instance commands are
documented in `coord/changes/Y9-finite-proper-classical-amplitude-imports.md`;
there are no current Lean importers or theorem users to adapt.
The theorem docstring now describes the actual proof.

Validation: the complete module compiles through `lcompile.py` with no errors or
warnings (35.3 seconds). The original/new theorem signatures were compared as
text and agree. All Lean lines are at most 100 characters. The zero coefficient
ring, empty schemes, `e = 0`, negative degrees and an arbitrarily negative tail
are covered by the arguments: torsion needs no nonzero ring, fibre comparison is
an isomorphism, and the left-complete theorem assumes no lower bound. The
canonical coproduct criterion includes empty families and all stated universes.

Search: launcher `msearch.py` was used with leanfinder for right-derived lower
bounds and adjoint products, loogle for `Functor.rightDerivedFunctor, "IsGE"`,
and grep for `hasLimitsOfShape_discrete|isLE_obj_of_isLE_of_homologyProperty`.
Loogle did not recognize the searched derived-functor identifier and the grep
results did not directly prove this theorem. Local `rg` searches and signature
reads found the useful proved declarations in `HomotopyCategory.Products`,
`DerivedCategory.LeftComplete`, `LeftCompleteHeartUpperBound`, and the coefficient
restriction helpers. The source blueprint's etale-bound/comparison route is
retained; the shorter generic completeness argument replaces its separate
truncation-window assembly below the unit level.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.finiteProper_classical_amplitude`
(node `lem-sfb-finite-proper-classical-amplitude`).

Item holes: 1 before, 0 after. Holes added: 0. Split-off statements: 0.
Every helper has a complete proof. No `sorry` remains in any delivered Lean file.
`#print axioms AlgebraicGeometry.ProEtale.finiteProper_classical_amplitude`
reports `[propext, sorryAx, Classical.choice, Quot.sound]`: `sorryAx` is inherited
from the existing dependencies, not a new hole in this packet. Existing
dependency theorems are used with their current proofs; this delivery does not
assert that the entire targets' dependency closure is already finished. The
axiom-check compile also succeeded without warnings (25.0 seconds).

## No longer needed

Removed these original imports:

- `public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `import Sheaf.CategoryTheory.RingedSiteModules`
- `import Sheaf.Paper.FiniteDiscreteCondensedRing`
- `import Sheaf.Paper.FiniteDiscreteSchemeRing`
- `import Sheaf.Algebra.Homology.KInjectiveProductsTermwise`
- `import Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `import Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `import Sheaf.CategoryTheory.KInjectiveComputes`
- `import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty`
- `import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `import Sheaf.SixFunctors.FiniteProperClassicalTruncation`

The first two removed imports exported the unused finite-coefficient alternative
presentation and the alternative derived-functor construction. Neither occurs
in this theorem's signature or its proof; its canonical ordinary constant-ring
functor is used throughout. The remaining removed imports were proof-only.
`WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete` replaces the broad
`CoproductsOfHomologyProperty` import for its precise completeness API.

Removed direct proof dependencies and their old top-level tool approvals:

- `def-weil-sheaf-of-modules-category`: ordinary module categories are supplied
  by the statement imports and the Grothendieck theorem; no extra result from
  its statement module is applied.
- `lem-pc-ringed-space-product-kinjective`: use the already-proved generic
  `DerivedCategory.hasLimitsOfShape_discrete` from `HomotopyCategory.Products`.
- `lem-weil-pbc-finite-discrete-condensed-ring-constant` and
  `lem-weil-pbc-finite-discrete-scheme-ring-constant`: the statement already uses
  the canonical constant ring sheaf, so no continuous-function coefficient
  presentation must be identified.
- `lem-sp-kinjective-computes`: degree-zero higher images are already expressed
  by the bounded-below single/homology functors and their proved compatibility.
- `lem-sfb-bounded-heart-amplitude-devissage` and `def-kun-truncations`: no
  separate bounded-heart theorem or extra truncation module is used. The sharp
  generic left-complete heart theorem supplies the required induction.

Also removed `lem-sfb-finite-proper-classical-truncation` from the direct route.
The proof uses `det-pe-products-exact`, the canonical derived homotopy-limit
triangle in `lem-sfb-derived-left-complete-truncation-bound`, and
`lem-sfb-left-complete-heart-upper-bound` instead. It does not use the weaker
`b + 1` consequence of left completeness. The other new direct dependency,
`lem-pe-classical-direct-image-preservation`, records the imported private exact
restriction and derived-direct-image compatibility helpers, not an assumption
of the conclusion being proved here.

These are dependencies pruned from this item, not declarations deleted from the
library. In particular no adopted source declaration is removed or weakened,
and no claim is made that another parent cannot still require these modules.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The first delivery attempt crashed
during the temporary checkout after a 600-second tooling timeout; the retry
reached preflight. Preflight required a change record for the two removed public
imports and file-local commands; that record is now included. The original DAG's
specialized finite-proper truncation-window step is unnecessary given the
existing proved sharp left-complete heart upper-bound theorem and exact
pro-etale products. This keeps the unit's etale proper-torsion bound, direct-sum
criterion and comparison transfer, while shortening the assembly beneath it.
The finite-discrete coefficient bridges were also unnecessary for the current
canonical constant-coefficient statement.

One stale compile request returned exit 124 while the compile server was busy;
subsequent compiles completed normally. No tooling or timeout was modified.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
