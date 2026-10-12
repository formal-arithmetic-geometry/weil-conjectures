## What changed

The target's signature is unchanged. Its proof obtains the inclusion and its site
properties from `AlgebraicGeometry.zariski_to_etale_core`, chooses Mathlib's canonical
sheaf pullback and adjunction, and proves finite-colimit preservation from that
adjunction. Only left exactness in arbitrary coefficient universes is split off in
`Sheaf.Paper.ZariskiEtaleSheafLeftExact`. Each new statement has its own module.
The core lemma has a complete natural-language proof, including representable flatness.

## Proved and sorry left

The one original theorem `AlgebraicGeometry.zariski_to_etale_is_morphism` has its
proof filled (1 of 1); it still rests on the two explicitly open intermediate theorems:
`AlgebraicGeometry.zariski_to_etale_core` (lem-weil-pbc-zariski-etale-core) and
`AlgebraicGeometry.zariski_to_etale_sheaf_left_exact`
(lem-weil-pbc-zariski-etale-sheaf-left-exact). No definition contains sorry.
This is a reduction, not an axiom-free completion of the target.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`:
Mathlib's canonical adjunction already supplies this component. Removed the redundant
new exactness theorem/node: finite-colimit preservation is now proved directly.
Old direct proof dependencies no longer used directly by the target:
- `lem-weil-pbc-open-immersion-etale`
- `def-sc-zariski-site`
- `def-weil-pbc-etale-site`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-open-preimage-fibre-product`
- `def-pc-fibre-product`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-site-continuous-pushforward-sheaf`
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`
- `lem-weil-pbc-presheaf-pullback-sets-left-exact`
- `lem-weil-pbc-sheafification-sets-exact`

The geometric dependencies remain below the core lemma, and the left-exactness
ingredients remain below its lemma. These are changes of direct dependencies, not
claims that all corresponding modules leave the target closure. No public import
was removed from the original module.

## Where the brief, the DAG or earlier work was wrong

The first worker searched for its invented names, not the mathematical statements;
those recorded searches did not establish novelty. The new nodes also depended in
their statements on their parent target, creating circular dependency records, and
their docstrings did not contain complete proofs. These are repaired. The earlier
arbitrary-functor exactness split was false; the delivered proof uses only the canonical
pullback. Mathlib's available flatness/left-exactness instances restrict the category
and coefficient universes and cannot directly supply the target's arbitrary v.
Thus the finite-limit half remains a genuine universe-general intermediate lemma.

## New nodes

`lem-weil-pbc-zariski-etale-core`: constructs the inclusion and verifies its site
data (steps 1-4 and representable flatness); new module Sheaf.Paper.ZariskiEtaleCore.

`lem-weil-pbc-zariski-etale-sheaf-left-exact`: only finite-limit preservation for
the canonical pullback, in arbitrary coefficient universes; new module
Sheaf.Paper.ZariskiEtaleSheafLeftExact. The colimit half needs no new node.
No existing signature or definition changed, so no change record is required.

## Second reading by S1

1. Compared the original module by diff: its existing declaration signature and
   docstring are byte-for-byte unchanged; only the proof and proof imports changed.
   New declarations were absent from the repository.
2. Compiled all three modules in import order, without errors or warnings. Inspected
   all delivered text for forbidden declarations and hollow definitions. Only the
   two named, wholly postponed intermediate proofs contain sorry. Axiom checks on
   scratch copies and the delivery probe verify only the standard three axioms and
   sorryAx from the recorded open statements.
3. Read the two intermediate statements and checked their edge cases: empty scheme,
   empty opens and covers, terminal object/empty finite limit, and arbitrary larger
   coefficient universes. They are true and strictly parts of the original argument.
   Attempted LeanSearch (service unavailable); searched LeanFinder, Loogle and rg with mathematical descriptions and nearby names;
   reviewed Mathlib's Pullback.lean and Flat.lean. Mathlib closes colimit preservation,
   but its finite-limit instances require more restrictive universes. Source proof:
   https://stacks.math.columbia.edu/tag/00X5 and /tag/00X6 (also read sites.tex).
4. Pruned the unused proof import, proved the colimit part directly, and kept the
   geometric and left-exactness parts of the route. Read sk-thm-p1.json realized:
   this item is below its realized nodes, and no unit statement or step is bypassed.
5. Rewrote proof/proof_deps/proof_origin to reflect the actual Lean reduction.
   New nodes contain definition dependencies, source, complete proof steps, authentic
   searches and matching Lean records; removed the dependency back to the target.

Second reading changed: narrowed the exactness split to left exactness, proved
finite-colimit preservation, gave each new statement its own module, expanded the
core proof docstring, repaired node routes/searches, pruned the unused proof import,
and removed all compilation warnings.
