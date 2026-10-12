## What changed

Replaced the author's degree-two/higher-degree constant-sheaf split by the actual
Artin-Schreier distinguished-triangle argument. The original declaration
`AlgebraicGeometry.isZero_etaleCohomology_constantZMod_of_one_lt_of_charP` has its
byte-for-byte original signature. Its proof obtains `artinSchreier_shortExact`, applies
unbounded derived global sections, proves epimorphy in degree q-1 (using first-degree
Frobenius epimorphy for q=2 and additive vanishing for q>=3), and applies Mathlib's long
exact homology sequence. The connecting map and the outgoing map both vanish, so
exactness gives the desired zero object.

The two new modules are `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing`
and `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi`. They expose genuine parts
of the original argument, concerning G_a rather than the constant Z/p sheaf. Their
imports provide their signatures; their unfinished proof plans are recorded in the
nodes and complete docstrings. No existing definition, public import, or statement
was changed. New proof imports of the item are plain `import`.

## Proved and sorry left

The item has 1 of 1 original theorem bodies proved:
`isZero_etaleCohomology_constantZMod_of_one_lt_of_charP`. It is a reduction to open
lemmas, not an axiom-free completion of Artin-Schreier vanishing.

Two named theorems remain open in new modules:

- `isZero_etaleCohomology_additive_of_two_le`, node
  `lem-sc-artin-schreier-additive-derived-vanishing`: transfer the existing ordinary
  additive cohomology vanishing across coefficient-universe and derived-encoding
  comparisons.
- `epi_etaleCohomology_artinSchreier_one`, node
  `lem-sc-artin-schreier-first-cohomology-epi`: assemble the proper/affine argument,
  scalar and Frobenius action, finite dimensionality, and Lang-Steinberg.

Each has proof exactly `by sorry`, a complete mathematical proof in its docstring,
and its own node. Neither states the conclusion of the original item. The existing
Artin-Schreier short exact sequence theorem is also still open upstream. The axiom
check is expected to contain the three standard axioms and `sorryAx`, with no other
axiom. A direct `#print axioms` scratch check and deliver3's full declaration probe
are used below.

## No longer needed

Removed the item's ten unused direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `Sheaf.AlgebraicGeometry.EtaleZariskiCohomology`
- `Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.Paper.PQFCohomology`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`
- `WeilConjectures.AlgebraicGeometry.Curve.Compactification`
- `WeilConjectures.LinearAlgebra.SemilinearFrobenius`

Removed the author's additional unused imports of general curve cohomological
dimension (both Sheaf and WeilConjectures). Deleted the two unlanded constant-sheaf
case nodes and their unlanded module from the sandbox; no library file is deleted.

Every old direct `proof_deps` entry replaced at the item node, other than the retained
`lem-sc-as-sequence`, is listed here:

- `def-sc-curves`
- `def-sc-etale-qcoherent-module`
- `def-sc-constant-sheaves`
- `def-weil-pbc-abelian-etale-sheaves`
- `lem-weil-pbc-abelian-etale-sheaves-grothendieck`
- `lem-sp-grothendieck-enough-injectives`
- `def-weil-pbc-etale-cohomology`
- `lem-sp-kinjective-computes`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `lem-sc-ga-cohomology`
- `lem-sc-compactification`
- `lem-sc-affine-open-proper`
- `lem-sc-etale-affine-qcoherent`
- `lem-pc-coherent-hi`
- `pqf-def-cohomology`
- `lem-sc-etale-zariski-qcoh-comparison`
- `lem-sc-lang-steinberg`

These are removals from the item's direct proof dependencies, not a claim that all
these nodes can leave the entire target closure. Additive comparison, compactification,
affine acyclicity, proper finiteness and Lang-Steinberg remain needed in the two
new helpers' proof plans. Definitions remain in the original statement dependencies;
Grothendieck/enough-injectives infrastructure is handled by the existing derived
functor implementation. The distinguished-triangle/long-exact-sequence route replaces
the direct universal-delta-functor construction in this item's proof.

## Where the brief, the DAG or earlier work was wrong

The author's degree-two node had a proof dependency back on the original theorem,
creating a cycle, empty searches, and an abbreviated non-verbatim Lean signature.
Its docstring did not cover the affine case. The higher-degree node cited the general
curve cohomological-dimension theorem instead of realizing the Artin-Schreier route;
its docstring did not supply the promised complete proof. The item node still carried
the original seven-step proof rather than the author's Lean proof. The report did
not enumerate the replaced dependencies and retained many unused proof imports.
The two original new declarations also had long-line warnings.

The available Mathlib distinguished triangle and long exact homology sequence do
suffice for the categorical reduction. The hard remaining glue is in the additive
cohomology encoding and Frobenius action, not the target case split. Searches found
no existing declaration of these precise helper statements. The existing
`subsingleton_etale_ga_and_structure_cohomology` concerns the smaller-universe
`Sheaf.H` encoding, not the derived object here; it is retained as a helper-plan
input rather than duplicated. Lang-Steinberg itself is an existing proved theorem.
A full proof-dependency closure audit also found an inherited cycle through
`lem-weil-pbc-sheaf-algebraic-structures-objects`, already reachable from the
repository version of this item. This delivery does not alter those nodes; it
introduces no new back-edge and removes the author-created cycle.
LeanSearch returned an HTTP 500 and is recorded as unavailable without a verdict;
LeanFinder, Loogle, actual Mathlib grep, and direct library searches were completed.

## New nodes

`lem-sc-artin-schreier-additive-derived-vanishing` realizes the additive-vanishing
part of blueprint step 2 in the exact derived encoding and coefficient universe
needed here. It has no dependency back on the original item. Its complete signature,
creation record, search records, sources, and proof steps are recorded.

`lem-sc-artin-schreier-first-cohomology-epi` realizes blueprint steps 3--7. Its
hypotheses specify natural additive section identifications and the precise
sectionwise Frobenius-minus-identity formula, so the conclusion is about the actual
map from `artinSchreier_shortExact`. Its statement and proof dependencies do not
use the original item or general curve cohomological dimension.

No change record is necessary: existing statements, definitions and public imports
are unchanged. All new imports in the original item are for its proof only.

## Second reading by B2

1. Compared the delivered item against the repository with `diff`, and separately
   compared its full original theorem signature byte for byte: unchanged. No existing
   definitions or public imports changed; no change record is required.
2. Compiled every delivered module in import order using lcompile, with no errors or
   linter warnings. The item has no `sorry`; the only new direct occurrences are the
   two listed named helper theorems. Scanned for prohibited declarations and escapes;
   none are present. The scratch `#print axioms` check shows only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` (the open inputs). The delivery probe
   additionally checks every generated declaration.
3. Rejected and removed the author's constant-sheaf case split and cyclic node.
   Read each replacement helper's full signature and proof. Tested the critical
   boundaries conceptually: q=2 uses epimorphy at 1 and vanishing at 2; q=3 uses
   vanishing at 2 and 3; q=0,1 are excluded. First-degree epimorphy is valid for both
   affine curves (zero cohomology) and proper curves (finite-dimensional p-semilinear
   Lang-Steinberg); no bijectivity of Frobenius is assumed. Section identifications
   are natural, so wp is the correct map. Coefficient-universe transfer is on finite
   affine hypercover cochains, not an unproved assertion about lifting injectives.
   Repeated searches with different terms; no exact existing statement found.
4. Used existing Artin-Schreier data, the proved right-derived triangulated functor,
   and Mathlib's single triangle/long exact sequence. Pruned all unused direct imports
   and enumerated every replaced original direct dependency. Read `dag/units/sk-prop-cd.json`:
   its `realized` entries are empty; no realized node is bypassed. Its characteristic-p
   clause still follows the Artin-Schreier route, with the original additive vanishing
   and proper/affine/Lang-Steinberg argument preserved in the helper plans.
5. Rebuilt the item node's proof, proof_deps and proof_origin to match the Lean
   distinguished-triangle proof. Both new nodes have complete exact Lean signatures,
   self-contained statements, source locations, mathematical proof steps, union-correct
   dependencies, three search kinds, and creation/blueprint/Lean records. No new back-edge or cycle is
   introduced, and no reference to the removed author's nodes remains. A closure
   audit found the pre-existing sheaf-algebraic-structures cycle noted above;
   it is also reachable from the original repository item. Other original node fields are
   unchanged.

Changes by this second reading: replaced the target restatement-style split with a
real Artin-Schreier long-exact-sequence reduction; replaced both split-off statements,
modules and nodes; removed unused imports; fixed all docstrings, sources, searches,
signature records, dependency records, and the pruning report.
