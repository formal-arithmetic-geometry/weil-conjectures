## What changed

The target module now proves `AlgebraicGeometry.Etale.moduleAbelianDerivedExchange_compatibility`
from a proved underived coefficient compatibility and a general right-derived cube lifting
lemma. Both endpoint definitions and the theorem signature are unchanged. Two private
`rfl` lemmas identify `derivedBaseChangeMapPlus` with the generic
`rightDerivedFunctorPlusBaseChange` construction for modules and abelian groups.

Added proof imports `Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange` and
`Sheaf.CategoryTheory.RightDerivedPlusCube`. The former is fully proved using the
abelian adjunction bijection, the defining coefficient mate unit identity,
`unit_map_baseChangeMap_app`, coefficientwise evaluation of `squareLowerStarIso`,
its naturality, and cancellation of the fixed comparison isomorphisms. The latter
states only the formal lifting step, conditional on an underived cube equation;
it has no geometric or coefficient-specific hypothesis.

All three modules compile through the required local wrapper. No new definition,
axiom, arbitrary witness, or changed public signature occurs.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.moduleAbelianDerivedExchange_compatibility`
(node `lem-weil-pbc-module-abelian-derived-exchange-compatibility`).

Proved the new
`AlgebraicGeometry.Etale.moduleAbelianUnderivedExchange_compatibility`
(node `lem-weil-pbc-module-abelian-underived-exchange`), including its private
unit helper. This is an actual proof of the original plan's underived step.

The only added and remaining hole is
`CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_cube`
(node `lem-weil-pbc-right-derived-plus-cube`). Its body is exactly `:= by sorry`.
It is strictly the formal lifting part of the argument: the target supplies its
underived commuting cube with a complete Lean proof. This delivery is a decomposition,
with one upper hole closed and one lower hole added (net zero holes), plus the
underived step proved. The item's module has no remaining sorry.

Edge cases: the general cube does not assume a or b invertible, only the exact
comparison edges c,d. With all coefficient edges identities it is naturality of
deriving a commuting underived square. Identity scheme squares and zero sheaves
are included in the underived proof, which uses no cartesianness or properness.
No preservation of injectives by coefficient forgetting is assumed.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`,
`WeilConjectures.SixFunctors.BaseChange.Derived`, and
`WeilConjectures.SixFunctors.BaseChange.Square`. Their declarations remain available
through the required comparison and underived-exchange imports. No library module
is claimed globally pruned.
The target no longer directly uses `lemma-weil-pbc-derived-exchange-replacement`;
the right-derived uniqueness argument is isolated in the cube node instead.
`def-weil-pbc-underived-exchange` is used by the proved underived node, and
`lem-weil-pbc-module-abelian-inverse-image-comparison` remains needed through the
canonical coefficient comparisons. None of the unit's realized statements or
steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide the comparisons, their invertibility and derived
exchange factorization, but not the formal cube coherence theorem. Step 3 hides
this missing general lifting argument. It is now an explicit independent item.
The underived step needed no new assumption: the pushforward unit formula makes
its coefficient compatibility a direct adjunction calculation.

Searches: LeanSearch returned Internal Server Error (recorded unavailable). LeanFinder returned general localization comparison factorization and
Guitart-exactness results, with no matching bounded below cube. Loogle found the
general `rightDerived` universal-property API; its exact source-specific
`rightDerivedFunctorPlusBaseChange` query found no result. Script grep and local
rg found no existing cube theorem or module/abelian exchange theorem. An existing
restrict-scalars exchange theorem concerns a different coefficient comparison and
is itself unproved, so it was not imported.

The local literature checkout does not contain sites-cohomology.tex; the cited
sources were read at https://stacks.math.columbia.edu/tag/0736 and
https://stacks.math.columbia.edu/tag/07A7. The generic cube is explicitly marked
as a formal expansion, not as a verbatim Stacks lemma.

## New nodes

`lem-weil-pbc-module-abelian-underived-exchange` records the fully proved underived
compatibility in `Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange`.

`lem-weil-pbc-right-derived-plus-cube` records the remaining general lifting theorem
in `Sheaf.CategoryTheory.RightDerivedPlusCube`, with complete hypotheses and a
factorization/uniqueness proof in words. No change records are needed.


## Second reading by B3

1. Compared the entire existing module with the repository using diff. Both public
   endpoint definitions and the target signature are byte-for-byte unchanged. Only
   proof imports, two private definitional-equality helpers, and the target proof
   changed. No statement or definition change record is needed.
2. All three delivered modules compile locally in import order without warnings.
   Inspected the proofs and scanned for forbidden declarations and hollow data.
   The only explicit sorry is the named generic cube theorem, with its node and
   complete natural-language proof. Scratch `#print axioms` checks confirm only
   the permitted standard axioms and sorryAx from open dependencies. No arbitrary
   witness or new data construction is introduced.
3. The cube theorem isolates the formal lifting step and assumes a separately
   proved underived cube; it does not restate the geometric target. Checked all
   source/target types and the inverse orientations of c and d. Identity edges
   reduce to derivation of a commuting square; zero transformations give zero
   composites. The proof by unit factorization and rightDerived_ext is valid:
   PlusExact supplies absolute derivability even after arbitrary postcomposition,
   so preservation of injectives by U or U′ is unnecessary. The underived node
   has a complete kernel-checked proof. Independent LeanFinder, Loogle, launcher
   grep and local rg searches found general comparison/universal-property APIs,
   but no existing theorem giving this cube or underived coefficient equation.
   The remaining generic lifting proof is not a few-minute closure.
4. Read the target downward through both new modules and the existing comparison,
   Square, and PlusBaseChange APIs. The underived adjunction calculation uses the
   shortest available unit formula; the remaining cube uses the canonical derived
   comparison, not chosen isomorphisms. Every public import is required by a
   statement, and the new proof dependencies are plain imports. Checked
   sk-thm-p1.json realized: none of its statement/step nodes is bypassed. The old
   proof dependencies removed from the parent are accounted for: underived
   exchange and inverse-image comparison remain needed transitively; derived
   exchange replacement is replaced by the generic cube's factorization route.
5. Compared the parent node's proof fields with the Lean application and both new
   nodes with their modules. Statements, sources, proof steps, dependency unions,
   creation/blueprint records and Lean signatures agree. The sole added hole is
   rightDerivedFunctorPlusBaseChange_cube. Verdict: valid decomposition, one
   original hole closed and one strictly simpler formal lifting hole added;
   net zero holes, with the underived step proved.

Second reading added a specific underived-exchange search to its node and changed
this report: corrected the inaccurate claim that no
imports were removed, distinguished removed direct imports from global pruning,
and recorded the five review checks. No Lean proof or public interface required
repair.
