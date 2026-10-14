## What changed

Repaired the proof of `CochainComplex.termwise_product_isKInjective_and_isLimit`
in `Sheaf.Algebra.Homology.KInjectiveProducts` without changing any signature,
visibility, universe, hypothesis, definition, or import. The K-injectivity argument
now uses Mathlib's `isKInjective_iff_rightOrthogonal` and
`IsKInjective.rightOrthogonal`: the previously constructed product in the
homotopy category makes any map from an acyclic object zero by projection
extensionality. Removed the separate null-homotopy assembly for this step.
Updated the docstring and the node's proof order and proof_origin to agree.

This is a repair item listed in coord/repairs.txt, not a fresh sorry item.
The existing complete product and localization constructions are retained.
The module compiles with lcompile.py without warnings. Searches through
msearch.py used LeanFinder, Loogle, and grep; direct source searches checked
both project roots and Mathlib. Read the supporting node, unit realization,
Mathlib's right-orthogonality criterion and Hom comparison, and the available
upstream HomotopyCategory/Products.lean. The local Stacks source is absent;
the source was read at https://stacks.math.columbia.edu/tag/0BK6.

## Proved and sorry left

`CochainComplex.termwise_product_isKInjective_and_isLimit` remains completely
proved, as do the private helpers `CochainComplex.productHomotopy` and
`CochainComplex.mapProduct`. No sorry remains and none was added.
Holes closed: 0, because the supplied baseline already had no holes.
Holes added: 0. Node: `lem-pc-ringed-space-product-kinjective`.
The K-injectivity step is shortened using existing Mathlib theorems, rather
than moved to a new statement. Empty and singleton families use the same
limit-extensionality proof; there is no inhabited-index, boundedness,
K-injective-resolution, or global-product hypothesis.

## No longer needed

No imports or modules removed. The direct K-injectivity proof no longer needs
`IsKInjective.homotopyZero` or a second application of `productHomotopy`.
The latter helper remains necessary for uniqueness in the homotopy category.
The public bridge import is retained to preserve all existing reexports.
The existing pruning of `lem-pc-abelian-groups-exact-products` remains valid:
no exactness of products in Ab is used. The unit sk-thm-picard-duality has
empty realized statement and step lists; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The brief calls this a module containing sorry, but the supplied module is
already proved. The relevant assignment is the duplicate repair entry from
upstream review #1428. That entry cites
`CochainComplex.isKInjective_of_isLimitFan` and
`DerivedCategory.isLimitFanMkQObjOfIsKInjective` in
`WeilConjectures.Algebra.Homology.DerivedCategory.Products`.
Neither declaration nor that module exists in the supplied repository,
source checkout, or published local Lean library. The available module is
`WeilConjectures.Algebra.Homology.HomotopyCategory.Products`; its
`homotopyOfFan` and `isLimitFanQuotient` require
`HasLimitsOfShape (Discrete T) C`, which is strictly stronger than existence
of this family's products in each degree. Applying those results directly
would change the statement's hypotheses, so that replacement is unavailable
in this baseline. This delivery removes the redundant K-injectivity
construction using the available Mathlib criterion; it does not claim to
have imported or used the two absent declarations. A full replacement by
those particular upstream declarations needs their sources and compiled
modules to be incorporated by the maintainer first. No tools were changed.

The three direct importers are
`Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`,
`Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts`, and
`Sheaf.Topology.RingedSpaceRGammaDerivedLimit`. Their statements and imports
need no adaptation because this delivery changes only a proof and its
explanation. No statement was disputed or weakened, and no arbitrary object
was chosen from an unproved existence theorem.

## Second reading by K4

1. **Interface: pass.** Compared the complete module with the repository using `diff`.
   Every existing declaration signature, definition, universe, visibility, and import
   is byte-for-byte unchanged. Only the public theorem proof and its explanatory
   docstring change. No change record or downstream adaptation is needed.
2. **Proof and axioms: pass.** Compiled the delivered file through `lcompile.py`
   without errors or warnings. A scratch copy with `#print axioms` for
   `CochainComplex.termwise_product_isKInjective_and_isLimit`, `productHomotopy`,
   and `mapProduct` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   There is no sorry or forbidden declaration modifier. The homotopy components
   and cone lifts are constructed from actual limits and inverse Hom bijections;
   no arbitrary data comes from an unproved existence theorem.
3. **Split statements: pass, none.** No statements, nodes, or holes are added.
   Inspected the Mathlib right-orthogonality criterion and Hom comparison, searched
   with LeanFinder, Loogle, grep, and direct `rg`, and read the upstream product
   module. Its generic product lemmas require all products of the index shape,
   whereas this statement only assumes products of the evaluated family.
   The argument handles empty and singleton families: projection extensionality
   requires neither an inhabited index nor a nonempty family.
4. **Route and pruning: pass.** Reviewed both private constructions and the theorem
   from its conclusion backward. The homotopy-category limit, orthogonality step,
   and localization Hom bijections prove both conclusions with the original
   hypotheses. The shortened K-injectivity step uses proved Mathlib results.
   The proof-only DerivedCategory.KInjective import is already private. Existing
   public imports are retained as part of the module's unchanged reexported
   interface. No old proof dependency is removed by this repair; the earlier
   removal of the exact-products-in-Ab node remains valid. Checked the unit's
   empty realized statement and step lists; no realized route is bypassed.
5. **DAG: pass after correction.** The node's proof dependencies are the union of
   its steps' uses, and its proof and origin match the Lean route. Its statement,
   Lean record, and unit are unchanged. Corrected the last step's stale reference
   from "product of Step 2" to "product of Step 1" after the reordered proof.

Second reading changed only that DAG step reference and appended this review;
no Lean repair was necessary. Independently checked the unchanged mathematical
statement against [Stacks Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6).
This is a completed proof repair, not a new hole closure: holes closed 0, added 0.
