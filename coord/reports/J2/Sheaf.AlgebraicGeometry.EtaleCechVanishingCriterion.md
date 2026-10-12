## What changed

Proved `AlgebraicGeometry.Scheme.isZero_rightDerived_etale_of_cech_vanishing` without changing
its signature. Its proof defines the property of Cech acyclicity on Cov, derives section
surjectivity over B from the existing H1 lemma, proves closure under short exact quotients
using the homology sequence, and performs dimension shifting by induction quantified over
all sheaves satisfying this property. The induction base proves the degree-zero map is epi
using `rightDerivedZeroIsoSelf`; the successor uses the quotient closure and injective
vanishing. This is the node's seven-step argument, with only Step 5 split off.

Added proof-only imports of `EtaleSectionsSurjectiveOfCechH1`, `InjectiveSheafCechAcyclic`,
`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`, Mathlib's
`HomologySequence`, and the new `EtaleCechSectionwiseShortExact` module. The new module proves
the zero-morphism preservation instance needed to apply the categorical Cech functor to a
short complex. Its remaining theorem states only short exactness of the Cech complexes
from sectionwise surjectivity, with no cofinality, covering, Cech vanishing, injectivity or
derived-cohomology hypothesis or conclusion.

Both modules compile cleanly using lcompile.py --all. Updated the original node's proof
route and dependencies to the implementation. All writes are in the sandbox; no push.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.isZero_rightDerived_etale_of_cech_vanishing`.
Also proved: `AlgebraicGeometry.Scheme.etale_cech_preservesZero`.

The only sorry added or left in the delivery is
`AlgebraicGeometry.Scheme.etale_cech_shortExact_of_sections`, node
`lem-weil-pbc-etale-cech-sectionwise-short-exact`, in the new module
`Sheaf.AlgebraicGeometry.EtaleCechSectionwiseShortExact`.

The existing imported theorems `CategoryTheory.injective_sheaf_cech_acyclic` and
`AlgebraicGeometry.Scheme.surjective_sections_of_cech_h1_vanishing` remain their own items;
this delivery does not change them. Thus the main result is reduced, not axiom-free yet.

## No longer needed

No original public imports were removed: they are part of the statement/instance interface.
Removed the experimental proof import `Mathlib.Algebra.Category.Grp.AB`; the remaining
Step 5 obligation explains the product-exactness argument in its docstring and node.

The route no longer needs `lem-weil-pbc-module-sheaves-enough-injectives` or its module
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`: the original local instance is already
a proved Mathlib Grothendieck-abelian instance and supplies injective resolutions.

No import of `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` is needed:
the existing proved upstream `exists_rightDerived_δ_exact` supplies exactly the two
positions of derived exactness the induction uses. The mathematical long-exact-sequence
node remains in proof_deps, realized by that existing upstream proof.

`lem-weil-pbc-cochain-complexes-degreewise-exact`, `def-weil-pbc-cech-complex`, and
`def-sp-left-exact-additive` move from direct proof dependencies into the Step 5 node;
they are still needed there and are not globally pruned. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original enough-injectives module is unnecessary because
its conclusion is already available from Mathlib. The source library already proves the
needed two-position derived long exact sequence, so the stronger sorry'd full sequence
need not be imported. The existing injective Cech and H1-surjectivity declarations fit
exactly and were used as instructed.

The unfinished glue in Step 5 is the identification of the degree-p categorical Cech
map with the product of section maps. A scratch attempt obtained short exactness after
evaluating the sheaf sequence on the discrete tuple diagram and taking its limit, but
transporting to the actual Cech degree required additional product/limit comparison
naturality. This is the precise remaining obligation, strictly smaller than the criterion.

Edge cases checked for the split statement: empty family gives zero in all degrees;
degree zero still uses one-fold slice products, not assumed definitional equalities with
the original objects; no covering hypothesis is needed; arbitrary infinite products of
abelian groups are exact by componentwise choice. The proof does not assume B is
isomorphism-closed: all intersections are exactly the piObj objects in hB.

## New nodes

`lem-weil-pbc-etale-cech-sectionwise-short-exact`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-cech-sectionwise-short-exact.json`, states
Step 5 of Stacks 03F9 as `etale_cech_shortExact_of_sections` in
`lean/Sheaf/AlgebraicGeometry/EtaleCechSectionwiseShortExact.lean`. The source, complete
natural-language proof, three available Mathlib search kinds and the unavailable LeanSearch attempt, Lean signature and chapter/unit provenance
are recorded. No statement/definition changes and no change records are needed.

LeanSearch was attempted through msearch.py but returned Internal Server Error. Its node entry
records unavailability without a verdict; the other search services and source grep succeeded.
The writer dry-run wrapper explicitly permits the missing second-reading section as the sole
remaining preflight reason; the second reader owns that section.

## Second reading by J2

1. Compared the delivered criterion module with the repository version. The theorem statement and all existing declaration signatures are byte-for-byte unchanged; only proof imports and the proof body changed. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The criterion theorem is proved, and the only remaining `sorry` is the named theorem `etale_cech_shortExact_of_sections`, which has its own node and complete source-level proof description. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. Reviewed the split statement and searched Mathlib and the project for an existing declaration. The statement is strictly smaller than the criterion: it asserts only sectionwise short exactness of the Cech complexes, with no covering, cofinality, vanishing, injectivity, or derived conclusion. Empty and infinite indexing cases are covered by product exactness. No duplicate declaration was found. Verdict: pass.

4. The proof uses the shortest available route from the imported H1-surjectivity, injective Cech acyclicity, derived exactness, and the sectionwise short-exactness node. The removed experimental `Mathlib.Algebra.Category.Grp.AB` import is not needed. The route preserves the unit and does not bypass its realized steps. Verdict: pass.

5. The DAG proof and dependency lists match the Lean proof: the main node records the induction and its actual imported dependencies, while the new sectionwise node records the split theorem and its source. Verdict: pass.

I changed only this second-reading section and reverted an exploratory product-isomorphism proof attempt because it did not compile; the delivered source remains the clean compiling version.
