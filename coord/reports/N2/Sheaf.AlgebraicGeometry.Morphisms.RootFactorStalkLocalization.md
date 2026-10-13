## What changed

Implemented the existing localization argument in
`Sheaf.AlgebraicGeometry.Morphisms.RootFactorStalkLocalization`, without changing
its public statement or visibility. The coefficient is the actual image of f
in the base stalk. A proved private helper combines `Polynomial.isLocalization`
with `IsLocalization.of_surjective` to identify the root quotient over that
stalk as a localization of the original root quotient. The prime P is explicitly
the extension of w; its contraction to the base stalk is the maximal ideal.
Monicity gives finiteness and integrality, hence P is maximal. Transitivity of
localization constructs the stalk isomorphism. A second proved private helper
uses Mathlib's compatibility of affine stalk maps with coefficient germs, and
localization extensionality proves the required equality of structural maps.

The existing DAG node now records these three implemented steps and the Mathlib APIs used.
Only private proved helpers were added; the second reader removed the two redundant proof imports. No public definition,
statement, instance, or visibility changed. No other module was adapted.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.rootFactor_stalk_localization`
(node `lem-sbc-root-factor-stalk-localization`).

Added zero holes. No `sorry` remains in the delivered module. Both private
helpers are proved from Mathlib. This is a proof, not a decomposition into new
unproved statements.

## No longer needed

Removed the first worker's redundant proof imports
`Mathlib.RingTheory.Localization.Algebra` and `Mathlib.RingTheory.Ideal.GoingUp`: both APIs
are already available through the existing imports, as confirmed by compiling
the entire proof without them. The original module had no proof-dependency
imports or lower DAG nodes to prune. Its three public imports are preserved.
No new Sheaf dependency is used.

## Where the brief, the DAG or earlier work was wrong

No statement correction or route departure was necessary. The existing plan is
implemented using Mathlib's generic localization and prime-ideal APIs.

## Second reading by N2

1. Compared the only delivered Lean module with the repository using `diff`
   and the declaration-table comparison. The existing theorem's signature,
   visibility and docstring are byte for byte unchanged. There are two new
   private proved helpers, no public interface changes and no adaptations.
   Verdict: pass.
2. Compiled the candidate and the final proof through `lcompile.py`, with no
   errors or warnings. A scratch copy of the final file prints the axioms of
   the public theorem and both private helpers: each uses only `propext`,
   `Classical.choice` and `Quot.sound`. Searched the delivered source for
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` and `extern`: none.
   The witnesses are actual constructions: the coefficient image, extended
   prime ideal and localization equivalence. Verdict: pass.
3. No statements were split off and no holes were added. Checked the quotient
   localization helper against Mathlib's `IsLocalization.of_surjective`: the
   two quotient maps are surjective, commute, and their principal kernels
   satisfy its exact hypothesis. This remains valid for arbitrary polynomials,
   including zero and unit polynomials. For the public theorem, exponent one
   gives the expected base stalk, zero coefficient is allowed, and the zero
   ring has no spectrum point to which the hypotheses apply. Positivity is
   used precisely for monicity and finiteness. Verdict: pass.
4. Read the proof from the public theorem down through its helpers and checked
   its Mathlib APIs. Searched the library and upstream root-localization code
   using alternate localization/base-change words, including an `msearch.py`
   grep query; found no existing theorem that closes the full statement.
   The generic polynomial/quotient localization reduction is appropriate.
   Both added imports were redundant: a scratch copy compiled after removing
   both. Removed them from the delivery. The original `proof_deps` is empty,
   so there are no obsolete DAG dependencies. Read
   `dag/units/sk-prop-input-spreading.json`, including its `realized` record;
   this argument supports the existing trait/root-chart step and bypasses no
   unit statement or step. Verdict: pass after import pruning.
5. Compared the delivered node with the repository. Only `proof` and
   `proof_origin` changed; `proof_deps` remains empty. Its three steps match
   coefficient/quotient localization, prime extension and maximality, and
   transitivity with compatibility of structural maps. There are no new
   nodes to audit, and the original node statement and Lean record are
   preserved. Verdict: pass.

Second reading changed only the two redundant proof imports and this report.
One original hole closed, zero holes added; no proof body repair was needed.
