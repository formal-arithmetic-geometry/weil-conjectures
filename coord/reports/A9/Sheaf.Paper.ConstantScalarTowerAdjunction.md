## What changed

Proved `WeilConjectures.PurStrictScalar.tensor_exact` in
`Sheaf.Paper.ConstantScalarTowerAdjunction` from existing finite-basis constructions
and `scalarTowerExtension_exact`. Three private proof imports expose the proved
integral basis, its universe lift, the constant-sheaf basis isomorphism, and the
whole-tower exactness theorem. Existing declaration signatures, definitions,
attributes and public imports are unchanged.

The node now records this argument and its three actual proof dependencies.
The arithmetic auxiliary is used directly, rather than invoking the completed
coefficient conclusion of its containing module. Likewise, the constant-sheaf
basis isomorphism is used before its sectionwise corollary. These are already
proved declarations, accessed with `import all`, with no copied constructions.

Searches: LeanFinder returned sheaf finite-limit preservation and sheafification
APIs, Loogle returned the whiskering API, and launcher grep returned zero hits.
Local source search found the exact generic tower theorem and the two basis
constructions used here.

## Proved and sorry left

Closed one original hole: `WeilConjectures.PurStrictScalar.tensor_exact`
(node `def-pur-constant-scalar-tower-adjunction`). Zero holes remain in the item;
zero holes added or split off. This is a proof, not a decomposition.

## No longer needed

None. No imports, nodes or modules withdrawn. The node previously had no proof
steps or proof dependencies. All three added proof imports are used. The proof
requires no completed-coefficient comparison, ramification argument, or new
statement beyond the already proved basis auxiliaries.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof plan despite its named exactness theorem
containing a hole. Its theorem docstring supplied the correct finite-basis
argument; the delivery records its existing reusable declarations in the DAG.
No statement correction or definition repair was needed. The construction handles
all schemes, including the empty scheme, through the generic sheaf-basis and
pointwise-tower constructions.

Validation: the complete module compiled in 8.5 seconds. The only warnings were
two overlong lines, subsequently wrapped. The delivery performs the final compile
and axiom/preflight checks. All three added DAG dependencies were checked for a
path back to the item; none exists. Explicit sheafification instances fix the
coefficient universe without changing any public instance or elaboration option.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
