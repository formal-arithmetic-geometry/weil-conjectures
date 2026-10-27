## What changed

Completed `SheafOfModules.existsUnique_signedLineProduct` in
`Sheaf.Paper.SignedLineScalarTensorTower`. Private, proved helpers construct tensor-basis
charts, compare signed bases by powers of a unit, glue compatible chart maps as sections
of the actual internal Hom sheaf, and detect the resulting isomorphism locally. Uniqueness
uses tensor-basis coordinates on the given cover and sheaf separation.

The existing private `tensorBasis_bijective` proof now uses a proved tensor-to-unit
component formula, avoiding repeated expansion of its composite on a slice. A proof-only
import of `WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective` supplies the
coverwise local-bijectivity lemmas. Existing public signatures, public imports, definition
bodies and target statements are unchanged. The existing node's multiplication proof
step and proof origin now describe the completed argument.

Local elaboration settings and their consumer check are recorded in
`coord/changes/V6-signed-product-elaboration.md`.

## Proved and sorry left

Closed one of the item's one initial holes:
`SheafOfModules.existsUnique_signedLineProduct`, node
`lem-pur-signed-line-scalar-tensor-tower`. Added zero holes, split off zero statements,
and retained zero holes in the delivered Lean file. All new private lemmas are proved;
all earlier proofs remain complete.

The complete candidate compiled through `lcompile.py` on the project server in
56.4 seconds. No diagnostic settings or scratch modules are part of the delivery.

The transition-unit construction includes the zero-ring case: injectivity of the basis
coordinates gives both inverse identities, without assuming a nonzero coefficient ring.
Negative exponents are checked by evaluating on the positive basis. Degree zero and
opposite exponents use the usual identities for integer powers of units.

## No longer needed

No imports, declared dependencies, nodes or modules are pruned. The proof uses the
existing localized tensor restriction, tensor bilinearity and internal-Hom APIs.
No new DAG nodes or public statements are introduced.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The earlier node's local-product plan was
mathematically sufficient; its remaining gluing and change-of-basis steps are now written
in Lean. The original private tensor-basis calculation repeatedly unfolded a large
slice composite; the new private component formula addresses that elaboration cost.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
