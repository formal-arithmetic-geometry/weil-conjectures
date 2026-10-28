## What changed

Replaced the body of `WeilConjectures.IntegralFiniteExtension.finiteU_isIso` by an
explicit ordinary-etale affine-cover argument and scalar-adjunction transport.
The proof identifies the local mate using the actual composite open adjunction,
uses the generic proved helpers in `DualizingOpenMate`, applies jointly-surjective
conservativity, and composes the etale/pro-etale and intrinsic restriction mates.
The final calculation transports the scalar adjunct through both origin isomorphisms
and matches the defining `finiteU` formula.

The new module `Sheaf.SixFunctors.CoefIntegralFiniteExtensionAffineCounit` isolates
only the ordinary-etale affine native-quotient counit calculation. It has no
non-affine descent, comparison-site transport, intrinsic realization, or final
scalar-adjunct normalization. This is a genuine local geometric subproblem, rather
than a renaming of `finiteU_isIso`. Its docstring and node specify the cofinal
finite-free/upper-field-quotient factorization, including ramification.

The item privately imports the affine calculation, the generic open-mate proofs
(`import all` is needed for its already proved private generic helpers), and the
adopted source's jointly-surjective isomorphism criterion. Its existing public
import of Core is preserved. No adopted source file is changed.

Corrected the intermediate theorem to include `hl : l ≠ D.p` explicitly, following
the source coefficient conventions. The sole caller is adapted to pass its existing
`hl`. The change record is `coord/changes/J8-finite-u-characteristic.md`.

## Proved and sorry left

The corrected `WeilConjectures.IntegralFiniteExtension.finiteU_isIso` has a complete
Lean proof from the affine theorem; there are no sorries in the item module.
The private categorical transport lemmas and `finiteEtaleU_isIso` are proved.

One new hole remains:
`WeilConjectures.IntegralFiniteExtension.affineCounit_isIso`, node
`lem-sf-integral-finite-extension-affine-counit`, in its own module.
One old sorry body is removed and one new sorry is added: net zero. This is a
statement repair and decomposition, not a completed proof of the formerly
unrestricted theorem. In particular the old theorem without `l ≠ D.p` is not
claimed proved. The remaining affine calculation is explicitly identified rather
than counted as progress. The caller has zero holes before and after adaptation.

All three files are compiled separately in import order with `lcompile.py --all`.
The unadapted caller was also compiled against the changed item to verify the
forced error. Delivery repeats the required checks and compatibility compiles.

## No longer needed

No existing module is withdrawn and no unit route is bypassed. No original public
import is removed. The item's direct proof no longer cites
`lem-coef-finite-free-extension` or `lem-coef-finite-dualizing`; these are retained
as proof dependencies of the new affine calculation, so they are not globally
pruned. The canonical scalar transport is proved generically in the item; the
same-field `FiniteDualizingScalarRealization` theorem and module are not imported.
The other original dependency, `def-sf-integral-finite-extension-core`, is retained.
There is no claim of a newly unreachable module.

## Where the brief, the DAG or earlier work was wrong

The original `hl` section variable disappeared from Lean's actual theorem
signature. The source fixes `ell ≠ p` in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-conventions.md`.
Both cited coefficient theorems have that hypothesis. The statement correction
restores it; no counterexample to the unrestricted statement is asserted. The only
citer, `lem-sf-integral-finite-extension-u-reduction-is-invertible`, still holds
because its dualizing data and theorem already carry `hl`. The node includes the
complete `statement_change` record and citer audit.

The original plan's assertion that the coefficient extension at every native
quotient level is finite free is not valid for a ramified extension. The finite-free
quotient is `O_L / pi_E^(n+1) O_L`, which is a cofinal upper-field quotient, not in
general `O_L / pi_L^(n+1)`. For instance at exponent two with ramification at least
two the latter is killed by `pi_E`, while the lower quotient need not be. The new
node records finite-free extension followed by the upper-field quotient comparison;
it never assumes the native quotient map is flat. Lean's open-mate generic helpers
already allow arbitrary finite coefficient ring maps, although the exported
same-field theorem's statement is narrower.

## New nodes

`lem-sf-integral-finite-extension-affine-counit` states the affine ordinary-etale
counit subproblem for the given field embedding and actual normalized quotient map.
Its source is paragraph 2 of the integral finite-extension proof. Its three proof
steps use finite-free cofinal extension, finite dualizing quotient compatibility,
and right-adjoint uniqueness. Identity and empty cases are included. It keeps the
item's chapter and unit, and records its full ancestry and three real Mathlib
searches. The helper is strictly smaller geometrically and omits the two further
transport arguments now proved in the item.

## Forced adaptations

`Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible` is unclaimed
in the current shared claim records. Its original line 46 fails against the
corrected item: `n : ℕ` is expected to have type `l ≠ D.p` in the application
`finiteU_isIso l E L ι X D n`. The only changed line passes `hl` before `n`.
No declaration signature, visibility, import or other proof line changes there.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionAffineCounit": "4b2a85f80a400268f199628f90f9d094c5d86b7a", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible": "96bcf04044febeab57b4bb19626b299c5ca0ff19", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible": "a73a4e6df5b22ee13a26116ba350bbd23dc7349d"}, "results": {}, "time": "2026-10-28T12:15:21+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
