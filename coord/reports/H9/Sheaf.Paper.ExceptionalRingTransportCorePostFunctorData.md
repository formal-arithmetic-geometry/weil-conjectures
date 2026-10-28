## What changed

In `Sheaf.Paper.ExceptionalRingTransportCorePostFunctorData`, construct the sequence
functors by conjugating the supplied integral functors through the inverse endpoint
reconstruction equivalences. The adjunction is the composite of the three supplied
adjunctions. Explicit equivalence unit isomorphisms give both realization maps and
both reduction maps. No new system functor or arbitrary data witness is chosen.

The private `reconstructionFiniteReduction` identifies reconstruction followed by
finite evaluation with actual quotient scalar extension. The private
`integralLeftEvaluation` composes the supplied left realizations with the actual
qcqs compact-support finite comparison, then lifts through the fully faithful
finite inclusion. This proves the entire left evaluation field without a new hole.
Whiskering each comparison by the inverse source reconstruction and cancelling its
counit yields the displayed sequence evaluation comparisons.

Prove `exists_exceptional_transport_integral_left` directly: compose the supplied
ambient left realization with `sfQcqsCompactSupportRealization` and take its fully
faithful preimage. Neither endpoint reconstruction nor integral system operations
or realization choices are needed for this proof.

The only remaining step is the right finite quotient comparison for fixed integral
and finite adjoints. It is isolated in the new module
`Sheaf.Paper.ExceptionalIntegralRightReduction`. Both new imports in the item are
private proof imports. The existing structure and theorem signatures, universes,
public import, and attributes stay unchanged. The unused-variable linter is
suppressed only for the two existing theorems, whose prescribed parameters include
unused system operation/realization choices.

Validation: the new statement module compiled in 8.8 seconds; the final item compiled
in 12.3 seconds with no errors or warnings, using only lcompile.py. Both Lean files
have lines at most 100 characters. The unchanged direct consumer
`Sheaf.Paper.ExceptionalRingTransportCorePostData` compiled with the delivered item
in import order: 11.8 seconds for the item and 9.3 seconds for the unchanged consumer,
with no errors or warnings. Its unchanged sandbox copy was then removed. All direct DAG references exist and the added edges create no
cycle. Delivery performs the final compile, axiom, record and consumer checks.

## Proved and sorry left

Original holes removed: 2. New holes added: 1. Net hole decrease: 1.

- `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_integral_left`
  is proved directly, with no new obligation, for
  `new-lem-sf-exceptional-ring-transport-integral-left`.
- `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_post_functor_data`
  has a complete assembly proof for
  `new-lem-sf-exceptional-ring-transport-post-functor-data`. Its categorical transport,
  adjunction, realization maps, reduction maps and left finite evaluation are proved.
  Its right finite evaluation is reduced to the new theorem below. This part is a
  decomposition, not a claim that the geometric right comparison is proved.
- The sole remaining `sorry` is
  `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_integral_right_reduction`,
  node `lem-sf-exceptional-integral-right-reduction`, in the new module. It is exactly
  the natural right quotient comparison for one fixed field stage and fixed
  adjoints, with the two actual endpoint reconstruction records. It constructs none
  of the nine fields of the original transport package. Its docstring gives its
  source and full argument in words.

There are zero `sorry` tokens in the item and one in the added module. No definition
or private declaration contains `sorry`. No axiom or prohibited implementation
feature is introduced.

## No longer needed

No existing import is removed, and no entire module is claimed globally pruned.
The original public reconstruction import remains necessary to state the item.

`lem-sf-integral-compactification-system-realization` is removed from both item
nodes' proof dependencies: the integral-left comparison already follows from the
supplied left realization and fixed qcqs realization, and the transported functors
are obtained from the supplied integral adjunction. The explicit `operations` and
`realizations` parameters stay in both signatures for compatibility but are unused.
Their modules remain transitively imported by the existing public interface.

`lem-sf-exceptional-system-transport` is no longer a direct proof dependency of the
assembly node. It remains needed by the new right-reduction node. The normalized
reconstruction calculus remains used by the explicit conjugation constructions.

The new helper is strictly a subargument: unlike the original theorem, it chooses
no sequence functor, no adjunction, no realization or reduction comparison, and no
left evaluation. Thus this is not a renaming or repackaging of the original hole.

## Where the brief, the DAG or earlier work was wrong

The original single proof step mixed elementary categorical conjugation with
geometric finite evaluation and a separate integral realization. The supplied
integral adjunction already suffices for the conjugation fields, and the existing
qcqs finite comparison proves left evaluation. The genuine unresolved bridge is
only right finite reduction. The system-transport declaration uses ordinary
strict-system categories and does not directly state this comparison in the
Reconstruction/sequence coordinates. The new node makes that remaining obligation
explicit rather than moving the entire package again.

An identical fully faithful integral-left construction exists in the downstream
normalization module. Importing it would create a cycle, so this item uses the
short construction directly. No downstream declaration is changed.

The new statement was checked on identity operations, the first quotient n=0
(exponent 1), zero complexes and empty schemes. It imposes no absolute separatedness
on X or Y and requires no faithfulness of finite evaluation. Zheng Proposition
5.26(3), read in the supplied PDF, is precisely the right finite reduction result.

A full traversal of the pre-existing DAG also encountered the existing cycle at
`lem-pc-ring-hom-extension-differential` and the missing reference
`def-weil-pbc-ideal-module-product-stalk`. They are outside this delivery; validation
of this packet therefore separately checks direct references and all newly added
edges. No new cycle was found.

## New nodes

`lem-sf-exceptional-integral-right-reduction`:
`lean/Sheaf/Paper/ExceptionalIntegralRightReduction.lean`, one theorem and one hole.
The statement is the right quotient comparison for fixed integral and finite
exceptional adjoints and supplied reconstruction records. Source: Zheng,
Construction 4.1, Lemma 5.22, Proposition 5.24, Construction 5.25 and Proposition
5.26(3). Mathlib LeanSearch, LeanFinder and grep searches found generic derived
functors or unrelated algebraic reduction; no exact match. The node records the
actual searches and the three steps of the argument. No change record is needed:
no existing statement, definition, instance, public import or attribute changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralRightReduction": "6264f03f4ef41537b512a3444d0a8821dad247f4", "Sheaf.Paper.ExceptionalRingTransportCorePostFunctorData": "12e1c24c00c96e7ecbf6535cd850e1827f328bd2"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCorePostData": {"hash": "67d70145abf660cd486fa5d40853b7e303ede8fb", "status": "OK"}}, "seconds": 93, "time": "2026-10-28T10:26:20+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
