## What changed

Replaced the hole in `WeilConjectures.integralLineTensorComparison` by a complete combination
proof. Its original statement and every existing definition are unchanged. The proof chooses a
flat-term K-flat representative, transports the normalized completion unit through that
representative, applies the strict line/Roos comparison, and then proves the naturality,
representative normalization, finite-generator formula and actual Roos projection equation. The
projection calculation uses the two existing cocone/product projection identities; it does not
assume an extra compatibility of adjunctions.

Added three separate results, with their own modules and nodes: the completion-unit criterion,
the strict chain-level line/Roos comparison, and the finite scalar-extension tensor comparison.
The finite comparison is recorded as a separate theorem whose proof plan uses the proved
`CochainScalarConstruction.exists_scalarTensorComparison`, the recorded object and map equations
of `reductionWitness`, and the existing total-bifunctor comparison. Local irreducibility markers
keep the proof from unfolding the chosen coefficient, reduction, tensor and representative
models; their definitions remain unchanged. No adopted source-library file is changed. No
statement or definition repair and no forced adaptation are included.

The independent coefficient and site universes remain `u` and `t`; coefficient modules use `max
u (t + 1)`. The original invertibility hypothesis on l in X is retained verbatim. No
boundedness, constructibility, finite cover, or global trivialization of the line is added. The
finite comparison is tested mathematically on zero complexes, zero coefficient rings, and
unbounded complexes: its construction only uses the balanced tensor identity and preservation of
the direct sums by scalar extension. The line/Roos statement also covers empty sites and
arbitrary locally trivial, rather than globally free, lines.

## Proved and sorry left

The original module had one hole, in `WeilConjectures.integralLineTensorComparison`; that hole
is closed, and the module now contains zero `sorry`s. The packet closes one existing hole and
adds three named holes. This is a decomposition, not a proof free of new assumptions; its net
count of holes closed is -2.

Private helpers proved in the original module are `roosUnit_projection`, `unit_conjugate`,
`exists_goodRepresentative`, `integralLineComparison_normalization`, and
`integralLineComparison_projection`.

The delivery adds the following named holes, each with its source and full proof in words:

- `WeilConjectures.IntegralOnSlice.integralCompletionUnit_isIso`, node
  `lem-sf-integral-completion-unit-criterion`.
- `WeilConjectures.integralLine_roosTensor`, node `lem-sf-integral-line-roos-tensor`.
- `WeilConjectures.integralFiniteTensorComparison`, node
  `lem-sf-integral-finite-tensor-comparison`.

The completion-unit criterion concerns the particular normalized unit on arbitrary complete
objects, with no tensor parameter. The line/Roos result is a chain-level assertion with no
completeness assumption. Neither is the original theorem under another name; the categorical
localization and normalization argument combining them is implemented in the item module. The
finite scalar-extension result is independent of completeness and of a line, and supplies only
the finite generator clause. Its unfinished work is the total-complex comparison with the exact
generator equation; the module-level balanced tensor comparison is available in the proved
source declaration cited above.

Validation: all four delivered modules compile through `lcompile.py` against the server's
published build and the sandbox dependency artifacts. The final item-module compile took
45.9 seconds with no diagnostics. The three auxiliary statements compiled separately in
0.2, 10.2 and 11.0 seconds. The original theorem signature and all existing definition
bodies were compared with the shared source and are unchanged.

## No longer needed

Removed these private proof imports from the item module:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.EtaleDerivedScalarTensor`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

The parent node no longer directly uses these former proof dependencies: `lem-weil-l-adic-
extension-integers-dvr`, `lem-weil-pbc-completed-constant-sheaf-reduction`, `lem-pur-site-
restriction-module-adjunction-exact`, `lem-weil-proetale-countable-products-exact`, `def-pc-
kflat-complex`, `lem-pur-kflat-change-of-rings`, `lem-pur-derived-change-of-rings`, `lem-weil-
finite-free-completed-scalar-comparison`, `def-pc-tensor-complex-sheaves`, `lem-pur-integral-
operations-well-defined`, `lem-pur-acyclic-kflat-tensor-arbitrary`, and `lem-pur-sheaf-ring-
derived-coefficient-adjunction`. The existing `tool_uses` approvals are retained: several of
these tools remain in the planned proofs of the new auxiliary nodes. No new tool approval is
asserted.

These are removals from the parent proof, not claims of global pruning. The definitions remain
statement dependencies, and several old tools remain dependencies of the new lemmas or of other
modules. No Lean module is withdrawn. All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The old plan did not provide the compatibility between the global completeness predicate's
chosen reduction presentation and the particular `IntegralOnSlice.completionUnit`. An
isomorphism with some limit object does not identify that unit. The new criterion states exactly
this missing normalization bridge, using the identity extension of the existing finite-free
completed scalar comparison and the scalar-extension universal property.

Likewise, the old general K-flat/change-of-rings declarations do not by themselves state that
line tensor commutes with the actual augmented strict Roos complex. That compatibility is made
explicit separately. The available signed-line theorem is specialized to equal site/coefficient
universes, so it cannot simply be applied at the independent universes of this item.

In contrast, the final Roos projection identity requires no new adjunction-identification lemma:
it follows directly from `mappingCocone.lift_fst` and `Pi.lift_π`.

## New nodes

`lem-sf-integral-completion-unit-criterion`, module
`Sheaf.Paper.IntegralCompletionUnitCriterion`, records invertibility of the specified
completion unit on complete objects, independently of any line. Its proof compares the
identity scalar-extension quotient presentation with the slice-operations presentation,
including augmentations and the zero second cocone coordinate.

`lem-sf-integral-line-roos-tensor`, module `Sheaf.Paper.IntegralLineRoosTensor`, records
K-flatness, preservation of quasi-isomorphisms and good representatives, and an augmented
strict Roos isomorphism for tensor with a locally free line. Local triviality, the balanced
reduction comparison, and preservation of products and finite biproducts supply its proof.

`lem-sf-integral-finite-tensor-comparison`, module
`Sheaf.Paper.IntegralFiniteTensorComparison`, records finite scalar extension of arbitrary
unbounded total tensor complexes, with its exact balanced generator formula. It uses the
existing module scalar tensor comparison and total-bifunctor comparison.

All three nodes belong to the original chapter and unit and the same blueprint ancestor's
integral tensor step. No unit statement or realized route is bypassed. The proof-context record is
`coord/changes/H7-integral-line-tensor-proof-context.md`; no existing statement or definition
is changed.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
