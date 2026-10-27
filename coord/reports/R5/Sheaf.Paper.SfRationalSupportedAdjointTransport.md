## What changed

Filled three theorem proofs in `Sheaf.Paper.SfRationalSupportedAdjointTransport`, preserving
all public statements, definitions, instances, attributes and public imports.

* `sfSupportedRationalHomCoordinates` constructs the additive equivalence by tensoring
  `sfRationalCoefficientEquiv` and commuting the factors. Tensor induction proves uniqueness
  among additive equivalences, without assuming their scalar linearity. This generalizes the
  existing construction in `sfRationalHomCoordinates_existsUnique` to the arbitrary category
  required here.
* `sfSupportedKernelRightAdjoint` uses the existing adjoint additivity and linearity lemmas,
  Mathlib's adjunction-induced coherent shifts, and right-adjoint triangulatedness. Unit
  compatibility determines each shift comparison, and extensionality gives uniqueness of the
  entire coherent shift structure. The Hom scalar equation follows from the unit formula.
* `sfSupportedIntegralCategoryIdentification` obtains Noetherianity and finite dimension
  from finite type over the given field, and maps the specified unit to global sections.
  `integralStratifiedPerfectDetailed` identifies the detailed and completed predicates;
  `integralStratifiedPerfectCharacterization` identifies the completed and perfect predicates.
  Equality elimination proves both literal raw object and pure-tensor normalizations.

Added one proved private extensionality helper for coherent shift structures. Scoped
`linter.unusedVariables false` to the kernel-adjoint theorem because its existing statement
names two instance binders used only by typeclass inference; their spelling is preserved. No new public
statement, definition, module or DAG node was introduced. The completed proofs follow steps
1, 6 and 7 of the existing node; its remaining transport plan and dependency records stay valid.

## Proved and sorry left

Closed three of the four original holes:

* `WeilConjectures.sfSupportedRationalHomCoordinates`.
* `WeilConjectures.sfSupportedKernelRightAdjoint`.
* `WeilConjectures.sfSupportedIntegralCategoryIdentification`.

One original hole remains, unchanged:
`WeilConjectures.sfRationalSupportedAdjointTransport`, attached to
`lem-sf-rational-supported-adjoint-transport`. It retains its source and complete numbered
proof plan in its docstring. Its remaining construction includes the three normalized raw
triangulations, five localized exact functors, three normalized adjunctions, and the original
and localized supported-triangle consequences.

Holes closed: 3. Holes added: 0. Split-off statements: 0. The private helper is proved.
The three proofs compile through `lcompile.py` in 13.0 seconds. The final delivery check
also compiles the final file with its axiom probe.

## No longer needed

Removed four unused private proof imports from this module:

* `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`.
* `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
* `WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`.
* `Mathlib.CategoryTheory.Adjunction.FullyFaithful`.

These imports are unused by the three completed proofs and by the module's public data.
No DAG dependency or module is withdrawn: the unfinished transport proof still needs its
recorded plan. In particular this delivery does not claim that any of these dependency nodes
has become unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

No statement error was found in the proved clauses. The integral raw-normalization proof
requires generalizing the completed predicate before eliminating its equality; direct
elimination between the two fixed predicates fails in Lean.

For the remaining transport proof, `exists_triangulated_scalarLocalization` exposes tensor
shift and identity comparison normalization only for shift one, whereas
`SfSupportedRawTriangulation` requires them for every integer. The implementation constructs
all shifts componentwise, but its published conclusion alone does not expose that stronger
normalization. A future proof must establish the additional equations or construct the
normalized shifts directly; this delivery changes neither interface.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
