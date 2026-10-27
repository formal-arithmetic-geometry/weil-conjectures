## What changed

Server single-file compilation passes for the item and the directly proved point-unit
lemma. The earlier full packet compile passed all data and split statement modules.
The delivery command runs the final combined compile and preflight.

Replaced the body of `WeilConjectures.NativeExceptionalForgetful.native_exceptional_forgetful`
by an explicit assembly proof. It uses normalized left comparisons and objectwise
representing counit triples with the existing proved generic
`Adjunction.forgetful_representingPair_rightMate`. The right comparison is the fixed mate;
its unit equation is taken directly from that theorem, and its counit equation follows by
cancelling the left comparison. Full faithfulness of the recorded ordinary realization
lifts the realized native point unit to `commonUnit`, with the required normalization.
The structural specialization is the same right comparison evaluated on the constant,
followed by the exceptional functor applied to `commonUnit`; its specified equality follows
from this definition. Ordinary point transport yields the literal `Spec k` specialization.

The geometric bridges not directly supplied by the existing dependency interfaces are
two named public theorems with holes in separate modules, plus a directly proved
point-unit theorem. They are strictly parts of the argument:
left comparisons and representing counit lifts (without a native right adjoint), the
ordinary image of the native constant, and ordinary structural exceptional-unit transport
(without native categories or a native adjunction). Each has its source and full proof in
words in its docstring and node. The left-model obligation retains both the degree -1
coinvariant term and the degree 0 invariant term through the existing cyclic derived Hom
lemmas. No derived faithfulness of native forgetting is assumed.

Moved the existing interface declarations verbatim to
`Sheaf.WeilSheaf.NativeExceptionalForgetfulData`, publicly reexported by the item, to permit
the bridge modules to import the interface without a cycle. A byte comparison verifies
that every moved declaration's attributes, signature, body and docstring is unchanged.
This relocation is for dependency direction, not a split to avoid a compile limit.
`tools/downstream.py` reports zero current Lean consumers of the original item. The node
attachment and the parent obligations remain; no module is withdrawn. The change record
is `coord/changes/A2-native-exceptional-interface.md`.

## Proved and sorry left

Original hole closed by a complete Lean assembly:
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_forgetful`
(node `lem-sf-weil-native-exceptional-forgetful`). Original item: 1 hole; final item: 0.

Two holes added, both named public theorem bodies:

- `WeilConjectures.NativeExceptionalForgetful.native_exceptional_left_models`
  (`lem-sf-native-exceptional-left-models`).
- `WeilConjectures.NativeExceptionalForgetful.native_exceptional_structural_transport`
  (`lem-sf-native-exceptional-structural-transport`).

This is a decomposition: 1 upper hole closed, 2 lower holes added, net -1 hole closed.
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_point_unit` is additionally
proved directly, with zero holes: closureMap is an isomorphism by its pullback construction;
exact-derived single-functor comparisons and adicLowerStarUnitIso identify the regular
native module; its section-module action is definitionally the ordinary regular action.
It is not a sorry-free proof of the geometric theorem. The data module has zero holes,
and no definition or private helper has a hole. No existing dependency proof is removed.

## No longer needed

Removed the original direct proof import
`Sheaf.CategoryTheory.CyclicDerivedHomExactSequence` from the item; it belongs to the planned proof of the
left-model obligation instead. The split statements do not import their planned proof dependencies until those proofs
are written; their DAG nodes retain them. The original four proof dependencies
`lem-sf-native-weil-open-proper-forgetting`,
`lem-sf-native-weil-scalar-frobenius-counit`,
`lem-sf-cyclic-derived-lifted-counit-represents`, and
`lem-sf-cyclic-derived-hom-exact-sequence` are now dependencies of that strict geometric
obligation. They are not globally pruned. The realization and generic right-mate nodes
are used directly in the assembly. All original public imports are retained in the
reexported interface. No module or unit route is pruned. The item’s obsolete direct `tool_uses` entries are removed: `lem-pur-ringed-site-grothendieck-abelian`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-pur-compact-support-condensed-realization`, `prop-weil-pbc-qbar-condensed-two-colimit`, `lem-sf-constructible-exceptional-adjunction-coefficients`, `lem-weil-pbc-mate-pasting`, `lem-sf-fixed-pair-derived-forget-comparison`, `lem-sf-cyclic-derived-hom-exact-sequence`. Their relevant mathematical uses remain in the original or new geometric dependency nodes; none is deleted.

## Where the brief, the DAG or earlier work was wrong

The planned generic lemmas exist, but their interfaces do not directly provide the
geometric assembly. `NativeWeilScalar.scalar_frobenius_counit` needs an actual chosen
coefficient construction, finite-stage descent systems and geometry, and has an explicit
presentation bridge; the item instead quantifies over arbitrary normalized coefficient
systems. The native Hom representability theorem is phrased on full subcategories of
fixed-pair derived categories and requires exactness and normalized Hom-boundary
compatibility. The new left-model obligation states precisely the remaining geometric
instantiation and transport, not an equivalent copy of the item theorem: it assumes no
native exceptional adjoint and gives no native comparison, unit or specialization.

The point clause is not definitional after the specified right-derived closure transport.
It is proved by the existing exact-derived single-complex comparisons and
`adicLowerStarUnitIso`; the final regular section-module presentation is definitional. Similarly `pointGeometricIso` alone
does not provide the comparison of ordinary exceptional systems for the two structural
maps; this is isolated in the ordinary structural transport obligation.

The Mathlib searches found generic right-adjoint uniqueness, exact-derived single-functor
comparisons and ordinary sheaf adjunctions, but no exact geometric bridge. Searches of
the current blueprint for forgetful model, point unit, representing counit and structural
exceptional returned no duplicate imported node. Empty schemes, identity morphisms and
an arbitrary chosen algebraic closure were checked in the stated proofs. The unit record
has no realized steps to bypass, and the existing native proof route is retained below it.

## New nodes

`def-sf-native-exceptional-forgetful-data` owns the existing interface relocated verbatim.
It introduces no new mathematical definition or data chosen from an unproved existence
assertion.

`lem-sf-native-exceptional-left-models` is the geometric implementation of the old first
two assembly steps: common-stage lifting, normalized left comparison and representing
counit triples, without assuming a native right adjoint. Its proof dependencies are the
original native open/proper, scalar counit, cyclic lifting and boundary lemmas and the
existing realization lemma.

`lem-sf-native-exceptional-point-unit` proves directly that the regular native coefficient
module in degree zero remains the regular ordinary module after exact closure transport
and section presentation. Its proof uses the existing source-library exact-derived API
and a reflexive equality of regular module presentations; it has no holes.

`lem-sf-native-exceptional-structural-transport` compares only ordinary exceptional images
of the coefficient unit under the canonical geometric point identification and
compactification coherence. It has no native exceptional hypothesis.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
