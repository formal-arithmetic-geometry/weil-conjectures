## What changed

Replaced the sorry in
`AlgebraicGeometry.perfect_hom_open_restricted_maps_exists` with a complete
construction of all eight fields of restricted `PerfectHomPushPullData`.
Every existing binder, universe and visibility is unchanged. The original public
import of `PerfectHomOpenRestrictedEquivFields` remains necessary for the argument
type. Added proof-only imports of `PerfectHomOpenTestBijective`,
`PerfectHomOpenTransportSquare`, `DerivedOpenTestObject`,
`DerivedOpenLocalization`, and `DerivedAdjoint`.

For each testing object on B, the existing test-object theorem supplies its
supported extension and an isomorphism with its restriction. Its all-target Hom
property determines the extension up to the compatible isomorphism used in the
proof: it is the exact extension by zero, not an arbitrary witness of mere
existence. Construct Hom equivalences by uniquely lifting a map through restriction,
applying the original equivalence, applying the explicit cartesian pullback
restriction, and conjugating by the testing isomorphism. All inverse data use
`Equiv.ofBijective`, whose forward map is explicitly specified. No new definitions
or interface adaptations are made.

The Lean proof supplies ordinary-Hom lifting identities, testing naturality,
precomposition naturality of conjugated pullback Hom, and both the stage and apex
map compatibility identities. The two geometric inputs below are kept as separate
items. Updated the existing maps node's proof and proof dependencies accordingly.

Validation: the missing published equivalence-fields module is now available.
The exact unchanged-signature assembly and both new modules compile locally.
The first dry run found only an unused-variable warning for the supplied e;
explicitly acknowledging that argument before clearing it preserves its name
and type and removes the warning. Removed the redundant file-level
transparency option, already supplied by the compiler configuration. The complete assembly supplies all four
compatibility fields without using coherence of e. Profiling in the earlier
attempt identified repeated comparison unfolding; passing the comparison
explicitly with its determining equation avoids that cost. No dependency source
was recopied or compiled to work around the last-green-build rule.
`deliver3.py --no-push` printed OK: the local compiles, axiom probes and
preflight pass, apart from the second reading reserved for the next worker.
Nothing was pushed.

The local literature documents are absent on this machine. Sources were read at
https://stacks.math.columbia.edu/tag/079W,
https://stacks.math.columbia.edu/tag/08FE,
https://stacks.math.columbia.edu/tag/08BT,
https://stacks.math.columbia.edu/tag/00A7,
https://stacks.math.columbia.edu/tag/0D5S, and
https://stacks.math.columbia.edu/tag/09RE.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.perfect_hom_open_restricted_maps_exists`
(node `new-perfect-hom-open-restricted-maps`). No sorry remains in the item.

Added two holes, each exactly a named public theorem with `:= by sorry`:

- `AlgebraicGeometry.perfect_hom_open_test_bijective`
  (`lem-pc-perfect-hom-open-test-bijective`, module
  `Sheaf.AlgebraicGeometry.PerfectHomOpenTestBijective`): bijectivity of the
  canonical pullback Hom restriction on a supported testing object for one
  geometric projection, independent of any stage diagram or representing data.
- `AlgebraicGeometry.perfect_hom_open_transport_square`
  (`lem-pc-perfect-hom-open-transport-square`, module
  `Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare`): commutation of canonical
  Hom restriction with one morphism over the base, with no bijectivity or
  representability assertion.

This is a decomposition (one original hole closed, two new holes added), not an
axiom-free proof of the geometry. The complete assembly uses both smaller inputs.
The auxiliary categorical naturality lemma is private and proved.

The new statements were checked on the empty open, full open, zero testing object,
zero target object, and identity base-change arrow. Empty and zero supported tests
have singleton Hom sets; full-open restriction is isomorphism conjugation. The
transport statement is an equality, not the false claim that base-change pullback
is generally bijective on Hom. Arbitrary rings, arbitrary cocones and a one-stage
preorder are allowed; no directedness, finiteness, flatness or perfectness
hypothesis was inserted.

## No longer needed

No original import is removed, and no module is claimed to leave the targets'
import closure. The original DAG proof dependency
`new-perfect-hom-open-restricted-core` is removed from the maps node: it is a caller
of this theorem, not a lemma this proof uses. The module
`Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore` remains needed upstream.

The proof does not use
`perfect_hom_open_restricted_equiv_fields_exists`, nor the particular supplied
`e`'s naturality or equivalences. Its module still occurs in the signature, and
its caller still invokes that existence theorem; those are not pruned by this
non-breaking delivery. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The maps node cited the core node, although the core module imports Maps and applies
this theorem. Following that dependency literally would be circular. The supplied
`PerfectHomOpenRestrictedEquivFields` has testing-object naturality but no
transition or apex compatibility; arbitrary independently chosen equivalences can
be twisted at separate stages. One cannot fill stageMap and limitMap just from
that naturality. The theorem itself only asks for existence of compatible data,
so its unchanged statement is addressed by constructing new coherent equivalences
from h using supported test objects. No equation about arbitrary supplied e is
asserted. The already disputed pinned theorem in the parent module is not imported
or used.

LeanSearch returned Internal Server Error, recorded as unavailable in searches.jsonl.
LeanFinder and Loogle returned underived pullback/naturality/mate APIs; the grep
queries found no exact derived open pullback Hom bijection or transport square.
The existing derived test-object and pullback-composition declarations are reused.
Blueprint searches found nearby extension-by-zero assertions for etale coefficient
sheaves, not these sheaves-of-modules statements with the fixed derived tensor
pullback and canonical comparisons.

## New nodes

`lem-pc-perfect-hom-open-test-bijective` isolates the single-projection supported
Hom bijection. Its docstring details the extension-by-zero adjunction, K-flat
cartesian comparison, and conjugation argument. The supplied comparison equation
makes the canonical value explicit without repeatedly unfolding it downstream.

`lem-pc-perfect-hom-open-transport-square` isolates the canonical cartesian square
identity for a single Over arrow. Its docstring details the pullback projection
calculation and the pasted composition-comparison associativity calculation.
Both nodes are in `sec-picard-framework`, retain unit `sk-thm-picard-semicon`, and
point to the ancestor's inverse-image open Hom comparison. No change record is
needed because no existing statement or definition changed.

## Second reading by E2

1. **Visible declarations and statements.** I compared the delivered assembly module with the repository version. The existing theorem signature is byte-for-byte unchanged, including all binders, universes, visibility, and the supplied `e`. The two additional modules contain only new named theorem statements; no existing declaration or definition was altered.

2. **Compilation and axioms.** I compiled all three sandbox modules with `lcompile.py --all`; each compiled successfully. The only remaining `sorry`s are the two explicitly named split theorems `perfect_hom_open_test_bijective` and `perfect_hom_open_transport_square`; there are no `sorry`s in definitions, and no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The assembly proof is kernel-checked apart from those imported split theorems.

3. **Split-off statements.** Both split statements are public, named, and strictly smaller than the assembly target: one asserts bijectivity for a single supported pullback test, and the other asserts only the canonical transport-square equality. Their docstrings give the intended extension-by-zero and cartesian-comparison arguments, and each has a matching DAG node with source, proof steps, dependencies, and Lean attachment. They do not duplicate the target or assert unsupported bijectivity for transport.

4. **Route and pruning.** The proof constructs supported test objects, lifts maps by the stated Hom bijections, conjugates the canonical pullback restriction, and proves naturality and transition/cocone compatibility. It uses the two split geometric inputs and the existing open-localization, adjunction, and pullback-comparison declarations. No old proof dependency is removed from the module's imports; the maps node removes only the erroneous circular core dependency from its `proof_deps`. The unit `sk-thm-picard-semicon` and its realized route remain intact.

5. **Node agreement.** The maps node's proof and dependencies match the actual Lean route, including both new lemmas and the local conjugated-map calculation. The two new node statements match their Lean declarations, and their `proof_origin`, source references, and blueprint links are present. Edge cases described in the reports (empty/full opens, zero objects, and identity arrows) are consistent with the displayed statements.

I changed only this report during second reading. No Lean proof, declaration, import, node statement, or dependency was changed.
