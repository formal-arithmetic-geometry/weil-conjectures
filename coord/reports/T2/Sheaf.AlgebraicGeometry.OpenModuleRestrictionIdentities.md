## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.open_module_restriction_identities` in
`Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities`, preserving its signature,
public imports, coefficient categories, and specified functors.

The open extension is the composite of scalar restriction along the coefficient
isomorphism with the linearization of abelian extension by zero. Both factors are
fully faithful, using the existing scalar equivalence and `fullyFaithfulMapModLeft`.
The inverse of the specified module adjunction's unit gives the first natural
isomorphism. The existing source theorem
`isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint` gives the second
objectwise; uniqueness of maps into zero proves its naturality.

The source full-faithfulness construction is reproduced directly inside the proof,
using its two general factors, to avoid importing the additional derived and
constructibility theory of `ModuleObject.Derived.OpenImmersionEssImage`.
All three new proof imports are private. No source-library file or public interface
was changed, and no consumer adaptation or change record is required.

Validation: the retained proof compiled cleanly against the current published build through
`lcompile.py` in 6.8 seconds on this repair attempt.
Import-direction checks accepted the reused source modules. Empty open support,
whole open support, zero modules, and the zero coefficient ring all satisfy the
same argument. No finiteness or Noetherian assumption was introduced.

## Proved and sorry left

Closed one of one item holes:
`AlgebraicGeometry.ProEtale.CondensedRing.open_module_restriction_identities`
(node `lem-sfb-open-module-restriction-identities`).

Added zero holes. There are no remaining `sorry` declarations in the delivered Lean
module. The new DAG node attaches an already proved source theorem; it introduces
no Lean declaration and is not a split-off hole. Existing dependency proofs and
holes, including the projection-formula instance used by linearization, are
unchanged; this delivery does not claim the whole transitive proof closure is closed.

## No longer needed

Removed the two private proof imports and the corresponding proof dependencies:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, node
  `lem-sfb-internal-module-operations-transport`.
- `Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`, node
  `lem-sfb-proetale-identified-open-closed`.

The proof does not use reconstructed section rings, internal/sectionwise module
transport, sectionwise open extension, uniqueness of its left adjoint, or
full-faithfulness lifting through sectionwise equivalences. The two obsolete
`tool_uses` approvals were removed from the item's node. These modules remain
available for their other users; no module withdrawal is requested.

The unit's restriction assertions and its constructibility route remain intact.
Only the proof beneath the restriction-identities node has been shortened.

## Where the brief, the DAG or earlier work was wrong

The return at head `91d6e241b61` requested restoration after quarantine. The
current repository has since restored the item through bulk restoration
`c283ba5d874`; its source is byte-identical to the archived quarantine source and
still contains the original theorem hole. The existing claim is held by T2.
This repaired packet preserves the restored statement and Lean attachment,
replaces its hole with the retained complete proof, and refreshes the existing
node from the current repository before applying only the owned proof fields.
It does not withdraw the module, delete the quarantine archive, or deliver an
empty module. The restoration return is thus reconciled with the current source.

The planned five-step sectionwise argument was unnecessary: the adopted source
library already proves the relevant full-faithfulness construction and disjoint
vanishing for the actual internal coefficient-module functors. The latter theorem
had no DAG attachment, so this packet records it rather than restating it with a
new hole. There was no false statement or unusable interface to repair.

## New nodes

`lem-sfb-internal-open-extension-disjoint-vanishing` records the existing theorem
`AlgebraicGeometry.ProEtale.CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`. It applies to
any morphism whose image misses the open, and is strictly the vanishing part of
the argument: it provides neither the open restriction isomorphism nor the
naturality assertion. Its proof reduces through the canonical coefficient
isomorphism to the existing abelian disjoint-image argument using empty fibre
products and the two adjunctions. Its source, complete proof, blueprint search,
three kinds of Mathlib search, and exact existing Lean signature are recorded.
No new Lean module, unproved theorem, or change record was added.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
