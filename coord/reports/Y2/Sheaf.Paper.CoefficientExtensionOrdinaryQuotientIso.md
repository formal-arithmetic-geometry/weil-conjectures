## What changed

Replaced `WeilConjectures.coefficientExtensionOrdinaryQuotientIso`'s proof hole by ordinary
scalar adjunction composition, uniqueness of left adjoints, and induction on actual sequence
transitions. The statement and its public imports are retained. All added helpers are private
and proved. The complete proof compiled in 26 seconds during validation. A general
private adjunction lemma keeps concrete tensor expressions out of the chain-map argument.
Added private proof imports for the ordinary sheaf scalar adjunction and the
existing concrete scalar/sequence transition APIs.

The associator is built from the supplied quotient adjunction itself. Its unit identity
therefore suffices without the additional `hunit` hypothesis; that hypothesis stays in the
public signature. The proof works degreewise on arbitrary complexes, including zero complexes,
with no boundedness, flatness, or ramification restriction. Equal indices use the actual
identity transition. The site's universes remain independent of the coefficient universe.

## Proved and sorry left

Closed: `WeilConjectures.coefficientExtensionOrdinaryQuotientIso`
(`stage3-pur-extension-ordinary-quotient-iso`), the item's one original hole.

Added holes: none. Remaining holes in this delivery: none. No decomposition or new node.

## No longer needed

No original import or declared proof dependency was removed. No module is withdrawn.
The proof uses the ordinary scalar adjunction and actual transition formulas; it does not
need a new sheafified balanced-associator theorem, a derived comparison, or a K-flatness lemma.
The new proof imports are used only privately. The original route's three dependencies
remain. The already proved ordinary transition
identities in `CoefficientSequenceRoosModel` are reused as tools; no derived Roos or
normalization statement is used. The ordinary sheaf adjunction node is also a proved tool.

## Where the brief, the DAG or earlier work was wrong

The planned pure-tensor associator construction can be replaced by uniqueness of left
adjoints, using the existing normalized ordinary adjunction. The transition equality follows
by applying the integral scalar adjunction's injective Hom equivalence, so it suffices to
check images of `1 tensor x`. This closes the ordinary obligation directly rather than
splitting it again. The corresponding proof steps and dependencies were updated in the
item's node. The unit record has no realized statement or steps here, and no unit route changes.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
