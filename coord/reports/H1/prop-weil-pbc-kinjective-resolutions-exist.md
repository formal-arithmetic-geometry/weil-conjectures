# prop-weil-pbc-kinjective-resolutions-exist

## Worker delivery

Files written:

- `dag/nodes/sec-curve-estimates/prop-weil-pbc-kinjective-resolutions-exist.json`: the parent split into existence/functoriality, comparison, and bounded-below clauses.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-kinjective-functorial-existence.json`: source construction at `CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean:142-180`; no matching pinned Mathlib declaration.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-bounded-below-injectives-kinjective.json`: Mathlib leaf `CochainComplex.isKInjective_of_injective`, `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:133-134`.

Attachments:

- `CochainComplex.IsKInjective.nonempty_iso_quotient_obj` belongs to existing node `lem-weil-pbc-kinjective-hom-derived`.
- No exact sorry-free declaration states the combined item.

WANTED: none.

The earlier attempt duplicated the comparison theorem, cited only grep searches, and used the abelian-sheaf definition where the item requires module sheaves. I removed the duplicate, cited the existing module-sheaf Grothendieck node, added all required search kinds, and made the comparison argument explicit. The imported blueprint source file is not materialized in this checkout; the imported node and Stacks Tag 079P are the source records.

Nothing remains unfinished in the split.

## Review by H1

I read the imported item and unit/chapter records, Stacks Theorem 19.12.6 (Tag 079P), the existing module-sheaf Grothendieck node, the source construction at `WeilConjectures/CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean:142-180`, the existing comparison node, and Mathlib's bounded-below theorem at lines 133-134. Step 1 uses the module-sheaf Grothendieck statement plus the source functor and natural quasi-isomorphism. Step 2 uses the K-injective definition and the existing bijection on maps into K-injective targets to lift the derived isomorphism and its inverse under the source. Step 3 specializes the exact strict-lower-bound and injective-term hypotheses of `isKInjective_of_injective`. No step is elementary.

I searched the whole DAG and blueprint before retaining children; the comparison statement already existed, so no duplicate was delivered. The functorial construction is an unsplit statement node because it is not in pinned Mathlib; the bounded-below child is an exact Mathlib leaf. Edge cases checked were the zero complex, identical resolutions, and a one-degree complex with an injective term. JSON escaping, node existence, proof-dependency union, and blueprint fields were checked before preflight.
