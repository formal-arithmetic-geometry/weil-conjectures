## What changed

Closed the only hole in `AlgebraicGeometry.derived_open_intersection_mate_isIso`, keeping
its full signature and visibility unchanged. Its proof first proves both arbitrary open
adjunction counits invertible using full faithfulness of derived open direct image.
The inverse law of `adjW.homEquiv` identifies the specified mate's restriction to W,
followed by the W counit, with the transported P counit. Cancellation proves that
restriction invertible; the overlap detection theorem then proves invertibility on O.

Two new, completely proved modules make the geometric and categorical steps reusable:
`DerivedOpenIntersectionEssentialImage` and `DerivedOpenIntersectionIsoDetection`.
The first uses `schemeDerivedDirectImage_openRestriction`, the explicit inverse-image
open isomorphism, a constructed module-sheaf equivalence, the derived open adjunction,
and uniqueness of right adjoints. The second constructs the overlap derived adjunction
and reflects invertibility between objects in its right adjoint's essential image.
Their proof imports are non-public. The existing item's proof-dependency import of
`DerivedDirectImageOpenRestriction` moves to the essential-image module.

All three modules compile without warnings through `lcompile.py --all`; the longest
single-file compile was approximately 12 seconds. No definition contains an admission,
and no object was chosen from an unproved existence statement. The derived category of
the auxiliary inverse-image open uses its standard morphism universe internally; the
four existing derived-category parameters retain their original universe and instances.

## Proved and sorry left

Closed: `AlgebraicGeometry.derived_open_intersection_mate_isIso` (1 original hole).

Added and proved:
- `AlgebraicGeometry.derived_open_intersection_mem_essImage`, node
  `lem-sc-derived-open-intersection-essential-image`.
- `AlgebraicGeometry.derived_open_intersection_isIso_of_restriction`, node
  `lem-sc-derived-open-intersection-iso-detection`.

There are no sorries left in the delivered modules and no new holes. The private helpers
`moduleIsoEquivalence`, `reflects_on_essential_image`, and `open_counit_isIso` are complete.
This closes a hole rather than decomposing it into new holes.
`#print axioms` for the item and the detection theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, so the closed item has no admitted dependency.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
from the item; it remains needed indirectly through `DerivedOpenIntersectionEssentialImage`.
No existing dependency module is pruned from the total import closure. The old
`proof_deps` node `lem-pc-restrict-derived-direct-image-open` is no longer a direct
dependency of the item; it remains used by the essential-image lemma. The other
old dependency, `def-pc-derived-open-restriction-maps`, remains used directly.

The old proof plan's sectionwise identification of the specified mate on a K-injective
representative, and its separate conjugation argument for arbitrary adjunctions, are
unneeded. The hom-equivalence inverse identity and invertible counits prove the specified
map invertible on W for the supplied adjunctions directly. No nodes or modules encode
those removed steps separately. The unit's route is unchanged.

The exploratory `Mathlib.CategoryTheory.Adjunction.Unique` import was removed from the
new essential-image module after checking that the remaining imports provide the API.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan correctly described the mathematics but required checking the specified
mate sectionwise after choosing resolutions. The existing Tag 08FE theorem exposes an
abstract natural isomorphism, not a formula identifying that mate. That formula is
unnecessary: invertibility on W follows formally, and restriction reflects invertibility
on O for the relevant essential-image objects.

Read Stacks Tags 08FE and 08DG at their official pages because the cited local tex file
is absent on this machine. Both comparisons apply to unbounded derived categories.
Edge cases checked in the argument: empty O or P, empty W, O = X, P = X, and W = P.
There is no covering assumption and no reflection claim for arbitrary objects of D(O).
LeanSearch returned an Internal Server Error; this is recorded as unavailable, with
LeanFinder, Loogle, and source searches recorded separately.

## New nodes

`lem-sc-derived-open-intersection-essential-image` records the geometric comparison:
restriction of RjP_* B to O lies in the essential image of any right adjoint to restriction
from O to W = O ∩ P. It introduces no mate or morphism-invertibility hypothesis and is
proved in `lean/Sheaf/AlgebraicGeometry/DerivedOpenIntersectionEssentialImage.lean`.

`lem-sc-derived-open-intersection-iso-detection` records reflection of invertibility from
W to O for maps JP(B) → JW(C), using the first node and the canonical nested-restriction
comparison. It is proved in
`lean/Sheaf/AlgebraicGeometry/DerivedOpenIntersectionIsoDetection.lean`.

Both inherit the item's chapter, unit, and nearest blueprint ancestor. No change record
or forced adaptation is needed: no existing signature, definition, or visibility changed.


## Second reading by Y2

1. **Interface: PASS.** Compared the delivered item with the repository using diff
   and independently compared the complete theorem signature byte for byte. It is
   identical, including all universe parameters, instances, adjunctions, and the
   specified mate. The only added declarations are private proof helpers and the
   two new proved theorems. No existing definition, visibility, target, or other
   module is changed. No change record is necessary.
2. **Proof and axioms: PASS.** Compiled all three delivered modules in import order
   using `lcompile.py --all`, with no warnings or errors. Independently compiled
   scratch copies with `#print axioms` for all three public theorems: each reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`. Source scanning found no
   admissions or forbidden declarations. The private equivalence is built from
   actual pushforward functors and composition isomorphisms; the auxiliary derived
   category uses the standard construction. The base-change Nonempty witness is
   eliminated only within a theorem proof, never used to define arbitrary data.
3. **New statements: PASS.** Both new statements are proved, so there are no open
   split-off statements. Read their full proofs and docstrings and checked the
   strength needed by each use. The essential-image lemma supplies both objects
   in the detection lemma; the latter handles any map between the specified direct
   images, and does not restate the mate theorem. Empty O, P, or W and the cases
   O = X, P = X, and W = P preserve the image identities and adjunction argument.
   Searched independently for essential-image conservativity with LeanFinder,
   queried the unit/essential-image characterization with Loogle, and searched
   Mathlib's adjunction API plus both Lean library roots. Mathlib provides the
   unit characterization already used; no duplicate geometric comparison or
   shorter theorem for the specified unbounded mate was found.
4. **Route and pruning: PASS.** Read the two cited Stacks pages (Tags 08FE and 08DG),
   the existing open-restriction comparison, and the unit's `realized` record.
   The argument keeps the open-gluing local comparison and changes only its
   implementation below the unit level. No unit realization is removed or bypassed.
   Proof-only imports are non-public and each supplies its geometric theorem,
   derived adjunction API, or derived full-faithfulness instances. The old direct
   dependency moved below the essential-image lemma is now named explicitly in
   `No longer needed`; no module is pruned from the whole import closure.
5. **DAG: PASS.** Independently checked each node's recorded Lean statement against
   the actual declaration signature and checked that `proof_deps` is the union
   of its proof steps' `uses`. Read every proof step against the Lean argument.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   The new nodes contain source, searches, creation and blueprint provenance,
   chapter/unit, and complete Lean records, and introduce no unresolved holes.

Changed during second reading: replaced the item's stale sectionwise-proof
paragraph with the actual proof using invertible counits, the hom-equivalence
inverse identity, and essential-image detection. Added the explicit old dependency
node accounting above. No proof term or statement needed repair.
