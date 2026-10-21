## Worker report

Item: `lem-sfb-small-triangulated-extension-classes` (O2, stage 2).

Record the exact existing declaration
`CategoryTheory.ObjectProperty.essentiallySmall_extensionProduct`, an instance in
`WeilConjectures.CategoryTheory.Triangulated.ExtensionProductEssentiallySmall`,
lines 41–43. No module, definition, theorem, proof, or dependency node is added.
Only the item’s `lean` field changes. The existing module was read in full both
from the read-only source and with `scompile.py --source`; the server source
agrees. Its complete context and statement are:

```lean
universe w v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
instance essentiallySmall_extensionProduct [LocallySmall.{w} C] (P Q : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (P.extensionProduct Q)
```

The `lean.statement` is the signature verbatim from `instance` to immediately
before `:=`; the surrounding binders are given above for review. `slopmaster2`
is the existing-WeilConjectures branch record required by the delivery checker;
the declaration is resolved and checked in the live published library.

Hypotheses and clauses, individually:

- Fixed universe V: the explicit universe `w`, used in all three smallness
  hypotheses/conclusions. Object universe `u` and Hom universe `v` are independent
  of `w`; no equality or size restriction between them is added.
- Pre-triangulated category T: `C : Type u`, `[Category.{v} C]`,
  `[Preadditive C]`, `[HasZeroObject C]`, `[HasShift C ℤ]`,
  `[∀ n : ℤ, (shiftFunctor C n).Additive]`, `[Pretriangulated C]`.
  These are exactly the recorded Mathlib encoding of
  `def-weil-triangulated-category` (TR1–TR3). Binary biproducts follow from
  pretriangulation; an extra additive-category assumption is unnecessary.
- V-small Hom sets: `[LocallySmall.{w} C]`, whose field is
  `∀ X Y : C, Small.{w} (X ⟶ Y)`.
- Two arbitrary object classes: `(P Q : ObjectProperty C)`. Neither is assumed
  nonempty, closed under isomorphisms, triangulated, or bounded.
- Each class has a V-small representative family: the two instances
  `[ObjectProperty.EssentiallySmall.{w} P]` and
  `[ObjectProperty.EssentiallySmall.{w} Q]`. Mathlib defines this as containment
  in the iso-closure of a small object predicate (Small.lean:101–106).
  Representatives in the original class can equivalently be selected using
  `EssentiallySmall.exists_small_le` (108–126), including the empty class.
- The extension class P*Q: `P.extensionProduct Q`. At
  Mathlib/CategoryTheory/Triangulated/Subcategory.lean:206–214 this means
  existence of `Y Z : C`, arrows `Y ⟶ X`, `X ⟶ Z`, `Z ⟶ Y⟦1⟧`, a distinguished
  `Triangle.mk` on those arrows, and `P Y ∧ Q Z`. Thus `Y`, `X`, `Z` respectively
  denote the node’s `B`, `M`, `C`, with exactly the stated arrow order and shift.
- The node additionally permits objects isomorphic to that middle term. This
  is the same predicate: the instance at Subcategory.lean:244–249 proves that
  `extensionProduct P Q` is closed under isomorphisms for arbitrary P and Q.
  Its proof transports the first two arrows through the middle-term
  isomorphism, retaining both endpoints and the third arrow. Consequently no
  extra iso-closure assumption on P or Q, and no replacement by a different
  notion, is needed.
- Conclusion: `ObjectProperty.EssentiallySmall.{w} (P.extensionProduct Q)`
  asserts exactly a V-small family of representatives for the extension class.
- No functorial cones, abelian heart, boundedness, Tor amplitude, or octahedral
  axiom occurs in the declaration. In particular `[IsTriangulated C]` is absent.

Dependency declarations read and used:

- `def-weil-size-convention`: its recorded `lean` is explicitly a convention,
  with no module/declaration. It is implemented by the explicit common `w`.
- `def-weil-triangulated-category`: its `mathlib_match` is
  `CategoryTheory.Pretriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`. Read its complete
  class signature and docstring at lines 43–87. The match’s additional
  `[IsTriangulated C]` describes triangulated categories; this item asks only
  for pre-triangulated categories, as does the existing instance.
- The proof dependency `lem-sf-triangle-morphism-iso` is the existing Mathlib
  two-out-of-three result, used by the existing proof as
  `Pretriangulated.isIso₂_of_isIso₁₃`. No new proof module is necessary.

Sources read: the item’s source proof in the current blueprint,
`sec-six-functors-basics/sk-lem-brown-hypotheses/sk-lem-brown-hypotheses-small.proof.md`,
Essentially-small paragraph; and Stacks `derived.tex`,
`lemma-third-isomorphism-triangle` (014A), lines 414–452, and
`lemma-cone-triangle-unique-isomorphism` (014B), lines 541–556.
The module’s proof at lines 44–67 is already written: choose small endpoint
representatives, count the dependent sum of shrunk connecting Hom types,
complete each arrow, compare triangles with endpoint isomorphisms using TR3,
and apply 014A to the middle component. This is the node’s four-step argument.
The existing proof is reused without editing it or introducing a duplicate.

Edge cases checked against the definitions and the existing proof:

- If P or Q is empty, the extension predicate is empty; Mathlib explicitly
  records `extensionProduct_bot_left` and `extensionProduct_bot_right` at
  Subcategory.lean:220–230. The dependent sum of endpoints is empty as well.
- Zero objects and zero connecting morphisms are permitted: no nonzero or
  nonempty hypotheses occur, and the construction completes every arrow.
  The zero category and P=Q={0} have a single isomorphism class of middle terms.
- For non-isomorphism-closed endpoint classes, middle-term isomorphisms
  transport the triangle without altering the chosen endpoints. This checks
  the only apparent wording difference between the node and the existing API.
- Repeated representatives are allowed; essential smallness imposes no
  injectivity requirement on the family.
- All smallness assertions use the same `w`, independently of `u` and `v`.
  In particular the result does not claim smallness in an unspecified fresh
  universe, and does not require all objects of C to form a small type.

Searches actually run (2026-10-21):

- `msearch.py`, leanfinder: “Extensions of two essentially small object classes
  in a locally small pretriangulated category form an essentially small class”.
  Eight hits, including `Triangulated.Subcategory.ext₂`, `ext₂'`, `ext₁`,
  `ext₁'`, `ObjectProperty.IsTriangulatedClosed₂`, and related closure facts;
  no Mathlib smallness theorem for extension products.
- `msearch.py`, loogle:
  `CategoryTheory.ObjectProperty.EssentiallySmall, CategoryTheory.ObjectProperty.extensionProduct`.
  Zero hits.
- `msearch.py`, grep:
  `essentiallySmall.*[Ee]xtension|[Ee]xtension.*[Ee]ssentiallySmall`,
  subdirectory `CategoryTheory`. Zero Mathlib hits.
- `msearch.py`, leansearch: “Extensions between two essentially small classes
  of objects in a locally small pretriangulated category form an essentially
  small class”. Eight hits, including `locallySmall_self`,
  `ObjectProperty.instEssentiallySmallFullSubcategoryOfLocallySmallOfEssentiallySmall`,
  `essentiallySmall_of_small_of_locallySmall`, and `Triangulated.Subcategory`;
  no exact Mathlib match.
- `rg -n 'essentiallySmall_extensionProduct|small.*extension|extension.*[Ss]mall'`
  in `lean/WeilConjectures` and `lean/Sheaf`: the exact existing instance is in
  the module recorded above, and BoundedEssentiallySmall.lean uses it at line 64;
  no Sheaf duplicate was found.
- `rg -n 'lem-sfb-small-triangulated-extension-classes|essentiallySmall_extensionProduct'`
  over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  the same exact instance and its existing caller; the node id has no separate
  source declaration. The node already records this instance as a candidate;
  this delivery verifies its statement and server availability for stage 2.

No statement correction, disputed statement, missing notion, dependency repair,
or new node is needed. The example Sheaf CompactObject module is withdrawn;
its node points to the upstream module, which was read for the current
existing-declaration convention.

Validation: the sandbox-only import/#check/axiom probe passed `scompile.py`
cleanly against the live published library (both sandbox and library checks).
The elaborated type has exactly three independent universe parameters, with
the same smallness universe throughout. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The
`deliver2.py --no-push` additionally checks the existing declaration on the live
server and runs the prescribed preflight. Independent review is left to the
maintainer as required by the dispatcher brief.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
