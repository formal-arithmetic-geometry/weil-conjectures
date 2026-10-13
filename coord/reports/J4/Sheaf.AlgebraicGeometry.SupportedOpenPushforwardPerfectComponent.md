## What changed

Proved `AlgebraicGeometry.Scheme.supported_open_pushforward_perfect` without changing
its signature or any definition. The proof constructs the exact open restriction/direct
image adjunction and uses full faithfulness of derived direct image to obtain an invertible
counit. It transports the perfect models on U through that counit. It then handles each
point by cases: in U, recover an ambient strictly perfect local model; outside U, use
T contained in U and the complementary-open vanishing lemma, then construct the zero
strictly perfect complex and its derived isomorphism explicitly.

Added two modules, each with a complete proof:
`Sheaf.AlgebraicGeometry.OpenRestrictionPerfectLocalModels` and
`Sheaf.AlgebraicGeometry.SupportedOpenPushforwardComplementZero`.
The first builds the exact equivalence of localized module categories from `overEquiv`
and the scheme isomorphism `U.ι.isoImage W`, transports finite free retracts, and derives
the restriction square. The second uses the existing private localization-transport helper from
`Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall` via a proof-only `import all`
to transport chosen localizations to open subschemes,
uses exact restriction and the stalk isomorphism to prove vanishing of all cohomology,
and applies the existing derived direct image/open restriction comparison.
All existential elimination is inside proofs. The only new definition is a private
concrete exact equivalence built from restriction functors and their composition and
identity isomorphisms; it has no deferred data or proof.

The supplied source was read at
[Stacks 08DP](https://stacks.math.columbia.edu/tag/08DP),
[Stacks 08FE](https://stacks.math.columbia.edu/tag/08FE), and
[Stacks 08CM](https://stacks.math.columbia.edu/tag/08CM).
The unit record `sk-thm-picard-duality` has no realized statement or step that this route
bypasses. The original two-open proof route is preserved.

Compilation: the three delivered modules compile with `lcompile.py`, in import order,
with no warnings. The local-model module also compiles with the default heartbeat limit.
The pointwise case split covers empty X and U, empty T, and total U. The vanishing lemma
requires neither perfection nor closedness nor T contained in U: only that the tested
open is disjoint from T, so it remains true in those cases. The local-model lemma asserts
nothing outside U and has no support or pushforward hypothesis.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.Scheme.supported_open_pushforward_perfect`
(node `lem-pc-supported-open-pushforward-perfect-component`).

The two new public theorems are also proved:
`AlgebraicGeometry.Scheme.open_restriction_perfect_local_models`
(node `lem-pc-open-restriction-perfect-local-models`), and
`AlgebraicGeometry.Scheme.supported_open_pushforward_complement_zero`
(node `lem-pc-supported-open-pushforward-complement-zero`).
Their private helpers are fully proved/constructed.

No sorry remains in any delivered module. Holes closed: 1. Holes added: 0.
This is a proof from existing library declarations, not a decomposition into new holes;
the existing imports may still depend on earlier library sorries.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` from the item's module.
It is still used by the proved complementary-open component and hence remains in the
transitive import closure. No existing node or module is globally pruned by this delivery.
The old direct proof dependency `lem-pc-restrict-derived-direct-image-open` is no longer
in the item's `proof_deps`: it is now used by
`lem-pc-supported-open-pushforward-complement-zero`. It remains a transitive dependency;
`def-pc-perfect-complex`, the other old proof dependency, remains directly used.
The two public statement imports, `PerfectComplex` and `SchemeDerivedDirectImage`, remain.
New proof imports in the item are the two local components and the source-library
`RightDerivedFunctor.Adjunction` and `RightDerivedFunctor.FullyFaithful` APIs.
Removed `Mathlib.CategoryTheory.Localization.Equivalence` from the complementary-open
module: the deleted duplicate helper was its only direct user. The localization-transport
helper `hasDerivedCategory_of_equivalence` is reused from
`Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall`. Its smallness theorem is not
used; the node records the helper API explicitly in its localization-transport step,
without citing the unrelated smallness statement. No existing module is adapted.
Every other delivered import supports a statement or a used proof API; no dependency of
the original plan was silently bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private theorem
`hasDerivedCategory_of_equivalence` already present in
`Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall`. Removed that declaration
and reused the existing theorem through `import all`; ordinary `import` does not expose
this private helper. No visibility change or forced adaptation is needed.

No mathematical error or statement change was found. The original first step compressed
zero-stalk detection, zero detection by derived cohomology, and transport between scheme
and over-site localizations. Its second step compressed transport of strictly perfect
models across the localized-site equivalence. This delivery supplies those details in Lean.
The physical local copy of `literature/stacks-project/cohomology.tex` is absent on this
machine; the cited official Stacks pages supplied the source text. LeanSearch returned
Internal Server Error for both new statements; Loogle/LeanFinder, local Mathlib grep,
and searches in both library roots supplied the component APIs. No claim of a successful
LeanSearch absence check is made.

## New nodes

`lem-pc-open-restriction-perfect-local-models` records the proved local model transport
from a perfect derived restriction on U to ambient neighbourhoods of points in U.
It is a general locality component, with neither support nor direct image hypotheses.
Its Lean proof constructs the model, finite free comparisons, retraction equations,
and derived comparison. Source: Definition 08CM and the locality step of 08DP.

`lem-pc-supported-open-pushforward-complement-zero` records proved vanishing of derived
open pushforward on any open disjoint from the given cohomological support. Its statement
has no perfectness, closedness, or containment hypothesis. Its proof uses the existing
08FE theorem, with zero-stalk glue proved locally and localization transport reused from the existing
private helper in `PerfectRestrictionClassesSmall`.
Source: the vanishing step of 08DP using 08FE.

The original node's `proof`, `proof_deps`, and `proof_origin` now match the complete Lean
proof and these two components. No change record is necessary: no existing statement,
definition, visibility, or public import was changed; no forced adaptation was made.

## Second reading by J4

1. PASS: Read all three delivered modules and compared the existing module with the
   repository using diff. Its theorem signature and docstring are byte-for-byte unchanged;
   only proof-only imports and the proof body change. The other two modules are new.
   The existing node changes only proof, proof_deps and proof_origin. No statement,
   public import, definition or visibility of an existing declaration changes.
2. PASS: Independently compiled all three files in import order through lcompile.py,
   without errors or warnings (29.2, 17.3 and 14.1 seconds). Fresh scratch copies with
   #print axioms compiled too: each of the three public theorems uses exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. Scanned all delivered Lean sources:
   no sorry, axiom, unsafe, opaque, implemented_by, extern or sorryAx. The private
   equivalence is a concrete construction. The reused localization helper is itself
   proved and explicitly constructs the transported localization; the existential
   eliminations occur only in proofs, with no arbitrary data from an unproved existence.
3. PASS: No statement is split off with sorry. Read both new statements, their full
   proofs and docstrings. The first only recovers models at points in U; it is vacuous
   for empty U and unchanged in meaning for total U. The second requires exactly
   vanishing stalks on the inverse image of V: empty U/V/T and total U cause no missing
   case. Neither component restates the original theorem. Independently searched with
   LeanFinder for local models under open-site equivalences and for zero derived open
   image where cohomology stalks vanish, and with Mathlib grep for zero-stalk and local
   perfectness APIs. Read matching library modules, including PerfectOfOpenPullbacks,
   SchemeIsoPerfectLocalTransport and SupportedOpenPushforwardLocalComparisons: none
   supplies either exact component under these hypotheses. The stalk and transport
   ingredients returned by the searches are already used.
4. PASS: The proof starts with the exact adjunction and fully faithful right derived
   functor, uses the proved local-model component on U and the proved zero component
   off T, and explicitly constructs the zero strictly perfect complex. Reviewed each
   import against its statement or proof APIs; proof-only APIs have plain imports,
   including the deliberately private helper accessed via import all. No shorter
   complete route was found. The No longer needed section accounts for both old
   proof dependencies and correctly reports no global pruning. Read the unit's
   realized record (empty statement and step arrays): no realized route is bypassed.
   Re-read official Stacks 08DP, 08FE and 08CM; the two-open argument matches them.
5. PASS: Checked all three node signatures against Lean verbatim, proof steps against
   the code, and proof_deps against the union of uses. Checked the new-node source,
   searches, creation, blueprint, chapter, unit and Lean records. The reused private
   helper is identified explicitly rather than citing the unrelated smallness theorem.

Changes by the second reader: added this independent review and fresh validation
results only. No Lean or node repair was needed. One original hole closed, zero holes
added; both new components are proved, not deferred split-off statements.
