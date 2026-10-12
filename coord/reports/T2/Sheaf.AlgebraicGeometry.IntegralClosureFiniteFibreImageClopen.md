## What changed

Proved `AlgebraicGeometry.integralClosure_finiteFibre_image_clopen` without changing its
signature or existing docstrings. The complete Lean proof constructs the quotient map,
proves closedness from finiteness and integrality, proves the inverse-image equality
using the restricted scheme isomorphism, obtains and identifies the unique idempotent,
and applies the remaining first-factor identification lemma.

Added proof-only imports of `Sheaf.AlgebraicGeometry.QuotientFirstFactorImageOpen` and
`Sheaf.AlgebraicGeometry.QuotientFirstFactorIso`. The first module is fully proved;
the second states the remaining product/localization/quotient argument in general rings,
without the finite-type or finite-module hypotheses. Updated the item's DAG proof to
match the Lean proof. No existing statement or definition changes.

Repair: removed the duplicate private `firstFactor_range` calculation from this item. The shared theorem is now exposed by `QuotientFirstFactorImageOpen` and imported and used directly here, satisfying the import-prune review.

The source was read at [Stacks Tag 09XH](https://stacks.math.columbia.edu/tag/09XH),
because the referenced local TeX file is absent on this clone. All three modules compile
without warnings with the mandated compiler. The unit is sk-thm-p1; this node is below
its realized steps, and the source's mathematical route is preserved.

## Proved and sorry left

Removed the only original sorry:
`AlgebraicGeometry.integralClosure_finiteFibre_image_clopen`
(node `lem-weil-pbc-integral-closure-finite-fibre-image-clopen`). It now has a complete
proof from named declarations, with one transitive remaining sorry.

Hole accounting: one original hole closed and one new lower hole added; net zero.
This is a decomposition, not an axiom-free proof of the original item.

Also proved `AlgebraicGeometry.quotient_firstFactor_image_isOpen`
(node `lem-weil-pbc-quotient-first-factor-image-open`). Its private first-factor spectrum
calculation and open-map argument are fully proved.

The only sorry in the delivery is
`AlgebraicGeometry.quotient_firstFactor_equiv_of_restrict_iso`
(node `lem-weil-pbc-quotient-first-factor-iso`), in its own module. Its docstring and node
contain the full argument: idempotent product decomposition, separating the first factor
from the closed complement of U, localization isomorphism, and corresponding quotient
ideals. This is strictly the last part of the original theorem: it assumes an already
identified idempotent and proves no clopenness, image equality, uniqueness, integrality,
or inverse-image equality.

Edge cases checked for both new statements: zero rings, zero or unit ideals, zero and
unit idempotents, and an empty open U. A zero first factor gives an empty spectrum and
the zero factor ring; no Nontrivial assumptions are needed. For U empty, the supported
first factor has empty spectrum and is the zero ring. Arbitrary universes of the target
factors are kept; the source factors are quotient rings in the source-ring universe.

## No longer needed

No pre-existing source import was removed: both public imports are required for the
unchanged statement. A trial proof import of
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic` was removed after checking
that the existing public imports already provide the required integral-tower lemmas.
It was not present on the base.

No original DAG dependency is globally pruned: the quotient, integral, closed-map,
idempotent and spectrum nodes are still used directly, while the basic-open separation,
section-ring and localization nodes are now dependencies of the remaining first-factor
lemma. They are no longer direct proof dependencies of the item's node, but remain
necessary for that smaller argument. Specifically, the following old direct dependencies
are no longer direct dependencies of the item (all four remain dependencies of
`lem-weil-pbc-quotient-first-factor-iso`):

- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`;
- `lem-weil-pbc-morphism-into-affine-scheme`;
- `lem-weil-pbc-affine-ideals-closed-subscheme`;
- `def-weil-ring-localization-away`.

No unused Sheaf proof modules were imported. The item’s duplicate first-factor helper and proof are no longer needed; the imported theorem is shared by both modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The local TeX source named by the node is unavailable;
the authoritative Stacks page was read instead. `range_comap_of_surjective` is a root
namespace declaration with the target ring as an explicit parameter, despite the old
node's `PrimeSpectrum.` qualification. Existing
`IntegralClosureFiniteFibreChooseG` requires algebra structures and compatibility on
both product factors not included in this theorem, and does not itself conclude the
first-factor quotient isomorphism. It was read but not imported or duplicated.

LeanSearch returned Internal Server Error twice. This unavailable search is recorded
without a negative verdict; LeanFinder, Loogle, source grep, and two blueprint searches
provided the remaining checks.

## New nodes

`lem-weil-pbc-quotient-first-factor-image-open`, module
`Sheaf.AlgebraicGeometry.QuotientFirstFactorImageOpen`: a general relative-openness lemma
for a quotient factor on a restricted scheme isomorphism locus. Fully proved, using a
lift of the product idempotent and the open-map property of the restricted morphism.

`lem-weil-pbc-quotient-first-factor-iso`, module
`Sheaf.AlgebraicGeometry.QuotientFirstFactorIso`: the remaining factor identification,
with induced quotient map, idempotent compatibility and support in U supplied as
hypotheses. One named public sorry; complete source proof in the node and docstring.
No change records are needed because existing public interfaces are unchanged.


## Earlier second reading (a previous round; superseded)

1. Compared the complete item module with the repository version using `diff -u`.
   The existing declaration signature and docstrings are byte for byte unchanged;
   only two proof imports, a private proved helper and the theorem proof were added.
   Both other modules and their nodes are new. No existing definition changed and
   no change record is required. Verdict: passes.
2. Compiled all three modules in import order with the mandated `lcompile.py`:
   no errors or warnings. Searched all delivered Lean for forbidden declarations
   and for `sorry`: the sole occurrence is the reported public factor-isomorphism
   theorem, whose body is exactly `by sorry`. A scratch module printed axioms:
   the openness theorem uses only `propext`, `Classical.choice`, `Quot.sound`;
   the item and factor-isomorphism theorem additionally use `sorryAx`, as expected
   from the single open dependency. No hollow definitions. Verdict: passes as a
   partial proof, not an axiom-free closure of the item.
3. Read both new statements, their complete proofs in words, and their nodes.
   The factor-isomorphism statement is strictly the last part of the argument:
   it assumes the idempotent, its compatibility and its support, and does not
   establish clopenness, inverse-image equality or uniqueness. Checked the
   Chinese-remainder factors, the identity t*K' contained in J', the separating
   lift g=t*l, and correspondence of quotient ideals after localization.
   For c=0 or U empty the first factors are zero rings; for c=1 the argument is
   the quotient map on a closed subscheme supported in U. Zero rings and unit
   ideals cause no Nontrivial assumption. Repeated independent searches with
   LeanFinder (closed-subscheme base change near its support), Loogle
   (`PrimeSpectrum.comap, RingHom.fst`), and grep (quotient/isIso and range of
   comap/fst), plus local Sheaf and upstream sources. Found closed-immersion,
   CRT and spectrum ingredients, but no theorem already stating either new
   result. The remaining geometry/localization formalization is not a short
   repair. Verdict: both true; the reported split is justified.
4. Read the proof from the conclusion downward and checked each import against
   its use. The item proves the quotient construction, integral closed image,
   inverse-image equality, unique idempotent and its compatibility directly
   using Mathlib; the general openness helper is fully proved. The two original
   public imports are needed for the unchanged signature, the two new imports
   are proof-only, and the new modules need Restrict in their signatures.
   Read sk-thm-p1's `realized` fields: this item is below its realized nodes and
   neither new lemma bypasses a unit step. Checked the source argument against
   [Stacks Tag 09XH](https://stacks.math.columbia.edu/tag/09XH).
   Verdict: route preserved; pruning report needed the explicit names below.
5. Compared all three nodes with their Lean statements and proofs, checked
   proof-step uses against proof_deps and checked the new-node metadata,
   source, searches, chapter, unit and declaration records. The item's old
   dependencies removed from its direct proof are exactly the four now named
   under No longer needed; they remain in the factor-isomorphism node.
   Verdict: nodes agree, with no globally pruned node.

Second reading changed only this report: explicitly listed all four removed
old direct dependencies and recorded the review and axiom evidence. No Lean
proof, statement, definition, import or DAG repair was needed.


## Second reading by T2

1. Compared the item with the repository using diff, and compared its declaration
   prefix through `:= by` byte for byte. The signature and existing docstrings
   are unchanged. The two other modules are new; no definitions or existing
   interfaces changed. Verdict: passes.
2. Independently compiled all three modules with `lcompile.py --all`: clean.
   The forbidden-declaration scan finds only the named public sorry
   `AlgebraicGeometry.quotient_firstFactor_equiv_of_restrict_iso`. A scratch
   axiom check shows only propext, Classical.choice and Quot.sound for the
   openness theorem; the item and factor theorem additionally use sorryAx.
   No definitions contain sorry. Verdict: valid decomposition with one open hole.
3. Read both new statements, their nodes and proofs in words against
   [Stacks Tag 09XH](https://stacks.math.columbia.edu/tag/09XH). In the remaining
   lemma, K'=J'+(1-t) is supported in U. Separation gives 1=l+k and g=t*l;
   t*K' is contained in J', so g-t is in J'. Localization at g preserves the
   first quotient because g becomes 1; the corresponding ideals are carried
   to each other by the localization isomorphism. This proves precisely the
   first-factor map, with the second induced map supplied by CRT. For c=0,
   U empty, or J'=top the first factors are zero rings; c=1 reduces to the
   quotient supported in U. The zero source ring forces a zero target ring.
   No nontriviality or universe assumption is missing. The lemma assumes the
   compatible idempotent and proves none of its construction, uniqueness,
   clopenness or inverse-image equality, so it is strictly a final subargument.
   Independent LeanFinder search for base change on a neighborhood of a closed
   subscheme, Loogle search for comap/fst, Mathlib grep for quotient isomorphisms
   and local Sheaf/upstream grep found ingredients, no direct duplicate.
   IntegralClosureFiniteFibreChooseG is now proved but requires the product
   factors and extra algebra compatibility data and does not identify the
   first factor. Closing the remaining localization/CRT formalization is not
   a repair achievable in a few minutes. Verdict: true, needed and simpler.
4. Read the item from its final application upward. Its quotient map, integral
   closed image, inverse-image equality and compatible unique idempotent are
   proved directly. The firstFactor_range theorem is genuinely shared with
   the openness proof, and all imports are used. The original public imports
   support the unchanged signature; the added imports are proof-only. The
   four old direct dependencies removed are explicitly listed above and remain
   in the lower factor node. Checked sk-thm-p1.realized: this argument is below
   its realized nodes and bypasses no unit step. Verdict: route and pruning pass.
5. Compared the Lean statements and proofs with all three node files. Metadata,
   source, search records, chapter, unit and declaration signatures agree.
   Found one stale description calling firstFactor_range private: repaired it
   to name the shared theorem and added its openness node to that step's uses;
   it was already in proof_deps. Verdict: nodes agree after this repair.

Second reading changed the report to state the zero net hole count and record
this independent audit; added a source/proof docstring to the shared proved
firstFactor_range auxiliary theorem; corrected the stale DAG step description
and citation. No Lean proof, statement, definition or import changed.
