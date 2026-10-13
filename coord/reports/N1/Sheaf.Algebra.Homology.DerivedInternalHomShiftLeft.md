## What changed

Replaced the hole in `CategoryTheory.derivedInternalHom_shift_left` without changing its
signature or existing docstring. Its proof uses the existing, proved functorial representative
comparison, commutes shifts across the derived localization, descends the resulting natural
isomorphism using `Localization.fullyFaithfulWhiskeringLeft`, and transports along a complex
representative of the arbitrary derived source. The opposite-category isomorphisms are used
in their contravariant directions.

Added the proof-only import `Sheaf.Algebra.Homology.HomComplexShiftLeft` and a module for the
signed source-shift calculation on complexes, with a complete proof. Updated the item's proof dependencies to match
this route. No existing interface, definition, visibility or target statement was changed.

## Proved and sorry left

Closed the item's single hole: `CategoryTheory.derivedInternalHom_shift_left`
(`lem-pur-derived-internal-hom-shift-left`). The localization and transport proof compiles
cleanly with `lcompile.py`.

Also proved the new `CategoryTheory.homComplex_shift_left`
(`lem-pur-hom-complex-shift-left`). The new module constructs the degreewise maps from
the existing product projections, proves both inverse identities, checks the signed
differential equation, and verifies naturality by projection extensionality.

Holes closed: 1 original hole. Holes added: 0. Every delivered public and private theorem
has a complete proof; no `sorry` remains in either module. No definition or existing
signature was changed. Both declarations' compiled `#print axioms` lists are exactly
`propext`, `Classical.choice`, and `Quot.sound`. The complete sandbox compilation passes
without warnings.

## No longer needed

Second reading removed the unnecessary public import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` from the new
`HomComplexShiftLeft` module. It is not a pruned DAG node or a claim of global pruning.

No import from the original module was removed: its single public import
`Sheaf.Algebra.Homology.DerivedInternalHom` is needed by its unchanged statement.

The separate node `prop-pur-kinjective-resolutions-exist` and module
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` are not needed by this proof:
the standard source-library resolution functor and its proved properties suffice, and the
additional generator assertion is irrelevant to this comparison. This removes that direct
planned dependency, rather than proving its unused generator clause.

There is no direct use or added import of `lem-pur-rhom-well-defined` /
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`; that node remains a transitive dependency
of the existing derived Hom representative comparison, so no global pruning of it is claimed.
`def-pur-hom-complex` is retained through the lower complex comparison.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The plan hid the explicit signed comparison and did not
supply a declaration for it. The new, proved node isolates that complex-level step. The lengthy
hand-written descent argument in the plan is replaced by Mathlib's fully faithful
precomposition API for localization. The unit record `sk-thm-picard-duality` has empty
`realized` entries for this auxiliary calculation; its statement and route are untouched.

The cited Stacks TeX file is absent from this machine's read-only literature checkout.
The official Stacks pages for Tags 0A8X and 08JA were read instead. Tag 0A8X supplies the
Hom differential; the source-shift sign calculation is explicitly recorded as agent-written.
Searches used LeanFinder, Loogle, grep and the required LeanSearch call; LeanSearch returned
an Internal Server Error and is recorded as unavailable. Blueprint search for `Hom shift`
found 34 broad matches but no natural isomorphism of sheaf-valued Hom complexes on a site.

## New nodes

`lem-pur-hom-complex-shift-left` records the underived signed source-shift comparison,
with product reindexing, inverse identities, differential compatibility and naturality in
the target complex. Its statement allows every integer shift, unbounded and zero complexes,
and empty sites. The sign ratio calculation uses no parity, characteristic or boundedness
restriction. Its module is `Sheaf.Algebra.Homology.HomComplexShiftLeft`; its blueprint
ancestor is `lem-sc-finite-duality`, inherited through the relative-shift comparison chain.
The new theorem is proved, not a postponed obligation. No change record or forced adaptation is needed.

## Second reading by N1

1. Compared every delivered module with the repository. The only existing module
   changes are the proof of `CategoryTheory.derivedInternalHom_shift_left`, its local
   elaboration option, and a plain proof-only import. The declaration comparison reports
   no changed statements. The original signature and docstring are byte-for-byte unchanged;
   the other module is new. No definitions, targets or existing visibility changed. Pass.
2. Read both proofs completely and compiled both modules locally with `lcompile.py --all`.
   The complex comparison constructs its maps by product limits, proves both inverse
   equations and the chain equation, and checks naturality. The derived proof uses the
   representative comparison, shift compatibility, fully faithful localization
   precomposition, and correctly directed opposite-category transport. There are no
   `sorry` occurrences or forbidden declarations in either delivered module. Pass;
   final axiom verification is recorded below.
3. No statement was split off with `sorry`. The new proved theorem is strictly the
   underived source-shift calculation and introduces no injectivity or boundedness
   assumptions. Independently checked m=0 (identity sign and reindexing), m=1
   (adjacent signs differ by -1), negative m (the same integer identities), zero
   complexes and the empty site. Repeated LeanFinder, Loogle and grep searches using
   suspension/reindexing and `leftShift` terminology. Mathlib's ordinary Hom-cochain
   operations have a different codomain and do not replace this sheaf-valued result. Pass.
4. Checked the shortest route from the target downward. The existing proved derived
   representative comparison and Mathlib localization API suffice; the new complex
   calculation is the remaining concrete step. The report accounts for all four old
   proof dependencies: derived Hom is retained, Hom complexes are used through the new
   lemma, well-definedness remains transitive, and the separate resolution-existence
   assertion is not used. The unit's `realized` statement and step lists are empty for
   this auxiliary calculation; no unit statement, step or route is replaced. Pass.
5. Compared both node records against the declarations and proofs. The existing node
   changes only `proof`, `proof_deps` and `proof_origin`; dependency unions agree with
   the steps. The new node includes its source, complete argument, searches, creation
   record, blueprint ancestry, chapter, unit and Lean signature. It has a complete Lean
   proof and adds no obligation. Pass.

Second-reading change: removed the unnecessary public import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` from the new
`HomComplexShiftLeft` module. Preadditivity is supplied by the retained public
`HomComplex` import; no abelian or Grothendieck structure is used in this calculation.
Kept the public shift import because the new theorem's signature uses the shift instance,
and kept `HomComplexProjections` as a plain proof-only import. No proof rewrite was needed.

Final second-reader verification: both final modules compile with no errors or warnings.
A scratch copy of the derived module with appended `#print axioms` commands compiled
against the final sandbox artifacts. Both `CategoryTheory.derivedInternalHom_shift_left`
and `CategoryTheory.homComplex_shift_left` depend exactly on `propext`,
`Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`. The scratch
copy is outside the delivered Lean tree. Holes closed: the one original theorem;
holes added: zero.
