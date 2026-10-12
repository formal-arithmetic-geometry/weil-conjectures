## What changed
`CategoryTheory.colimitSite_cech_complex_isIso` has the original signature verbatim and
now has a proof combining two strict sub-conclusions. The transported covering/product
clauses are in `Sheaf.CategoryTheory.ColimitSiteCechTransport`; the complex diagram,
projection equations, and colimit witness are in `Sheaf.CategoryTheory.ColimitSiteCechColimit`.
The final comparison-isomorphism clause is proved with Mathlib
`IsColimit.nonempty_isColimit_iff_isIso_desc`, rather than left in the colimit lemma.
Both new modules have public imports for their signatures. Their imports in the original
module are ordinary imports because only the proof needs them. No definition changes.

## Proved and sorry left
The original module's one open theorem, `CategoryTheory.colimitSite_cech_complex_isIso`,
has a compiling reduction, with no `sorry` in its body. It still depends on the two
unfinished lemmas below and therefore uses `sorryAx`; this is not a completed target proof.

- `CategoryTheory.colimitSite_cech_complex_transport` remains `:= by sorry`, in
  `Sheaf.CategoryTheory.ColimitSiteCechTransport`, node
  `lem-weil-pbc-colimit-of-sites-cech-complex-transport`.
- `CategoryTheory.colimitSite_cech_complex_colimit` remains `:= by sorry`, in
  `Sheaf.CategoryTheory.ColimitSiteCechColimit`, node
  `lem-weil-pbc-colimit-of-sites-cech-complex-colimit-data`.

Each is a public named theorem with a source, complete natural-language proof docstring,
and matching new node. There are no other new declarations or unfinished proofs.

## No longer needed
Removed the original module's ordinary import `Sheaf.CategoryTheory.ColimitSiteSections`:
its new proof calls the two split lemmas and Mathlib's colimit comparison criterion.
The parent's old direct proof dependencies are replaced by the two new nodes:
`def-weil-pbc-sites-and-cohomology`, `lem-weil-pbc-colimit-of-sites`,
`def-weil-pbc-site-cech-complex`, `lem-weil-pbc-colimit-of-sites-sections`, and
`lem-weil-pbc-filtered-colimits-commute-finite-limits`. All five remain in the new
lemmas' proof plans or statement dependencies; no node is claimed globally dispensable.
No unit realization or unit-level route is pruned.

## Where the brief, the DAG or earlier work was wrong
The first worker copied the entire parent statement into both split node statements,
left empty statement/proof dependencies, copied stale review/search metadata, and used
ordinary comments instead of complete sourced proof docstrings. The new lemmas also
occupied the parent module rather than their own modules. These faults are repaired.
The old parent proof plan was unchanged despite the new Lean reduction; it now records
the actual split lemmas and the Mathlib criterion.

The existing `colimitSite_sections_isIso` concerns sections of a sheaf colimit on one
site. It does not by itself identify those sections with sections of the original
stage sheaves. That additionally requires the inverse-image section formula and the
diagonal-refinement argument of Stacks 09YM/09YN. Those steps are explicitly retained
in the colimit lemma's proof plan and docstring; they have not been falsely reported
as a one-line application of the existing section theorem.

## New nodes
`lem-weil-pbc-colimit-of-sites-cech-complex-transport` states precisely the two covering
transport/product-isomorphism clauses, with projection compatibility. Its own module
is `Sheaf.CategoryTheory.ColimitSiteCechTransport`. The proof follows the Hom pullback
calculation in [Stacks 09YL](https://stacks.math.columbia.edu/tag/09YL), induction on
products, and uniqueness of the universal property.

`lem-weil-pbc-colimit-of-sites-cech-complex-colimit-data` states only the existence of
the compatible stage complex diagram and colimiting cocone, including both projection
equations. Its own module is `Sheaf.CategoryTheory.ColimitSiteCechColimit`. The source
is the displayed complex comparison in [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP),
expanded using [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN). The additional
isomorphism clause is omitted because the parent proves it from the colimit witness.

The change record is `coord/changes/colimit-site-cech-intermediates.md`; it contains
the new signatures verbatim. There are no existing users of the two new names.

## Second reading by F2
1. Compared every delivered module with the repository version. The existing module
   changes only ordinary proof imports and the theorem body. Extracted and compared
   its complete signature byte for byte: identical. Existing docstrings and definitions
   are unchanged. The two other modules are new; their additions are declared in the
   change record. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`, without errors or
   warnings. Compiled scratch copies with `#print axioms` for all three declarations:
   each lists only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
   The latter is confined to the two named split proofs in source and inherited by
   the parent. Scanned for prohibited declaration mechanisms and hollow definitions:
   none. Verdict: pass as a partial reduction, not as an axiom-free target proof.
3. Read each split statement against its actual conclusion and the source. Empty
   covering indices give no nonempty-length tuples and zero cochain groups; the
   empty product comparison is valid. In degree zero, `W_zero` identifies the chosen
   product with the original object. A singleton covering still has its genuine
   self-intersection products in higher degrees; no monomorphism or trivialization
   is assumed. For a terminal index category the construction reduces to the original
   covering and complex with canonical isomorphisms. The transported-product and
   complex-cocone assertions are strict parts of the original argument, not renamed
   copies of the original theorem. Searched the library, upstream, and the DAG by
   transport, product, refinement, and Cech terms. Ran fresh LeanFinder, qualified
   Loogle, and Mathlib grep searches via `msearch.py`; no matching full lemma was found.
   LeanSearch returned Internal Server Error, recorded as unavailable without a verdict.
   Loogle found the Mathlib comparison criterion, which is used directly. Verdict: pass.
4. Read from the main theorem down. Kept the two mathematical sub-conclusions, but
   removed the final isomorphism obligation from the unfinished lemma and proved it
   directly with Mathlib. The original module's imports are minimal for its signature
   and this proof. Listed every old direct proof dependency under No longer needed,
   distinguishing delegation from global pruning. Checked `dag/units/sk-thm-p1.json`:
   its realized statement and steps are unchanged; this split is below that level.
   Verdict: pass.
5. Checked the original node's new proof steps and dependency union against the Lean
   calls. Checked each new node's precise statement, complete proof steps, dependency
   union, source, fresh searches, creation record, blueprint lineage, inherited chapter
   and unit, module path, declaration name, and signature against its module. Removed
   stale inherited review metadata. Verdict: pass.

Second reading changed: moved the split lemmas into their own modules, supplied complete
sourced docstrings, corrected both new DAG statements and all proof records/searches,
pruned the obsolete direct import, and proved the final comparison-isomorphism clause
with Mathlib. Both substantial subproofs remain open.
