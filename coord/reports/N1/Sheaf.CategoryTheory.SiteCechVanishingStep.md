## What changed

Filled `CategoryTheory.Sheaf.siteCech_vanishing_dimension_shift` in
`Sheaf.CategoryTheory.SiteCechVanishingStep`, without changing its signature or docstring.
The proof follows Stacks 03F9 (`lemma-cech-vanish-collection`, read in the local Stacks
source copy), using the two existing site Čech lemmas and Mathlib's Ext and complex
homology exact sequences. All added imports are proof-only.

The proof first obtains surjectivity of sections from the existing 03F8 lemma. Its
quantification over all product choices is met by the proved `comparison_exists`
natural isomorphism of Čech complexes and transportation of degree-one homology.
It then inducts uniformly over all Čech-acyclic sheaves, constructing the injective
embedding and its actual cokernel. In degree one the free representable/sheafification
adjunction identifies morphisms with sections; lifting a quotient section makes its
Ext boundary zero. In higher degrees sectionwise short exactness is proved explicitly
on every intersection and then on products. The homology long exact sequence proves
the cokernel Čech-acyclic, and Ext exactness completes dimension shifting.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
The node is below the unit's realized statements and steps; those remain in use upstream.
The empty covering-index case is included by the componentwise product arguments.
The induction quantifies over the cokernel sheaf, rather than incorrectly using
vanishing of the preceding degree of the original sheaf.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.Sheaf.siteCech_vanishing_dimension_shift`
(node `lem-weil-pbc-site-cech-vanishing-dimension-shift`).
There are no sorries left in the delivered module and no holes added or split off.

The proof still depends on the existing named holes
`CategoryTheory.surjective_sections_of_site_cech_h1_vanishing`
(node `lem-weil-pbc-site-ses-cech-h1-surjective`) and
`CategoryTheory.site_injective_cech_acyclic`
(node `lem-weil-pbc-site-injective-cech-acyclic`). These are the next needed items,
not newly introduced assumptions or proofs of them in this delivery.
The dry run checks the declaration's axioms with the project probe.

## No longer needed

Removed the circular planned proof edge to
`lem-weil-pbc-site-cech-vanishing-criterion` /
`Sheaf.CategoryTheory.SiteCechVanishingCriterion`: this criterion already imports
`SiteCechVanishingStep`, so it cannot prove the step. The criterion itself remains
needed upstream; no claim that its module is globally unreachable is made.

No original imports were removed: both public imports are needed by the statement.
Temporary direct proof imports `Mathlib.CategoryTheory.Whiskering` and
`Mathlib.Algebra.Homology.ShortComplex.Ab` were removed by the first worker.
The second reading additionally removed redundant direct proof imports
`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`,
`Mathlib.CategoryTheory.Adjunction.Whiskering`, and
`Mathlib.Algebra.Homology.HomologySequence`, after a clean compile with all three
removed together. Their APIs remain available through the retained imports;
these are redundant import removals, not globally pruned modules.

The finite-cover source-library module
`WeilConjectures.CategoryTheory.Sites.CechCriterion` is not imported: its criterion
requires finite cofinal covers, a terminal object, and finite products in every slice.
The present proof requires none of these additional assumptions.
No generic right-derived delta-functor or full right-derived long-exact-sequence module
is imported: the definition of H' as Ext allows Mathlib's proved Ext exactness directly.
These modules may remain needed by other items; this is pruning of this proof route.

## Where the brief, the DAG or earlier work was wrong

The original node pointed its proof back to the enclosing vanishing criterion, creating
a circular plan. Replaced that edge with its actual injective embedding, section
surjectivity, Čech acyclicity, and homology dependencies.

The source-library finite-cover criterion does not fit the present general-site
hypotheses. Merely applying it would add assumptions not present in this item.

`site_injective_cech_acyclic` is marked STATEMENT-DISPUTED in its existing module
because of independent universes. This delivery uses only the matched-universe
specialization: site objects, morphisms, covering indices and coefficient groups
all have universe u. Thus the reported small-coefficient/large-site counterexample
does not apply to this use. Its unrelated degree-zero conclusion is not used.
The dependency's eventual universe repair must retain this valid specialization.

Searches used LeanFinder for general Čech vanishing, Loogle for
`Ext.covariant_sequence_exact₁`, the launcher's grep search, and local rg across
both library roots. The exact-sequence, injective, adjunction, and homology APIs
were then read from the pinned Mathlib sources. Import-direction checks permit
both new Sheaf proof imports. Single-file compilation is clean.


## Second reading by N1

1. PASS: compared the delivered module with the repository using diff. The only
   changes are the proof body and proof-only imports. The theorem signature,
   universes, hypotheses, conclusion, docstring, and both public imports are
   byte-for-byte unchanged. There are no definitions or other delivered modules,
   and no statement change needs a change record.
2. PASS: compiled the module locally without errors or warnings. An explicit
   `#print axioms CategoryTheory.Sheaf.siteCech_vanishing_dimension_shift` in a
   scratch copy reports exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`, the latter from the two existing named dependency holes listed
   above. No sorry or forbidden declaration form is present in the delivery.
   The injective embedding is Mathlib's proved enough-injectives construction;
   its cokernel is the actual categorical cokernel. No arbitrary data are
   obtained from an unproved existence theorem.
3. PASS: no statements or holes were split off, and no nodes were added. Checked
   the existing dependencies at the used universes. The injective acyclicity
   dependency's disputed independent-universe version is used only with all
   site, index, and coefficient universes matched. Degree zero is not used.
   Checked the empty-cover product case, the degree-one boundary argument,
   and the successor step: induction is uniform in the sheaf, so it applies
   to the cokernel rather than assuming the desired vanishing for it.
4. PASS after import pruning: independent searches by LeanFinder, Loogle for
   `CategoryTheory.Sheaf.H'`, launcher grep for Ext exactness and vanishing,
   and rg across both source roots found no shorter applicable theorem. Read
   the upstream finite-cover criterion: its terminal object and finite cofinal
   families are additional assumptions unavailable here. The enclosing general
   criterion imports this item, so using it would be circular. The report names
   the sole old proof dependency removed. Read `dag/units/sk-thm-p1.json`:
   this helper is not a realized unit statement or step, and none of the unit's
   realized nodes or routes changes. Tested every added proof import separately;
   three were redundant, and removing all three together still compiles cleanly.
5. PASS: compared the old and new node records. Only `proof`, `proof_deps`, and
   `proof_origin` change; the steps describe the actual Lean proof. The dependency
   set is exactly the union of the steps' uses. The enough-injectives,
   degreewise-short-exact, and homology-sequence nodes are Mathlib leaves whose
   recorded declarations agree with the APIs used here. Both remaining Sheaf
   theorem dependencies are called explicitly.

Second-reading changes: removed the three redundant direct proof imports named
above and corrected the pruning report to distinguish direct import removal from
global module pruning. Kept the proof and node route unchanged: no mathematical
repair or additional split was needed. The delivery closes one existing hole,
adds zero holes, and leaves the existing dependency holes open.
