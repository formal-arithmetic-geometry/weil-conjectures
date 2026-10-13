## What changed

Repair of the landing-tool return: removed the duplicate private `tensor_cycles_lift`
from the main module. Added the proof-only import
`Sheaf.Algebra.Homology.TensorHomologyPairing`, and obtain the required cycle witness
from its public `HomologicalComplex.tensor_homology_pairing` theorem. Its internal
`tensor_cycles_lift` is private, so the public pairing is the available interface.
Updated the main node to include `lem-sc-tensor-homology-pairing` as a proof dependency.


Completed the earlier sandbox attempt in three modules:
- `Sheaf.Algebra.Homology.TensorHomologyMapBijective`: prove the original bijectivity statement
  unchanged, using a left inverse for injectivity and a spanning argument for surjectivity.
- `Sheaf.Algebra.Homology.TensorHomologyCoordinates`: construct and prove a linear coordinate map
  on total homology by extending the two homology quotients to full terms and descending through
  the total differential.
- `Sheaf.Algebra.Homology.TensorHomologyProductSpan`: prove product classes span total homology.
  Construct cycle-valued endomorphisms homotopic to identity, tensor their homotopies using
  Mathlib, and test the quotient by the product-class span on tensor generators.

The two helper modules are new, fully proved, and imported only for the main proof. The product
span proof imports the already proved `Sheaf.CategoryTheory.SplitCategoryNullHomotopy` as a
split-category tool. Its theorem is used after proving every vector space projective and
injective via semisimplicity. No existing public signature, visibility, or definition changes.
The main node's proof route and dependencies now name the two new nodes. The unit record
`sk-prop-av-cube` has no realized node at this level; its cube-theorem route is preserved.

All three modules compile cleanly with lcompile.py --all. The delivery dry run also compiles
with its axiom probes. New statements were checked against zero complexes, cycles with zero
class, negative indices, unbounded and infinite-dimensional terms, and characteristic two:
the coordinate construction kills all boundaries and the span proof uses degree-local splittings
and finite-support total colimits, with signs handled by Mathlib tensor homotopies.

## Proved and sorry left

Closed one original hole:
`HomologicalComplex.tensor_homology_map_bijective`
(node `lem-sc-tensor-homology-map-bijective`).

Also fully proved:
`HomologicalComplex.tensor_homology_coordinates`
(node `lem-sc-tensor-homology-coordinates`) and
`HomologicalComplex.tensor_homology_product_span`
(node `lem-sc-tensor-homology-product-span`). All remaining private helpers are proved:
`term_homology_projection` and `cycle_projector`. The duplicate private
`tensor_cycles_lift` was removed in this repair.

No sorry remains in any delivered module. No holes were added or split off. This is a proof,
not a decomposition into unfinished lower statements.

## No longer needed

The local duplicate `HomologicalComplex.tensor_cycles_lift` and its differential-formula
proof are no longer needed; the existing pairing supplies the witness. No module is pruned
by this repair, and no existing public interface is changed.


No original import, DAG node, or existing module is pruned: the original node had no proof
imports or proof dependencies. The new product-span module omits the unnecessary
`Mathlib.Algebra.DirectSum.Module` import from the earlier sandbox attempt; its statement needs
only the submodule span, and its proof uses categorical colimit extensionality.

No separately formalized differential-complement isomorphism or contracting-summand distribution
lemma is needed: the already proved split-category null-homotopy tool and Mathlib bifunctor
homotopies implement those steps. There were no existing named dependencies for these steps
in the original node to prune.

## Where the brief, the DAG or earlier work was wrong

The landing-tool return correctly identified a word-for-word duplicate of the private
cycle-lifting helper in `TensorHomologyPairing`. The earlier proof/review missed this
reuse opportunity. This repair removes the duplicate and uses the existing public theorem.
The previous second-reading section below describes the pre-repair version; a fresh
second reading must verify this repair.


The earlier attempt lacked DAG records and a report and its product-span module did not compile.
Repaired the identity-map simplification, evaluated tensor-map equation coercions, quotient-zero
lemma name and its explicit submodule argument, and added the needed quotient-definition import.
All repairs are confined to the sandbox delivery.

The original statement is sound and unchanged. Boundedness is unnecessary for the coordinate
construction and unused mathematically in the span argument; the original hA/hB binders stay.
The original DAG marked the long complement argument elementary without any proof dependencies;
its updated route records the proved helpers rather than hiding this work.

The literature source file is absent from this machine. Source context was read at the official
Stacks page https://stacks.math.columbia.edu/tag/0BED (equation the project server). The explicit linear
splitting expansion is the agent argument already recorded by the parent node; the new nodes
also mark proof_origin.by as agent. WANTED: local literature/stacks-project/varieties.tex,
varieties-lemma-kunneth / varieties-equation-kunneth-on-cech, for both new helper nodes.

Existing searches in searches.jsonl cover LeanFinder, Loogle, grep, and an unavailable LeanSearch
service. New LeanFinder search for total tensor homology spanning returned tensor infrastructure
and TensorProduct.exists_eq_tmul_of_forall, no matching theorem. Repository searches found no
existing coordinate or product-span declaration. New node search records preserve the queries
and returned names, including the service failure.

## New nodes

`lem-sc-tensor-homology-coordinates`: new module
`lean/Sheaf/Algebra/Homology/TensorHomologyCoordinates.lean`; a fully proved coordinate extraction
statement, strictly the left-inverse ingredient of the bijectivity argument.

`lem-sc-tensor-homology-product-span`: new module
`lean/Sheaf/Algebra/Homology/TensorHomologyProductSpan.lean`; a fully proved spanning statement,
strictly the surjectivity ingredient. Its only project proof dependency is the already proved
`lem-pc-split-category-null-homotopy`, used as a generic categorical tool.

No change record is needed: existing public interfaces are unchanged. No forced adaptations.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Read the repository and sandbox modules and their diff.
   The entire existing `tensor_homology_map_bijective` signature is byte-for-byte unchanged:
   the field, integer-indexed complexes, both lower-bound hypotheses, degree, linear map,
   representative compatibility for every summand and every matching cycle, and bijectivity
   conclusion all remain. Its docstring and public imports are unchanged. Only a proved private
   cycle-lifting helper, two private imports, and the proof replace the hole. No definitions or
   downstream modules are altered, so no change record is required.
2. **Proof and axioms: PASS.** Independently compiled all three modules in import order using
   `lcompile.py --all`; all compile cleanly. In scratch copies, `#print axioms` for all three
   public theorems and all three private helpers returned exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. Scanned all delivered Lean for sorry and forbidden
   declarations/attributes; none occur. The projection extensions and homology sections come
   from proved linear splitting/projectivity/injectivity, not unproved existence assertions.
3. **Helper statements: PASS.** No unfinished statements are split off. Coordinates supply
   only the left-inverse equation; product-span supplies only generation of the codomain, so
   neither merely renames bijectivity. Read their full proofs: boundary annihilation permits
   descending the coordinates, and a cycle-valued endomorphism homotopic to identity proves
   generation after quotienting by the product span. Zero complexes and zero cycle classes
   give zero maps/spans as required; integer neighbors and finite-support colimits cover
   negative degrees and unbounded/infinite-dimensional complexes; signs are handled by proved
   Mathlib tensor homotopies, including characteristic two. Independent LeanFinder query
   `cohomology tensor complexes over a field deformation retract onto cycles Kunneth` found
   representation-theoretic Tor comparisons, not these statements. Loogle query
   `HomologicalComplex.homologyMap, HomologicalComplex.mapBifunctorMap` returned no hits.
   Additional rg searches in Mathlib homology and repository Lean found no replacement;
   the repository's `tensor_kunneth` depends on this item and cannot be used as a shortcut.
4. **Route and pruning: PASS.** Traced the main proof through direct-sum/tensor extensionality
   to its left inverse and then span containment to surjectivity. The generic split-category
   null-homotopy theorem is already proved; its tensor homotopies implement the complement
   argument without introducing a new open dependency. The original proof_deps is empty,
   so `## No longer needed` correctly lists no old nodes to prune. Read
   `dag/units/sk-prop-av-cube.json`: its realized statement and step entries are empty;
   these algebraic helpers preserve the cube route. All new proof imports are private.
   Tested downgrading `ShortComplex.ModuleCat` to a private import: public signatures then
   fail to synthesize HasHomology/HasMapBifunctor instances. Restored the original import,
   which genuinely supplies statement-level instances, rather than treating it as proof-only.
5. **DAG agreement: PASS.** Compared the existing node with the repository: only proof,
   proof_deps, and proof_origin differ. The two new node Lean statements occur verbatim in
   their modules. Their source, parent/unit/chapter, searches, creation records, and Lean
   records are present. Proof-dependency unions are respectively coordinates plus span for
   the main node, empty for coordinates, and split-category null-homotopy for span; these
   match the actual proofs. No new node hides an open proof obligation.

Changes made by the second reader: corrected the coordinate node's proof_origin note, which
had unnecessarily referred to the split-category theorem used only in the span proof; added
this independent review and verification evidence. No final Lean proof or signature change
was necessary. Removed all temporary axiom-probe copies before delivery.

## Second reading by B4

1. **Interface: PASS.** Compared the delivered main module with the repository using
   `diff -u`. Its original declaration signature and docstring are byte-for-byte unchanged;
   the only edits are three plain proof imports and the proof replacing `sorry`.
   The helper modules are new. No existing definition, visibility, target statement, or
   downstream module changes, and no change record is required.
2. **Proof: PASS.** Independently compiled all three modules in import order with
   `lcompile.py --all`. Read every proof, including the private projection and cycle-projector
   helpers. Scratch-copy `#print axioms` checks for all three public theorems and both private
   helpers show only `propext`, `Classical.choice`, and `Quot.sound`. Scanning the delivered
   Lean files found no sorry or forbidden declaration/attribute. All splitting choices use
   proved linear-algebra or categorical results; no data comes from an unproved existence
   theorem. In the repaired main proof, the pairing's witness is used only locally in a
   proposition proof, and its cycle inclusion equation is exactly the premise of `hf` and `hr`.
3. **New statements: PASS.** There are no unfinished statements split off. Coordinates
   provide the left-inverse ingredient; product-span provides the generation ingredient.
   Neither restates bijectivity. Checked zero terms and complexes, boundaries with zero
   class, negative degrees, infinite-dimensional terms and characteristic two against the
   constructions. Coordinate extensions kill boundaries; tensor homotopies handle the signs;
   colimit extensionality handles finite-support sums without dimension or boundedness
   assumptions. Independent LeanFinder query `Kunneth cohomology tensor total complex split
   vector spaces cycle projection` returned group-(co)homology comparisons, not a replacement.
   Loogle query `HomologicalComplex.mapBifunctorMap, HomologicalComplex.homologyMap` returned
   no hits. Additional repository and Mathlib homology searches found the existing pairing
   and tensor homotopy tools already used, but no coordinate or spanning theorem to reuse.
   `tensor_kunneth` calls this item and cannot supply a shortcut.
4. **Route and pruning: PASS.** Read the main proof from its left-inverse equation down to
   the span/range argument, then read both ingredients and the existing proved split-category
   null-homotopy tool. The duplicate cycle-lifting proof is absent; the existing public pairing
   supplies the witness. All three new main imports are proof-only. The helper proof imports
   provide linear splittings, quotient-zero reasoning and tensor homotopies. The original
   main node has empty `proof_deps`, so there are no old dependencies missing from
   `## No longer needed`. The unit `sk-prop-av-cube` has empty realized statement and step
   lists at this level; its route is preserved. No existing module is pruned.
5. **DAG: PASS.** Compared the existing node with the repository: only `proof`,
   `proof_deps`, and `proof_origin` differ. The updated main proof-dependency union is
   coordinates, product-span and pairing, agreeing with the repaired Lean proof. The new
   coordinate node has no project proof dependencies; the span node uses the split-category
   null-homotopy node. Both new nodes have verbatim Lean statements, complete proof steps,
   sources, search records, creation metadata, blueprint ancestry and chapter/unit records.

Changes made by this second reader: added this fresh review of the repaired delivery and its
independent compilation, search and axiom-check evidence. No Lean or node repair was needed.
Removed temporary axiom-probe copies before the final dry run and delivery.
