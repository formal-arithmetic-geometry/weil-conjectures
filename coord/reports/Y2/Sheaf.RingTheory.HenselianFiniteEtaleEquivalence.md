## What changed

Replaced the sole sorry in `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence` with a
complete Lean assembly of Stacks Tag 04GK. The signature and existing docstring stay
unchanged. The proof decomposes an arbitrary finite étale residue algebra using
`Algebra.Etale.iff_exists_algEquiv_prod`, lifts its finite separable field factors,
constructs their finite product, and composes `Algebra.TensorProduct.piRight`,
`AlgEquiv.piCongrRight`, and the inverse decomposition isomorphism. It installs Full,
Faithful, and EssSurj and constructs IsEquivalence from them. No algebra definition
chooses an arbitrary witness from an unproved existence theorem: all choices occur
inside this proposition's proof.

Added two independently provable intermediate modules, each with one public theorem,
a complete source-based proof in its docstring, and a new DAG node. They isolate
original steps 1–7 (morphisms) and step 8 (one field extension); original step 9 is now
proved in Lean. Neither intermediate asserts the equivalence or essential surjectivity
for an arbitrary residue algebra. Updated the original node's proof and dependencies.
The new modules retain the original plan's non-Mathlib dependency imports required
for their future proofs.

All three modules compile in dependency order, without warnings. The empty product is
covered by the same proof: Mathlib's finite-product instances and tensor product
isomorphism allow an empty index type. The field-lifting lemma includes degree one
and excludes the zero ring by its Field hypothesis. The morphism statement includes
zero source and target algebras, as explained in its proof docstring.

## Proved and sorry left

Closed:
`CommAlgCat.FiniteEtale.isEquivalence_baseChange_residueField_of_henselianLocalRing`
(node `lem-weil-pbc-henselian-finite-etale-equivalence`). No sorry remains in the item.

Added and left:
- `CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`
  (`lem-weil-pbc-henselian-finite-etale-map-bijective`, module
  `Sheaf.RingTheory.HenselianFiniteEtaleMapBijective`).
- `CommAlgCat.FiniteEtale.exists_finiteEtale_residueField_equiv_of_finite_separable`
  (`lem-weil-pbc-henselian-finite-etale-field-lift`, module
  `Sheaf.RingTheory.HenselianFiniteEtaleFieldLift`).

This is a decomposition: one upper hole closed, two strictly smaller holes added.
It is not an axiom-free proof of the equivalence and claims no positive net hole count.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`
- `Sheaf.RingTheory.HenselianEtaleRetraction`
- `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`

These imports moved to the appropriate intermediate modules: none is asserted to be
unneeded by the overall argument or prunable from the targets' closure. The original node's former direct proof dependencies remain available transitively
in the two new nodes, or are used directly in the product assembly. No mathematical node or module
is globally pruned. The final step needs no new product-lifting or categorical
assembly sorry; Mathlib supplies those constructions.

For completeness, the old direct `proof_deps` removed from the equivalence node are:
- `lem-weil-pbc-etale-quotient-base-change`
- `lem-weil-pbc-henselian-etale-retraction`
- `lem-weil-pbc-etale-retraction-finite-product-local`
- `lem-weil-pbc-etale-algebra-finite-presentation-localization`
- `lem-weil-pbc-finite-algebra-local-radical`
- `lem-weil-pbc-etale-prime-generates-maximal`
- `lem-weil-pbc-etale-algebra-residue-field-separable`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-nakayama-jacobson`
- `lem-weil-pbc-etale-algebra-flat`
- `lem-weil-pbc-finite-flat-local-free`
- `lem-weil-pbc-etale-ring-map-prescribed-residue-field`
- `lem-weil-pbc-henselian-finite-type-product-decomposition`
- `lem-weil-pbc-etale-ring-map-quasi-finite`

The first twelve remain in the morphism node's proof plan. The last three remain in
its field-lifting counterpart. The second reading removed an unnecessary preliminary
decomposition from the field node; its direct dependencies on henselian retraction,
finite-product-local decomposition, and residue separability are unnecessary there.
Those nodes remain needed by the morphism argument, so this prunes no global module.


## Where the brief, the DAG or earlier work was wrong

No false Lean statement was found. The second reading qualified the new morphism node's
factor-uniqueness assertion: uniqueness is relative to the projections, since abstract
field factors can have automorphisms. The source has the known typo saying the factors
are étale over S rather than R, already corrected in the original DAG. The original
plan's declarations do not directly state the aggregate morphism-bijection argument
or the finite field-lifting conclusion, so those portions are isolated rather than
asserted to follow by a single application of an existing dependency.

LeanSearch returned Internal Server Error for both new statement queries; these
searches are recorded as unavailable, with no mathematical no-match verdict.
LeanFinder, Loogle, and local source searches were available. Mathlib's field
classification and tensor/product results were checked by their types and successfully
used. The local Stacks TeX file is absent on this machine; the source proof was read
at https://stacks.math.columbia.edu/tag/04GK and agrees with the nine-step DAG proof.
No unit statement or unit proof step is bypassed: this lemma is below the realized
statement and steps of `sk-thm-p1`, whose records are unchanged.

## New nodes

`lem-weil-pbc-henselian-finite-etale-map-bijective` records the full-faithfulness part
of Tag 04GK, through the matching tensor-factor indices. Its module is
`lean/Sheaf/RingTheory/HenselianFiniteEtaleMapBijective.lean`.

`lem-weil-pbc-henselian-finite-etale-field-lift` records the lift of one finite
separable residue extension, through the prescribed-residue theorem and henselian
finite-type decomposition. Its module is
`lean/Sheaf/RingTheory/HenselianFiniteEtaleFieldLift.lean`.

No existing statement, definition, visibility, or public import changed. No change
record or forced adaptation is required.


## Second reading by Y2

1. **Unchanged interface — pass.** Diffed the delivered equivalence module against
   the repository version. The existing theorem signature is byte for byte unchanged;
   the docstring, visibility, universes, and both public imports are unchanged.
   Only its proof and private proof imports changed. The other two modules are new.
   No definitions or statements were adapted, and no change record is required.
2. **Proof and axioms — pass as a decomposition.** Compiled all three modules locally
   in dependency order, without errors or warnings. Separate scratch copies with
   `#print axioms` for each of the three declarations show precisely `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. There is no sorry in the item;
   exactly the two named, documented helper theorems retain sorry. There are no data
   definitions or forbidden declarations. Witness choice stays inside a proposition's
   proof and creates no public algebra chosen from an unproved existence theorem.
3. **New statements — pass.** Read both statements, their docstrings, and their nodes
   against [Stacks Tag 04GK](https://stacks.math.columbia.edu/tag/04GK). Morphism
   bijectivity isolates full faithfulness; lifting one finite separable field isolates
   the source's single-field construction. Neither restates the whole equivalence.
   Checked the zero source/target algebras, the empty product, a one-factor product,
   and the degree-one field extension. HenselianLocalRing excludes a zero base ring;
   Field excludes a zero extension. New LeanFinder searches used morphism lifting and
   closed-fibre wording, with Loogle and local searches of both library roots and
   Mathlib. No exact replacement exists: formal-unramified lifting results require
   nilpotence, and the existing prescribed-residue theorem does not give finiteness.
   Closing either helper requires substantial local-factor and residue-field transport,
   so neither can be closed by a short existing-lemma application.
4. **Shortest route and unit — pass.** Checked the field classification and finite
   product/tensor-product assembly. The item uses Mathlib directly for those steps;
   each imported helper is used, and all extra imports are private proof imports.
   The helper dependency imports preserve the unfinished source argument. Read
   `dag/units/sk-thm-p1.json`: this lemma is below the realized statement and steps;
   no unit step is bypassed. The No longer needed section now explicitly enumerates
   every removed old direct dependency and distinguishes it from global pruning.
5. **DAG agreement — pass after repair.** The original node changes only `proof`,
   `proof_deps`, and `proof_origin`, matching the compiled assembly. Both new nodes
   have complete source, search, provenance, chapter/unit, and verbatim Lean statement
   records. Their dependency lists equal the unions of their steps' uses. Removed
   the field node's unrelated preliminary decomposition and qualified factor
   uniqueness in the morphism node to require compatibility with the projections.

Second-reading changes: repaired those two new DAG proof plans, completed the pruning
inventory, and added this review. No Lean proof or signature required repair. The
outcome remains one original hole closed and two smaller holes added (net -1), with
no global modules pruned; it is a decomposition, not a completed axiom-free result.
