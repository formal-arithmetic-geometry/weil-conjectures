## What changed

Proved `AlgebraicGeometry.Scheme.AffineProEt.affine_closed_inverseImage_evaluation`
in `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`, retaining
its exact statement, universes, visibility and three public imports.

The first clause constructs the presheaf-precomposition/sheafification adjunction,
then uses `CategoryTheory.isIso_inverseMate_of_equivalences` and the commuting
direct-image square to identify it with the ordinary inverse image restricted
to the affine basis. The restriction equivalences already exist in the source
library.

The second clause is a complete finite-cover argument. Local injectivity of the
sheafification unit and preservation of covers prove injectivity. The proved
`SigmaCover` API gives finite disjoint unions and arbitrary-family gluing;
representable sheaves prove their coproduct universal property. Preservation
by the left adjoint gives gluing after the lift. Subcanonical Yoneda and
separatedness show that a singleton cover induces an epimorphism of representable
sheaves. The hypothesis on evaluation at V then splits the cover. Local lifts
of a sheafified section glue on the finite disjoint union and pull back along
this section, proving surjectivity.

All seven private helpers are proved here, including the `IsColimit` construction;
none introduces an unproved intermediate statement. Empty indexing families and
the empty object need no separate nonemptiness hypothesis. There are no changes
to definitions or other modules and no forced adaptations.

Added private proof imports:
- `Sheaf.CategoryTheory.InverseMateEquivalence`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products`

Updated only `proof`, `proof_deps` and `proof_origin` in
`lem-weil-pbc-affine-closed-inverse-image-evaluation`, to record the actual proof.
The theorem docstring now describes that route. The unit statement and its proof
steps remain intact.

Validation: the final module compiles without warnings through `lcompile.py`.
All three added imports pass `tools/import_direction.py may`. The delivery dry
run supplies the signature, axiom, import, and preflight checks.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.AffineProEt.affine_closed_inverseImage_evaluation`
(node `lem-weil-pbc-affine-closed-inverse-image-evaluation`). Both clauses are proved.

Added 0 holes, split off 0 statements. No `sorry` remains in the delivered module.
This is a proof from existing dependencies, including the still-unproved
`AlgebraicGeometry.Scheme.AffineProEt.affine_closed_site_functor_properties`;
it does not claim that the entire transitive proof closure is free of `sorryAx`.
The new private helper proofs use the established source-library and Mathlib APIs.

## No longer needed

Removed private imports (none of the public imports changed):
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`
- `Mathlib.CategoryTheory.Sites.Pullback`
- `Mathlib.CategoryTheory.Yoneda`
- `Mathlib.RingTheory.Etale.Pi`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`

Removed direct proof dependencies from this node:
- `def-weil-pbc-ind-etale-algebra`
- `def-weil-pbc-proetale-site`
- `lem-pc-fppf-dense-sheaf-equivalence`
- `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`
- `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection`
- `lem-weil-pbc-etale-algebra-finite-product`
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-proetale-qcqs-finite-family-geometry`
- `lem-weil-pbc-site-sheafification-sections-local`

The source library's proved `SigmaCover` construction, gluing/extensionality,
and surjective projection lemmas replace the planned filtered-colimit/product,
ind-etale stability and finite-family-geometry work. Mathlib's
`Presheaf.equalizerSieve_mem` and `Presheaf.imageSieve_mem`, applied to the
sheafification unit, replace `SiteSheafificationSectionsLocal`. Existing affine
restriction equivalence instances replace a separate dense-subsite equivalence
argument. The inverse-mate theorem replaces an explicit left Kan extension
calculation and a separate coyoneda comparison.

These modules/nodes are unnecessary for this item's proof; no claim is made that
other targets no longer use them. Statement dependencies are unchanged, even
where an obsolete proof dependency has been removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's route was longer
than needed: it reproposed finite disjoint-union and affine comparison facts
already proved in the source library. Its planned local sheafification statement
also has the exact covering-sieve API needed here in Mathlib. These are route
simplifications, not changes to the mathematical statement.

Source checked: Stacks Project [Tag 09BL](https://stacks.math.columbia.edu/tag/09BL),
clauses (1) and (2). The proof follows its preservation of sums, separatedness,
splitting of a finite singleton refinement, and final local-lift argument.

## Second reading by D4

1. **Interfaces — PASS.** Compared the sole delivered Lean module with the
   repository version using `diff`. The existing theorem's complete signature is
   byte-for-byte identical, including universes, hypotheses and conclusion. All
   three public imports and the exposed public section are unchanged. The seven
   added helpers are private. No definition used by a target was changed; no
   change record or forced adaptation is needed.
2. **Proof and trust — PASS.** Read the complete proof and its upstream APIs.
   `lcompile.py` compiled the delivered module without errors or warnings (4.8 s).
   A scratch copy with `#print axioms` for all seven helpers and the main theorem
   also compiled (3.7 s). Every helper uses only `propext`, `Classical.choice` and
   `Quot.sound`; the main theorem additionally uses `sorryAx`, through existing
   open dependencies, including `affine_closed_site_functor_properties`. No
   forbidden declaration, hidden hole or hollow definition occurs here.
   `sigmaCover_colimit` constructs the universal-property witness from proved
   bijectivity; its descent maps are uniquely determined. The adjunction witness
   from the open site-properties theorem is eliminated inside a proof of a
   proposition about the already constructed fixed functors. No definition or
   geometric object chooses arbitrary data from an unproved existence theorem.
3. **Split statements and edge cases — PASS.** No new statements with `sorry`,
   no new public declarations and no new nodes were added. Checked that finite
   families may be empty: the established SigmaCover gluing and extensionality
   lemmas include empty families, the coproduct construction uses no inhabited
   assumption, and the singleton-cover argument applies to empty objects. The
   identity immersion and empty closed subscheme require no extra hypotheses.
4. **Route, searches and pruning — PASS.** Checked the argument against
   [Stacks Tag 09BL](https://stacks.math.columbia.edu/tag/09BL), clauses (1),(2).
   The direct-image square and inverse mate give the required orientation of the
   natural isomorphism. Cover preservation proves unit injectivity; preservation
   of the finite coproduct, Yoneda cover splitting and local lifts prove
   surjectivity. Read SigmaCover and Replete; their existing results are reused.
   Independent `rg` searches for coproducts, singleton epimorphisms and unit
   injectivity, and a Loogle search for injective `toSheafify`, found no shorter
   exact theorem to substitute. Each new private import supplies an API used by
   the proof. Compared old and new `proof_deps`: all ten removed dependencies
   and all twelve removed private imports are listed under `No longer needed`.
   The unit record `sk-thm-properbasechange` retains all of its realized statement
   and step nodes; this item simplifies only auxiliary work below that route.
5. **DAG correspondence — PASS.** The sole node changes exactly `proof`,
   `proof_deps` and `proof_origin`. Its five proof steps follow the Lean argument,
   and `proof_deps` is exactly the union of their `uses`. Checked the dependency
   records, including the Mathlib Yoneda match and the proved inverse-mate node.
   The node's statement, statement dependencies, Lean record and unit are
   unchanged. No new-node fields or change records are required.

Second-reading changes: appended this independent review and its verification
results. No fault requiring a Lean or DAG repair was found, so their correct
proofs and records were retained. The delivery closes the one original named
hole and adds zero holes; it does not close the remaining upstream holes.
