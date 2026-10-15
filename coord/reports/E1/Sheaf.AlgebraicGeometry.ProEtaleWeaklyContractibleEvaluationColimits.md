## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.affine_weaklyContractible_evaluation_colimits`
in `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`, with its
signature unchanged. Second reading removed seven redundant direct imports while
preserving the transitive public import closure. Added five proved private helpers for finite
covering refinement, local surjectivity of the presheaf/sheaf colimit comparison,
finite support of coproduct sections, invertibility of the coproduct comparison, and
preservation of coproducts.

Exactness reuses the proved theorem
`weaklyContractible_evaluation_preservesHomology`. The new coproduct argument adapts the
proved private sheafification-comparison and finite-support arguments in
`Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover`; those helpers are private and its
public theorems concern module sheaves on the Zariski site, so that module cannot directly
supply this pro-etale result. Affine fpqc refinement comes from
`QuasiCompactCover.exists_hom`. A projection onto the finite union of supports replaces
coordinate gluing. Mathlib constructs all colimits from coproducts and coequalizers;
`colimit.map_post` supplies naturality.

Added proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`
- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`

Updated only `proof`, `proof_deps`, and `proof_origin` of the existing DAG node
`lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits` to record this route.
No statements, definitions, other modules, or unit-level steps changed.
The public-import cleanup is declared in
`coord/changes/ProEtaleWeaklyContractibleEvaluationColimits-imports.md`, including all
20 downstream users. Their exported declarations and instances remain available.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.ProEt.affine_weaklyContractible_evaluation_colimits`
(node `lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`).

The five proved private helpers are `finite_cover_refinement`,
`colimit_comparison_locally_surjective`, `affine_coproduct_section_finite_support`,
`affine_evaluation_coproduct_isIso`, and `affine_evaluation_preserves_coproducts`.
No `sorry` remains in the delivered module and
none is added elsewhere: one hole closed, zero added, no decomposition or split-off.
`#print axioms` for the completed theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; in particular the reused exactness theorem introduces no unproved axiom.
Local single-file compilation passed without warnings in under ten seconds.
Second reading independently compiled the cleaned file in a scratch copy with
`#print axioms` for all six theorems: each uses exactly the same three standard axioms
and no `sorryAx` (6.8 seconds).

The proof treats arbitrary index types of the stated universe. The empty family,
empty support, zero sections, and empty affine scheme are included by the same finite
refinement, separatedness, and split-projection arguments. No nonemptiness assumption
was introduced.

## No longer needed

Removed the original proof imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`

Second reading also removed redundant direct public imports (each remains publicly
available transitively through the retained imports):

- `Mathlib.CategoryTheory.Limits.Preserves.Limits`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Sites.LocallyBijective`
- `Mathlib.CategoryTheory.Sites.LeftExact`

It removed redundant proof imports from the first worker's version:

- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`
- `Mathlib.CategoryTheory.Limits.Constructions.Filtered`
- `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`

These seven removals remove duplicate direct edges; they do not withdraw their modules
from the transitive import closure.

Removed these direct proof dependencies from this node:

- `lem-weil-pbc-module-sheaves-colimits-forgetful`
  (`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`).
- `lem-pc-sites-sheafification-underlying-sets`
  (Mathlib match in `Mathlib.CategoryTheory.Sites.PreservesSheafification`).
- `lem-weil-pbc-site-sheafification-sections-local`
  (`Sheaf.Paper.SiteSheafificationSectionsLocal`).
- `lem-weil-pbc-module-sheaves-limits-sectionwise`
  (Mathlib match in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`).

Their roles are covered by the existing exact-evaluation theorem and the proved private
adjunction argument. These are dependencies pruned from this item's route; other target
routes may still need them. No module is withdrawn. Exploratory helper modules are not
part of this delivery, and no additional proof-dependency imports remain unused.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's mathematical argument is
valid, but exactness was already proved in another module. Coordinate-by-coordinate
gluing and local-equality arguments can be replaced with the finite-support projection
and its splitting. Mathlib already supplies the arbitrary-colimit construction and the
comparison's naturality, so these steps need no new statements or nodes.

## Second reading by E1

1. **Existing interface: PASS.** Compared the sole delivered module with the repository
   using `diff`, and extracted the entire existing theorem signature through its final
   comparison equality: byte-for-byte identical. The hypotheses still allow every scheme
   X, every commutative ring sheaf R in the section universe, and every affine W with the
   stated surjectivity property for all set-sheaf epimorphisms. Both exactness clauses,
   all small colimits, the filtered comparison, and its naturality are unchanged. Only
   private proved helpers were added; no existing definitions or attributes changed.
   The import cleanup is declared in the change record, with the public transitive
   import chains and the complete downstream-user table. No downstream edit is needed.

2. **Proof and axioms: PASS.** Independently compiled the delivered proof, then its
   cleaned scratch copy with six `#print axioms` commands, through `lcompile.py` only.
   Both runs were clean; each theorem depends solely on `propext`, `Classical.choice`,
   and `Quot.sound`. No `sorry`, forbidden declaration, hollow definition, or data chosen
   from an unproved existence theorem occurs. In particular the finite refinement comes
   from Mathlib's proved `QuasiCompactCover.exists_hom`, and the reused exactness theorem
   introduces no `sorryAx`. The sheafification comparison is identified on every colimit
   inclusion using the adjunction triangle identity, so local surjectivity applies to
   the actual canonical comparison. The finite-support projection fixes the section on
   a covering family; separatedness gives the asserted global equality. The kernel
   argument uses a genuine split inclusion, not sectionwise exactness assumed in advance.

3. **Split statements: PASS, none.** The sole original hole is closed and no holes are
   added. All five helper statements are proved, private, and used. Checked the empty
   index family, empty finite support and empty affine scheme: the zero projection and
   separatedness arguments still apply; neither `Nonempty` nor a nonzero-ring assumption
   is introduced. The finite comparison is available by additivity alone, and filtered
   colimits of modules supply each element used in the injectivity argument. No new
   public statement or DAG node needs delivery.

4. **Route and pruning: PASS after import cleanup.** Read the reused exact-evaluation
   proof, the private comparison in `CompactFlatGeneratorCover`, and Mathlib's finite
   affine refinement and sheaf-colimit implementations. Searched LeanFinder afresh for
   quasi-compact global sections preserving direct sums, and searched both library roots
   and Mathlib for evaluation, finite covering and coproduct results. The hits concern
   free sheaves, scheme-module colimit existence, or specialized condensed sites; they
   do not replace this argument. Read Stacks Tags [0946](https://stacks.math.columbia.edu/tag/0946),
   [0935](https://stacks.math.columbia.edu/tag/0935), and
   [03DB](https://stacks.math.columbia.edu/tag/03DB): exact evaluation, finite-subsum
   reduction over a quasi-compact object, and sheafification of module colimits agree
   with this proof. Mathlib already supplies the coproduct/coequalizer construction and
   `colimit.map_post`, both used directly. All four old proof dependencies omitted from
   the new proof are listed under No longer needed. Read
   `dag/units/sk-thm-properbasechange.json`: this node and its removed dependencies are
   below the nodes realizing the unit's statement and three steps. The P1, reduction,
   and torsion-assembly route is untouched; no unit realization is bypassed.

5. **DAG agreement: PASS.** Diffed the node: only `proof`, `proof_deps` and `proof_origin`
   change. Its six steps follow exactness, finite refinement, the adjunction comparison,
   finite-support descent, bijectivity, and the general colimit/naturality argument.
   `proof_deps` is exactly the union of their `uses`: exact evaluation, the pro-etale
   site, and colimits. No new node, statement change, or unit edit occurs. Corrected the
   source document of Tag 00WK from the modules/cohomology files to `sites.tex`, and
   included that file in `proof_origin`.

Changes made by second reading: removed seven redundant import lines, added the explicit
public-import change record, corrected the node's Tag 00WK source document, and updated
this report. The proof terms and all theorem signatures were retained.
