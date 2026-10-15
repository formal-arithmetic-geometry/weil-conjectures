## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_cover` with its
signature unchanged. The proof follows Stacks Tag 0F4P, using the existing affine weakly
contractible covering-family theorem and the direct finite-coproduct-evaluation theorem.
The latter replaces the larger qcqs finite-family geometry bundle.

Added a fully proved private helper `exists_finite_refinement`. It pulls the cover back to
finitely many affine charts, applies Mathlib `QuasiCompactCover.exists_hom` on each,
and composes the resulting finite affine refinements. This handles quasi-compact bases
without assuming quasi-separatedness. The retained original objects remain weakly
contractible; the affine refinement objects are only witnesses that the resulting
singleton is a covering.

The map from the coproduct is the preimage under lifted Yoneda of the uniquely determined
colimit descent map. The proof verifies its composites with all coprojections, transfers
the quasi-compact covering condition along the refinement, and proves weak contractibility
by the natural section-product bijection. No data definition or public interface changed.

Updated the existing DAG node's proof, proof dependencies, and proof origin to match.
Compiled the module locally without errors or warnings (about 2.3 seconds).
Read Stacks Tags [0F4P](https://stacks.math.columbia.edu/tag/0F4P) and
[0990](https://stacks.math.columbia.edu/tag/0990); the empty index type is covered by the
same dependent-product argument. All imports are proof-only except the original public
statement import.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_cover`
(node `lem-weil-pbc-proetale-qc-affine-contractible-cover`). The private helper
`exists_finite_refinement` is also fully proved. No holes remain in the delivered module;
no new holes or split-off declarations were added.

The proof uses the already stated theorems
`AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_covering_family`
(node `lem-weil-pbc-proetale-affine-wcontractible-covering-family`) and
`AlgebraicGeometry.Scheme.ProEt.finite_coproduct_evaluation`
(node `lem-weil-pbc-proetale-finite-coproduct-evaluation`), whose existing proofs still
contain `sorry`. This delivery closes the upper hole from those existing dependencies.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`
and bypassed node `lem-weil-pbc-proetale-qcqs-finite-family-geometry` by directly using
`Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`.
The bundled theorem's qcqs site-limits branch
(`lem-weil-pbc-proetale-qcqs-site-limits`, module
`Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`) and its qcqs-subsite interface
(`Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite`) are unnecessary for this proof.
The subcanonical instance comes from Mathlib; the subcanonical node remains among the
finite-coproduct theorem's own planned dependencies and is not claimed pruned globally.

A trial explicit import of `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` was
removed after checking the two proof imports already provide the required instances.
All remaining proof imports are used. No unit-level statement or realized proof step is
bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable signature was found. The large qcqs finite-family geometry
bundle contains more than this argument needs; its finite-coproduct constituent suffices.
The finite-subfamily step needs care for non-quasi-separated bases: affine sources alone
do not justify assuming every morphism to T quasi-compact. The compiled chartwise
refinement argument supplies the required covering witnesses explicitly.

Searches run through the required wrapper: Lean Finder on a singleton affine weakly
contractible cover, Loogle on `IsCompactOpenCovered`, and grep on weak contractibility.
No existing direct proof was found. Mathlib's covering and quasi-compact refinement APIs
supply the geometric glue.


## Second reading by C4

1. **Interfaces: pass.** Read the complete repository and delivered modules and their
   diff. The signature of `exists_affine_weaklyContractible_cover` is byte-for-byte
   identical, including the sole compactness assumption on `T.left`, full-site sheaves
   in `Type (u + 1)`, singleton precoverage membership, affineness, and surjectivity for
   every sheaf epimorphism. The only added declaration is the private, proved refinement
   helper. There are no definition changes, public helpers, adapted modules, or change
   records. No open change record names this module or the declarations used here.
2. **Proof and axioms: pass.** Independently compiled the delivered module with
   `lcompile.py`: exit 0, no warnings, about 2.2 seconds. A scratch copy with
   `#print axioms` for both declarations also compiled. The private
   `exists_finite_refinement` uses only `propext`, `Classical.choice`, and `Quot.sound`.
   The public theorem additionally uses `sorryAx`, consistently with the existing
   covering-family and finite-coproduct-evaluation holes. The delivered file contains
   no `sorry`, forbidden declaration or kernel-check bypass, and no data definition.
   The existential witnesses of imported theorems are eliminated inside the theorem
   proof; no arbitrary choice is exported as a definition. The descended arrow `g`
   is fixed by the colimit universal property and full faithfulness of lifted Yoneda.
3. **Split statements and edge cases: pass.** No new hole or split-off statement is
   introduced. Read the exact signatures of both imported geometric theorems.
   The retained objects `V (r.s₀ j)` inherit affineness and weak contractibility from
   the original covering; those properties are never asserted for the refinement
   objects. Checked empty indexing: dependent choice constructs the empty tuple and
   the product bijection still supplies the required section. Checked a non-quasi-
   separated compact base: the helper applies the finite-affine-cover instance only
   over each affine chart, then uses the bind instance. It never assumes a morphism
   from an affine scheme to an arbitrary base is quasi-compact. Repeated retained
   indices cause no problem for either covering refinement or the product argument.
4. **Route and pruning: pass.** Read Stacks
   [0F4P](https://stacks.math.columbia.edu/tag/0F4P),
   [0990](https://stacks.math.columbia.edu/tag/0990), and
   [090K](https://stacks.math.columbia.edu/tag/090K), and the Mathlib sources
   `Cover/QuasiCompact.lean` (`exists_hom`, pullback, bind, finite affine covers,
   `of_hom`) and `Cover/Open.lean` (`finiteSubcover`). They support precisely the
   finite-refinement, finite-union, and section-product route. A fresh Lean Finder
   search for a finite refinement of a quasi-compact scheme cover returned the
   existing compact-open witness and finite-subcover APIs, rather than a direct
   replacement for the chartwise helper. Searched `lean/Sheaf` and
   `lean/WeilConjectures` as well: upstream `exists_isWeaklyContractible_cover`
   supplies a covering sieve and a family, not the requested affine singleton
   precoverage, so it is not a direct replacement for this proof. Both proof imports
   are used; the sole public import supplies the public statement's vocabulary.
   The old `proof_deps` loses exactly
   `lem-weil-pbc-proetale-qcqs-finite-family-geometry`, already listed under
   `No longer needed`. Read `dag/units/sk-thm-properbasechange.json`: neither this
   bundle nor its site-limits branch realizes a unit statement or step. The unit's
   projective-line, reduction, and torsion-assembly realizations are preserved.
   No claim of global removal of those modules is made.
5. **DAG: pass.** Compared the two node files: only `proof`, `proof_deps`, and
   `proof_origin` change. The statement, source, unit, and Lean signature record
   are unchanged. The dependency set equals the union of all proof-step `uses`.
   Steps match the Lean: covering family; chartwise finite refinement; coproduct
   descent and transfer of the quasi-compact covering condition; lifting sections
   factorwise and using naturality and injectivity. `WeaklyEtale.of_comp` justifies
   the arrow's weakly etale property from its structural composite. The direct
   coproduct theorem replaces the unused larger bundle without using its proof.

Second-reading changes: appended this independent review and search evidence to the
report. The Lean proof and DAG were correct as delivered and were left unchanged.
