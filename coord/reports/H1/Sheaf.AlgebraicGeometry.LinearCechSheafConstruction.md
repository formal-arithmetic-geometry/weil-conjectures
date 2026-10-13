## What changed

Proved `AlgebraicGeometry.exists_augmented_linear_cech_sheaf_complex` with its original
signature and all four conclusion clauses unchanged. The only delivered Lean module is
`Sheaf.AlgebraicGeometry.LinearCechSheafConstruction`.

The proof uses the explicit `cechModuleSheafComplex`, its degree-zero augmentation and
its proved cocycle equation from `CechModuleSheafFunctor`, plus
`cechModuleSheafComplex_term_iso` from `CechModuleSheafTerms`. Added one proof-only import:
`Sheaf.AlgebraicGeometry.CechModuleSheafTerms`, which also makes the functor available.
The original two public imports are retained because the statement needs them.

The sectionwise comparison theorem hides its existential witness and therefore cannot
supply local scalar compatibility. Its canonical comparison implementation is reproduced
as private, fully proved helpers in this module (with private local instances), with
`linearCechComparison` stating the
differential and augmentation equations for that specific comparison. In the final proof,
the coordinate equation `hc` reduces a coordinate to the module-sheaf product projection;
its section map's `LinearMap.map_smul` proves the local scalar equation. The comparison's
scalar-restriction identification has identity underlying maps.

Updated only `proof`, `proof_deps`, and `proof_origin` in
`lem-pc-linear-cech-sheaf-construction` to record this implemented route. No existing
statement, definition, public visibility, target, or other module was changed. No arbitrary
object was selected from a holed existence theorem. The construction works without a
cover, including empty index types and infinite families.

Searches run through msearch: LeanFinder query “Cech complex of module sheaves product
comparison local scalar multiplication” returned scalar/sheafification and sectionwise
projection tools but no exact theorem; Loogle `CategoryTheory.cechComplexFunctor` found
that construction; grep `cechModuleSheafDegreeIso|exists_augmented_linear_cech_sheaf_complex`
returned no upstream matches. Repository rg located the existing functor, comparison,
terms and non-linear construction. Read their signatures and proofs. Read Stacks Tag 02FU
at https://stacks.math.columbia.edu/tag/02FU: the displayed sheaf product and canonical
augmentation are the relevant construction; covering is used later for exactness, which
this item does not assert. The unit's realized statement/steps arrays are empty; the
construction follows the displayed Cech route, and no unit step is bypassed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.exists_augmented_linear_cech_sheaf_complex`
(node `lem-pc-linear-cech-sheaf-construction`).

No `sorry` remains in the delivered module. No holes were added or split off. Every private
helper is fully proved. This is a proof, not a decomposition.

## No longer needed

No existing import was removed. No global module-pruning claim is made: other targets may
still need any module mentioned here.

For this proof, `def-weil-pbc-site-cech-complex` and its recorded module
`Sheaf.CategoryTheory.SiteCechComplex` are not proof dependencies. The concrete Mathlib
`cechComplexFunctor` and `cechModuleSheafComplex` are used directly. The node remains a
statement dependency, so this does not claim its removal from the whole DAG.

The proof does not import `Sheaf.AlgebraicGeometry.CechModuleSheafComparison` or
`Sheaf.AlgebraicGeometry.CechSheafConstruction`, and does not apply their existential
theorems (`lem-pc-cech-module-sheaf-comparison`, `lem-pc-cech-sheaf-construction`). Their
canonical comparison argument is implemented locally because the local scalar clause
needs the specific comparison, rather than an unspecified existential witness.
No local exactness, covering, quasi-isomorphism, affine-cover, or ordered-Cech modules
are needed for this construction.

## Where the brief, the DAG or earlier work was wrong

The original DAG cited only definitions for a substantial construction; existing proved
modules already supply the concrete sheaf functor and open-direct-image term description.
The public comparison theorem does not specify its witness, so applying it alone would
not justify the last local scalar clause. The proof retains and checks its canonical
implementation rather than assuming every globally linear natural isomorphism is locally
linear. No mathematical statement was corrected.

`tools/import_direction.py may` failed while reading a missing repository file
`lean/Sheaf/AlgebraicGeometry/AlternatingCechSheafLocalContraction.lean` (FileNotFoundError).
The tool was not edited or bypassed by modifying project state. The delivery tool runs its
independent cycle check over the delivered sources. No other tool change is requested.

Repair of the return at landing-tools head 8f5eda331: generalized the two private
helpers in place rather than duplicating the existing private statements.
`intersectionProductComparison_hom_π` applies to any universe-sized family of opens
W : α → X.Opens, not only products indexed by Čech tuples. Its proof is the product
comparison projection calculation; the augmentation and scalar proofs specialize it.
`cechModuleSheafDegreeIso_naturality` applies to every simplex morphism between arbitrary
degrees, including codegeneracies, rather than only cofaces. The differential proof
specializes it to SimplexCategory.δ. Both generalizations are fully proved and used.
The existing helpers in CechModuleSheafComparison are private, so they cannot be imported
and applied directly. No other module is changed. The earlier second reading predates
this repair and has been removed so that the second reader can assess the repaired file.

## Second reading by H1

1. Interface comparison: read the complete repository/sandbox diff for the only
   delivered module and node. The signature of
   `AlgebraicGeometry.exists_augmented_linear_cech_sheaf_complex`, from `theorem`
   through its last conclusion before `:=`, is byte-for-byte identical. Its original
   docstring and two public imports are unchanged. All added declarations and instances
   are private; the added Terms import is proof-only. No existing definition, target,
   visibility, or other module changed. Verdict: pass; no change record is needed.
2. Proof and axioms: compiled the delivered file locally with `lcompile.py` (14.1 s,
   exit 0, no warnings). Regenerated the scratch audit from the repaired file, rather
   than trusting the stale pre-repair copy, and printed axioms for all twelve added or
   proved declarations, including both generalized helpers and the public theorem.
   The audit compiled cleanly (13.4 s); every list contains only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Source scan found no sorry,
   axiom, unsafe, opaque, extern, implemented_by, or kernel-check bypass in delivered
   Lean. All lines meet the 100-character limit. D, epsilon and e are actual
   constructions; the term isomorphism theorem is proved, and no arbitrary witness
   from an unproved existence theorem is selected. Verdict: pass.
3. New statements and small cases: no public statement or split-off hole was added.
   Read every private helper. The generalized projection identity is exactly the
   composition of Mathlib's `Pi.mapIso_hom_π` and `piComparison_comp_π_assoc` for any
   family W. The generalized simplex identity is naturality of the constructed
   cosimplicial isomorphism; its component equality is checked by `rfl`, and it covers
   identities and degeneracies as well as the cofaces used in the differential.
   Empty families make coordinate clauses vacuous and use preserved empty products;
   p=0 uses the actual single-degree augmentation identity. Empty schemes, zero
   modules, repeated opens and infinite families require no extra hypothesis.
   Verdict: true helpers, with no split-off statement to validate or close.
4. Route and pruning: read CechModuleSheafFunctor, CechModuleSheafTerms, and the
   private comparison implementation and public existential signature in
   CechModuleSheafComparison. Independently searched repository/upstream source for
   scalar-compatible Cech constructions, and Mathlib for product comparison and
   scalar-composition tools. Mathlib's restrictScalarsComp'App has identity underlying
   maps; products preserve their coordinates by piComparison. An unspecified witness
   from exists_cechModuleSheafComparison supplies no local scalar equation, so it
   cannot replace the concrete comparison used here. In the final clause hc reduces
   the coordinate map to the sheaf product projection; its O_X(B)-linear map_smul
   supplies exactly restriction along prod.snd on the right, not merely global
   linearity. Read Stacks [02FU](https://stacks.math.columbia.edu/tag/02FU): its displayed
   product terms and canonical augmentation match this construction; its covering
   hypothesis is used for the subsequent exactness argument, which is not asserted
   here. The blueprint files are absent on this machine; the unit record and existing
   node/source descriptions were read. sk-thm-picard-coherence has no realized
   statement or step nodes, and its Cech route is retained. The sole old proof_dep
   omitted, def-weil-pbc-site-cech-complex, is explicitly listed under No longer
   needed and remains a statement dependency. No removed import or globally pruned
   module is claimed. Verdict: pass.
5. DAG consistency: parsed both node files and checked the only changed fields are
   proof, proof_deps and proof_origin. The proof_deps list is exactly the union of
   the uses lists. Step 1 uses the concrete functor, complex and proved augmentation
   cocycle equation; steps 2 and 3 describe the scalar and product isomorphisms,
   generalized projection and simplex naturality, and alternating-sum calculation;
   step 4 uses fromSingle₀Equiv; step 5 applies the proved term isomorphisms and local
   map_smul. Each is implemented in the delivered Lean. There are no new node files
   or changes to the node's statement, statement dependencies or Lean signature.
   Verdict: pass.

Second reading changed only this report and the scratch axiom audit (the latter is not
part of the delivery). No Lean or DAG repair was needed after the previous worker's
reported generalization repair. Confirmed one existing hole closed, zero added, zero
split off; this is a proof rather than a decomposition.
