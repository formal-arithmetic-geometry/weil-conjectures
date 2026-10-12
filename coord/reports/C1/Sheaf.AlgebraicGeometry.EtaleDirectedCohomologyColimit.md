## What changed

Proved `AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isDirected` with its
signature and existing docstring unchanged. Its proof now explicitly establishes
preservation of the supplied cocone, including its original mapped legs.

A proved private helper `sections_isColimit` transports the existing theorem
`AlgebraicGeometry.etale_sections_filtered_colimit` from module sheaves to abelian
sheaves. It uses the equivalence between abelian groups and Z-modules, proves that
its induced sheafCompose functor is left adjoint, applies the module-sections
comparison, and reflects its colimit structure through the coefficient equivalence.
This also resolves the coefficient-universe issue: Z itself has universe zero,
but its module carriers and the filtered index have universe u+1. Grothendieck
abelianness at that size is transported explicitly along the coefficient equivalence.

The main proof transfers preservation of evaluation at the terminal etale object
to global sections, uses the existing degree-zero derived-functor isomorphism,
and inducts over the degree. The successor uses the existing proved abstract dimension-shifting theorem
from `Sheaf.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor` and one
new strictly intermediate result: injective-colimit acyclicity at coefficient size.
It then constructs the existing natural single-complex/right-derived comparison
and transfers colimithood with `IsColimit.mapCoconeEquiv`.

Added proof-only imports of `Sheaf.AlgebraicGeometry.EtaleSectionsFilteredColimit`,
`Sheaf.AlgebraicGeometry.EtaleInjectiveColimitAcyclic`,
`Sheaf.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor`, and
`Mathlib.CategoryTheory.Sites.Adjunction`. The original public import is retained.
Updated the original node's proof, proof_deps and proof_origin to match this argument.
No existing definition, public signature, target, or unit route is changed.

Both delivery modules compile together with lcompile.py without warnings.
The new acyclicity statement was checked against Stacks Tag 0739. The existing
proved successor criterion is universe-polymorphic and applies to this filtered index.

## Proved and sorry left

Proved/reduced the sole original sorry:
`AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isDirected`
(node `lem-weil-pbc-etale-directed-cohomology-colimit`).
The item's module now contains no sorry. The new private helper is also proved.

Exactly one sorry is added, the entire proof of a public named theorem in
its own module, with a source and complete natural-language proof:

- `AlgebraicGeometry.Scheme.isZero_rightDerived_globalSections_colimit_of_injective_coefficientSize`
  in `Sheaf.AlgebraicGeometry.EtaleInjectiveColimitAcyclic`, node
  `lem-weil-pbc-etale-injective-colimit-acyclic`. This is only the acyclicity
  claim of Step 5 of the original plan, not preservation for arbitrary sheaves.
Edge cases: the successor criterion includes n=0, where the injective term in
its cokernel row cannot be omitted. Singleton diagrams, zero diagrams, and the
empty scheme satisfy the acyclicity statement. The main proof requires the same
nonempty directed index as before and never shrinks it to universe u.

## No longer needed

No import from the original file was removed: its sole import supplies its public
statement. During development, redundant explicit imports of
`Mathlib.Algebra.Category.Grp.ZModuleEquivalence` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal` were removed after compiling
without them; their APIs are already available through the retained imports.
An exploratory import of `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`
was removed. Terminality follows directly by reflecting Mathlib's terminal identity
object of Over X, so this large module is not required.

The route no longer needs these original nodes as separate proof dependencies:

- `def-weil-pbc-kinjective-resolutions`, module
  `Sheaf.AlgebraicGeometry.KInjectiveResolutions`;
- `prop-weil-pbc-cohomology-resolution-independent`, module
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
- `lem-weil-pbc-cohomology-pullback-functorial`, module
  `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.

The existing natural single/right-derived isomorphism and total/bounded-below
compatibility already supply the final identification; no scheme-pullback theorem
or separately chosen resolution is used. These are local pruning claims, not
claims that other targets no longer need those modules.

The geometry/Cech dependencies of original Steps 2 and 5 move under the new
acyclicity node: etale composition/cancellation, qcqs permanence, cofinal finite
coverings, affine qcqs, sections colimits, the Cech complex, injective Cech
acyclicity, exact filtered abelian colimits, and the Cech vanishing criterion.
Functorial injective embeddings, long exact sequences, natural connecting maps,
injective derived vanishing, and the four/five lemma move under the existing proved successor
node `lem-weil-pbc-right-derived-filtered-colimit-successor`. They are retained there, not pruned. Original definition nodes remain
statement dependencies or dependencies of these intermediate nodes.

Every original proof dependency removed from the item directly is listed here;
except for the three locally pruned resolution/pullback nodes above, these remain
statement dependencies or are used through the acyclicity/successor nodes:

- `def-sp-left-exact-additive`;
- `def-weil-pbc-abelian-etale-sheaves`;
- `def-weil-pbc-category-colimit`;
- `def-weil-pbc-cech-complex`;
- `def-weil-pbc-etale-cohomology`;
- `def-weil-pbc-etale-site`;
- `def-weil-pbc-kinjective-resolutions`;
- `def-weil-pbc-scheme-conventions`;
- `lem-weil-pbc-affine-scheme-qcqs`;
- `lem-weil-pbc-cech-vanishing-criterion`;
- `lem-weil-pbc-cohomology-pullback-functorial`;
- `lem-weil-pbc-derived-functor-injective-vanishing`;
- `lem-weil-pbc-derived-functor-long-exact`;
- `lem-weil-pbc-etale-composition-cancellation`;
- `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`;
- `lem-weil-pbc-five-lemma`;
- `lem-weil-pbc-grothendieck-functorial-injective-embedding`;
- `lem-weil-pbc-horseshoe-delta-functor`;
- `lem-weil-pbc-injective-sheaf-cech-acyclic`;
- `lem-weil-pbc-qcqs-morphism-permanence`;
- `prop-weil-pbc-cohomology-resolution-independent`;

## Where the brief, the DAG or earlier work was wrong

The existing `etaleCohomology_isColimit_of_isFiltered` only has index universe u;
its signature cannot be directly used for this item. The existing sections theorem
is sufficiently universe-polymorphic, but is stated for modules, so the coefficient
transport above is necessary rather than a bare application to abelian sheaves.

The original DAG's final step invokes a scheme-pullback naturality theorem although
only coefficient-functor naturality is needed. It also separately invokes resolution
independence and a module-valued K-injective-resolution definition. Those ingredients
are unnecessary once the already proved natural derived-single comparison is used.
The original source references are otherwise mathematically sound. No disputed
statement or tool workaround is introduced.

## New nodes

`lem-weil-pbc-etale-injective-colimit-acyclic`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-injective-colimit-acyclic.json`,
is the positive-degree global-sections vanishing of an injective-diagram colimit.
Its four steps record the qcqs basis, the existing sections comparison, Cech
acyclicity, and evaluation at the terminal object. It is not a restatement of
the original theorem. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleInjectiveColimitAcyclic.lean`.

The acyclicity node inherits chapter and unit from the item, carries three kinds of
Mathlib search, and cites the existing nodes for its parts. The existing theorem
of the same mathematics has an index of universe u, so it cannot replace this
coefficient-size (u+1) statement. There are no change records because no existing
statement or definition changed.

## Second reading by C1

1. Compared the delivered item with the repository using diff. The sole existing
   theorem signature and its full docstring are byte-for-byte unchanged. There
   are no existing definition changes and no target changes. Verdict: pass.
2. Compiled both modules in import order with lcompile.py. No errors or warnings;
   the item has no sorry, and the only added sorry is the whole proof of the named
   public acyclicity theorem. Scanned for axiom, unsafe, opaque, implemented_by,
   extern, and hollow definitions. Printed axioms for the main theorem, the new
   acyclicity theorem, and the reused successor theorem: only propext,
   Classical.choice, Quot.sound, and sorryAx (open dependencies). Verdict: pass
   as a reduction, not an axiom-free completion of the target closure.
3. Read the acyclicity proof against Stacks Tags 0739 and 03Q5. Its finite qcqs
   coverings and Cech-vanishing argument establishes precisely the stated positive
   derived-global-sections vanishing. Checked q=1, singleton and zero diagrams,
   and the empty scheme. Searched LeanFinder with "positive sheaf cohomology
   vanishes for direct limits of injective objects on a coherent site", and rg
   for acyclic colimits and derived-colimit preservation across both library roots.
   Found the existing smaller-index acyclicity statement (not applicable at u+1)
   and an applicable proved successor criterion. The remaining split is a strict
   part of the argument and has its source, complete proof docstring and node.
   Verdict: pass after removing the redundant successor split.
4. Read from the target through degree zero, induction, and the natural derived
   comparison. Replaced the new successor sorry by the existing proved theorem.
   The sections helper retains the original cocone legs through coefficient
   transport and reflection. All proof-only imports are plain imports. The unit
   sk-thm-p1 realized fields and its route are unchanged; this is below unit level.
   The No longer needed section accounts for all old proof dependencies removed
   directly, including those retained indirectly. Verdict: pass after repair.
5. Checked every proof step's uses union against proof_deps, the new Lean statement
   against its node record, and the existing node's allowed-field diff. Updated
   the item to cite the existing successor node. Removed the duplicate successor
   module and node. Renamed the new acyclicity declaration with coefficientSize
   to avoid colliding with the existing smaller-index declaration. Verdict: pass.

Changes in this second reading: reused the existing proved successor criterion;
removed one duplicate module, node and sorry; renamed the coefficient-size
acyclicity declaration and updated its node and call site; corrected this report.
