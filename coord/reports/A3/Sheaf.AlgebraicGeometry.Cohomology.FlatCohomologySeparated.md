## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.H.baseChange_bijective_of_isSeparated`
without changing its signature or public imports. The proof chooses
`X.affineCover.finiteSubcover`, checks that its open ranges form a finite affine
cover, obtains the canonical Cech chain isomorphism, applies its cohomology
compatibility square, and proves that the resulting composite is an isomorphism.
`ConcreteCategory.isIso_iff_bijective` then proves the original conclusion.

Added one proof-only import of
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechNaturality` to the item.
Added two modules, each with one public theorem left with sorry:
`FlatCohomologyCechBaseChange` and `FlatCohomologyCechNaturality`.
Their definitions reuse the library's ordered Cech complex after restricting
scalars along the displayed map to Spec R. A concrete coordinate predicate
specifies the canonical pure-tensor map through the module adjunction unit.

Proved `baseChangeCover_intersection_le`, `extendScalarsTensorIso`,
`extendScalarsTensorIso_hom_tmul`, and `flatCechHomologyIso`. The pure-tensor
formula for the tensor identification is proved by reflexivity. The scalar-extension identification uses the identity
R-linear equivalence from S with the categorical restriction-of-scalars action to
S with its given algebra action, tensors that equivalence, and proves S-linearity
by tensor induction. The homology isomorphism follows from exactness of flat
extension of scalars and Mathlib's `ShortComplex.mapHomologyIso`.
No new definition contains sorry or uses an unproved theorem to choose its data.

The two remaining lemmas are strictly different parts of the original argument:
the first concerns chain-level affine sections and does not assume flatness or
that the family covers X; the second identifies the induced cohomology map and
makes no invertibility assumption on the chain map. Neither asserts the item's
bijectivity conclusion. Updated the item's proof route and supplied nodes for
both lemmas. The unit's route remains the finite affine Cech argument.

Validation: all three modules compile together through lcompile.py.
The deliver3.py --no-push dry run printed OK: local compilation, the axiom
probe, server compilation and preflight passed, except for the second reading
which the second reader writes. Nothing was pushed. An earlier dry run found
a missing server artifact for the existing FlatCohomologyComparison module;
retrying after its refresh resolved the failure without changing that module. The edge
cases were checked against the statements: an empty indexing family gives the
zero Cech complex; an empty scheme admits this cover; degree zero is included;
no boundedness assumption is imposed; the base algebra may be the zero ring or
R itself; no properness, field, or finite-dimensionality assumption was added.
Mathlib/blueprint/library searches found no existing result with these explicit
Ext/scalar/unit interfaces. LeanSearch was unavailable; the requests and the
successful LeanFinder, Loogle, and grep searches are recorded in searches.jsonl.

## Proved and sorry left

Proved the item's only former sorry:
`AlgebraicGeometry.Scheme.Modules.H.baseChange_bijective_of_isSeparated`
(node `lem-pc-flat-cohomology-separated`). The item's module has no sorry left.

The delivery leaves exactly two named sorries, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_cechBaseChange_iso`, node
  `lem-pc-flat-cech-base-change`, in
  `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange`.
- `AlgebraicGeometry.Scheme.Modules.exists_cechBaseChange_cohomology_square`, node
  `lem-pc-flat-cech-cohomology-square`, in
  `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechNaturality`.

Both have complete proof descriptions and sources in their docstrings and nodes.
The item is reduced to these lemmas, not yet closed over the allowed axioms alone.

## No longer needed

Relative to the current repository version, removed the item's proof-only imports
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`; the parent now uses
`FlatCohomologyCechNaturality` instead. The old direct proof dependencies no
longer used directly are `lem-pc-cech-computes`,
`lem-weil-pbc-flat-tensor-exact`, `lem-weil-pbc-module-pullback-affine-sections`,
and `lem-weil-pbc-separated-affine-open-intersection`. Their mathematical
roles remain in the two split lemmas' plans (exact tensor through the existing
Mathlib homology-comparison node). No node is claimed globally pruned.
The parent proof_deps records the chain comparison, the cohomology square,
the canonical comparison and the existing Mathlib homology-comparison node.

Removed the unused public import of
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` from the new chain
module after compilation; only its smaller Cech/section infrastructure is needed
for the new signatures. The Leray theorem remains a proof dependency of the
cohomology-square node. Descent is imported by the new naturality module because
its exposed exact-homology definition uses the flat scalar-extension instance.

Deleted the previous sandbox's unproved `FlatCohomologySeparatedEquiv` helper;
it was never a repository module. Also deleted the sandbox copy of
`FlatCohomologyComparison`, which was identical to the repository's file and
needed no adaptation. Neither is part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt asserted existence of an unspecified linear
equivalence and tried to use its bijectivity for H.baseChange. An arbitrary
equivalence does not identify the canonical comparison and therefore cannot
prove the item's statement. This delivery supplies the missing canonical-map
identification separately from the chain isomorphism.

The existing Leray declaration provides Nonempty of a linear equivalence, not
an inverse-image naturality theorem tying its choice to H.baseChange. The
existing `BaseChangeMapCech` lemma uses derived sheaf-module objects and its
Lean signature does not expose the ordered ModuleCat complexes or the Ext-based
comparison of this item. It cannot directly fill this interface gap.

The planned affine-section lemma uses `tensorPullback`, while H.baseChange uses
the library's `pullback`. Transferring the section comparison through the
unit-compatible uniqueness of left adjoints is part of the chain lemma's proof;
it must preserve the adjunction-unit formula. This is recorded explicitly.

The Stacks source was read online at Tags 02KH, 02KG, 01XD and 02KE;
the node proof_origin is marked agent for the explicit Lean-interface argument.
No statement correction or change record is required. No unit or target was
changed. No proof dependency was treated as unusable merely because it has sorry.

## New nodes

`lem-pc-flat-cech-base-change` in
`dag/nodes/sec-picard-framework/lem-pc-flat-cech-base-change.json`
is the finite affine chain comparison, with a fully defined canonical coordinate
predicate. It inherits unit `sk-thm-picard-rr` and realizes the chain-level tensor
identification in the separated paragraph of flat base change. The finite family
need not cover X, and flatness is not assumed.

`lem-pc-flat-cech-cohomology-square` in
`dag/nodes/sec-picard-framework/lem-pc-flat-cech-cohomology-square.json`
is the naturality/identification of the canonical cohomology comparison under
Leray and exact tensor. It applies to every chain map with the coordinate formula,
without asserting its invertibility. It inherits the same unit and realizes the
passage from the Cech model to the specified Ext comparison. Existing derived
Cech comparison nodes do not state this interface. There are no change records.


## Second reading by A3

1. PASS: compared the parent module with the current repository version using
   diff. Its existing declaration signature and docstring are byte for byte
   unchanged; only its proof and proof-only imports differ. The other two
   modules are new. No target or existing definition changed, and no change
   record is required.
2. PASS as a reduction, not a closed target: all three delivered files compile
   locally in import order. A scratch copy printed axioms for the parent and
   every new definition/theorem. The helper definitions, tensor identification,
   inverse-image inclusion and flat homology isomorphism use only propext,
   Classical.choice and Quot.sound. The parent and the two named split theorems
   additionally use sorryAx; exactly those two split theorems contain textual
   sorry. No forbidden declaration or hollow definition was found. The scratch
   copy was removed before delivery.
3. PASS: read both split statements, their coordinate predicate, docstring
   proofs and nodes. Checked the empty indexing family, an empty scheme,
   a singleton affine cover, degree zero, identity scalar extension, the zero
   algebra, and nonflat extension at chain level. The coordinate restrictions
   are invertible identifications of categorical product opens with tuple
   infima, so the predicate determines the whole chain map on pure tensors.
   The first split needs neither flatness nor a covering assumption; the second
   accepts any canonical chain map and assumes no invertibility. Thus neither
   merely renames the parent's conclusion. Read Stacks Tags 02KH, 02KG, 01XD
   and 02KE. Independent LeanFinder searches for restriction-of-scalars Cech
   homology and canonical pullback, Loogle searches for homologyMap/IsIso and
   ShortComplex.mapHomologyIso, and rg searches with tensor/scalar/pullback
   terms found algebraic tools and related Cech refinement results but no
   complete replacement. Read BaseChangeMapCech and the affine-section and
   Leray signatures: they do not identify this specific Ext comparison.
   The remaining geometric/naturality proofs are not a few-minute closure.
4. PASS after repair: the parent selects a finite affine cover, combines the
   two canonical comparisons, and uses the proved exact homology isomorphism
   and ConcreteCategory.isIso_iff_bijective. No arbitrary equivalence is used
   to stand for the canonical map. Removed the unused public import
   Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact from the new chain
   module and recompiled all three files. Other imports support exposed
   statements/definitions, except the parent's explicit proof-only import.
   Corrected No longer needed against the current repository baseline and
   listed every removed direct proof dependency. Read
   dag/units/sk-thm-picard-rr.json: its realized fields remain unchanged, and
   the finite affine Cech route is retained.
5. PASS: checked the parent proof/proof_deps/proof_origin against the actual
   combination and checked both new nodes' statements, recorded Lean
   signatures, sources, proof-step dependency unions, search records,
   creation/blueprint/chapter/unit fields and lean records. No node repair
   was necessary. Existing node changes are confined to proof, proof_deps
   and proof_origin.

Second reading changed only the unused new-module public import and the
report's pruning account; no Lean statement or proof body was rewritten.
