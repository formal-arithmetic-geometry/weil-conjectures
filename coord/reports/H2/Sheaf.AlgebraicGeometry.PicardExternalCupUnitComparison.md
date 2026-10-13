## What changed

Completed the saved reduction of
`AlgebraicGeometry.Scheme.picard_external_cup_unit_comparison`, preserving its
signature and docstring. The proof tensors the two adjoint unit isomorphisms,
composes with the left unitor, and maps this coefficient isomorphism through
module cohomology and restriction of scalars. It composes the resulting additive
equivalence with the comparison on the product. The two scalar cup identities
and comparison naturality then prove both projection formulas for this same
product equivalence.

Repaired the new coefficient-identity module: its local monoidal instance is
noncomputable, and the product scheme is explicitly
`CategoryTheory.Limits.pullback`, avoiding the module-pullback name in its namespace.
Updated that new node's Lean statement to match. All three delivered modules compile.
No existing interface changes or forced adaptations are required.

## Proved and sorry left

Closed one original hole, by a decomposition into two strictly separate parts:
`AlgebraicGeometry.Scheme.picard_external_cup_unit_comparison`
(node `lem-sc-picard-external-cup-unit-comparison`). Its complete Lean proof has
no sorry. This is a decomposition, not an unconditional proof of all dependencies;
net holes closed minus added is -1.

Two holes added, each the whole proof of a public named theorem in its own module:

- `AlgebraicGeometry.Scheme.scalar_unit_cohomology_pullback_comparison`, node
  `lem-sc-scalar-unit-cohomology-pullback-comparison`: simultaneous unit-coefficient
  comparisons compatible with pullback, without cup operations.
- `AlgebraicGeometry.Scheme.Modules.external_cup_unit_coefficient_identities`, node
  `lem-sc-external-cup-unit-coefficient-identities`: scalar cup-with-one identities
  under the explicit coefficient map, without abelian comparisons.

No sorry remains in the assigned module. No data is defined using an arbitrary
witness of unproved existence. The comparison family is obtained only within the
proof of the original existential theorem.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`,
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`, and
`Sheaf.Paper.ModuleCohomologyCupProduct` from the assigned module, replacing them
with the two intermediate modules. Their nodes
`lem-sc-module-abelian-zariski-cohomology`,
`lem-weil-pbc-module-pullback-structure-sheaf`, and
`def-sc-module-cohomology-cup-product` remain dependencies of the intermediate
argument (the tensor unit isomorphism is also used by the main proof). Thus no
module or node is globally pruned. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempts were blocked before elaboration by the missing published
`ScalarUnitCohomologyCoordinates.olean`. That dependency is now available. Actual
compilation exposed the two errors repaired above; the saved reduction had not
previously been validated. No dependency was copied into the sandbox as a workaround.

The existing module-to-abelian lemma gives coefficient naturality on a fixed scheme;
it does not state scheme-pullback compatibility. The existing cup characterization
also does not directly state compatibility of scalar Ext cup with the augmented
unit class. These are the two parts extracted from parent proof steps 1–3.
Both new statements permit empty schemes, arbitrary characteristic and arbitrary
global structure-ring maps, and assume no properness, separatedness or spanning.

WANTED: `literature/stacks-project/sites-cohomology.tex`, Tag 03FD;
`literature/stacks-project/cohomology.tex`, Tag 01F7 and section-cup-product;
`literature/stacks-project/varieties.tex`, Tag 0BED. These files are absent locally.
The previous worker inspected the online Stacks pages. The expanded proofs are
recorded as agent-written explanations of the parent steps.

The ancestor tool returns None for the assigned node because its created.item is
a module name. The new nodes preserve the parent's recorded theorem-of-cube ancestry.
The unit record `sk-prop-av-cube` has no realized statement or steps to bypass.

## New nodes

`lem-sc-scalar-unit-cohomology-pullback-comparison` in
`ScalarUnitCohomologyPullbackComparison.lean` isolates parent steps 1 and 3:
common module-to-abelian unit comparisons and their scheme-pullback naturality.
It has no cup conclusion and is strictly a part of the parent argument.

`lem-sc-external-cup-unit-coefficient-identities` in
`ExternalCupUnitCoefficientIdentities.lean` isolates parent step 2 before applying
abelian comparison. The coefficient map is the explicit tensor of adjoint unit
maps followed by the unitor. It has no comparison-equivalence conclusion.

Both nodes carry the previous worker's actual LeanSearch, LeanFinder and grep
searches; LeanSearch was unavailable. Their statements now compile, and the main
node's proof and proof_deps describe the compiled combination. No change records.

## Earlier second reading (a previous round; superseded)

The assigned module and both new node modules were compiled from the sandbox after
repairing the noncomputable local instance and qualifying the categorical pullback.
The assigned theorem retains every hypothesis and both quantified equalities of
`lem-sc-picard-external-cup-unit-comparison`; its proof uses the two new statements
only as strict parts of the three recorded proof steps. The new comparison theorem
contains no cup operation, and the coefficient theorem contains no abelian comparison,
so neither restates the parent conclusion. The tensor-pullback unit route and the
recorded theorem-of-cube unit remain in the dependency plan. That earlier round recorded a namespace-open adaptation; the current repository
already has the same open command, so its stale change record is removed below.


## Second reading by H2

1. **Interfaces: pass.** Diffed every delivered module against the read-only
repository. Only the assigned module exists there; its theorem signature and
original docstring are byte for byte unchanged. Its two public imports and open
commands are unchanged. The new dependencies are plain proof imports. No existing
definition, target, hypothesis, conclusion or declaration visibility changes.
The only existing DAG node changes in proof, proof_deps and proof_origin.

2. **Proof and axioms: pass, conditional decomposition.** Independently compiled
all three modules in import order with lcompile.py (all exit zero, no warnings).
The main proof constructs the actual coefficient isomorphism from the two adjoint
unit maps, applies derived cohomology and scalar restriction, and uses the same
product equivalence for both equations. There are exactly two sorry tokens, the
whole proofs of the two reported public theorems. No forbidden declaration or
hollow definition occurs. A scratch import probe printed axioms for all three
public theorems: exactly propext, Classical.choice, Quot.sound and sorryAx.
Thus the main hole is closed only relative to the two new holes and existing
open dependencies; one closed minus two added is -1, not an unconditional proof.

3. **New statements: pass.** Read both signatures, docstring arguments and nodes
against the scalar operations' actual definitions, including the normalized
module-to-Ext comparison, inverse-image coefficient adjunction and Ext tensor cup.
The comparison lemma has no cup assertion; the coefficient lemma has no abelian
comparison or existential equivalence. They isolate distinct parts of the parent
argument and neither renames its conclusion. The canonical comparisons are
compatible with all scheme morphisms over k; no global-ring bijectivity is needed.
Checked the empty-scheme case (zero cohomology), affine schemes (degree one zero),
identity morphisms (identity comparison square), and characteristic two (no sign
in these bidegrees). These give no counterexample or extra hypothesis.
The three cited Stacks pages were independently read online:
[03FD](https://stacks.math.columbia.edu/tag/03FD),
[01F7](https://stacks.math.columbia.edu/tag/01F7), and
[0BED](https://stacks.math.columbia.edu/tag/0BED).
03FD supplies the module/abelian comparison, 01F7 its resolution construction and
functoriality, and 0BED the external-product construction; the unit specialization
and its compatibility with this library's Ext model remain the agent-written
arguments recorded in the docstrings, rather than claims that 0BED states these
new lemmas verbatim. In particular its Kunneth hypotheses are unnecessary for the
unit identities. New searches used LeanFinder for Ext cup with degree-zero identity
and Loogle for Abelian.Ext.comp; they found mk-zero identity and associativity
lemmas, but no matching normalized scalar comparison theorem. Searched lean/Sheaf
and the upstream Lean modules for unit products, comparison and pullback. Read
ModuleCohomologySourceComparison and ScalarCupCoefficientNaturality: the first
only handles coefficient maps on one scheme; the second does not identify the
augmented degree-zero unit. Neither closes these holes in a few minutes.

4. **Route and pruning: pass, no global pruning.** The explicit coefficient
isomorphism is the parent route, and its tensor-pullback unit theorem is retained.
The main proof imports only its two new proof dependencies; their public imports
provide names used in their signatures and their plain imports support the recorded
proof arguments. No existing public import is downgraded. The cube unit's realized
statement and step entries are empty and unchanged; no realized unit is bypassed.
For completeness, the old direct proof dependencies no longer in the main node's
proof_deps are lem-sc-module-abelian-zariski-cohomology,
def-sc-structure-sheaf-cohomology-pullback,
lem-sc-scalar-unit-cohomology-coordinates, and
def-sc-module-cohomology-cup-product. All remain used in the statements or the
intermediate proof arguments, so no module or node is globally pruned.

5. **Nodes: pass.** Both new nodes have matching verbatim Lean statements, named
docstring proofs and sources, creation records, ancestry, chapter/unit and search
records. Checked that each proof_deps equals the union of proof step uses. The
main node describes precisely the compiled combination and names both new nodes,
the tensor-pullback unit theorem and scalar cohomology operations. No node statement
or unit record changes.

**Second-reader repairs:** removed the stale
coord/changes/PicardExternalCupUnitComparison.md, whose claimed namespace-open
change is absent from the actual current diff; corrected the historical report
reference and completed the account of removed direct proof dependencies above.
No Lean proof or statement needed rewriting. No additional holes closed or added.
