## What changed

The signature and public imports of
`AlgebraicGeometry.Etale.exists_etale_limit_finite_cech_stage_data` are unchanged.
Its proof now obtains a finite descended covering, constructs every nerve comparison
and pullback-pasting isomorphism, invokes the coefficient construction, and assembles
all ten groups of equations into the original existential conclusion.

The private proved helper `nerve_iso` uses the finite-limit-preserving slice functor
`Over.post B ⋙ Over.map eU.hom`. `PreservesProduct.iso`, `Pi.mapIso`, and
`piComparison_comp_π` give the product comparison and its projection equations.
The private proved helper `pasting_fst` uses Mathlib's actual `pullbackComp` inverse
and proves its first-projection equation. The transition base equality follows from
`D.map_comp` and subsingleton preorder homs; the limit equality follows from `c.w`.
These prove the geometric comparison part of the original plan outright.
The outer stage witnesses are fixed immediately after cover descent, before
constructing the comparisons; unused proof-local Pj and Plim bindings are omitted.
The final single-file compile of the item took 9.4 seconds.

Two new modules state separate remaining parts of the plan:
`Sheaf.AlgebraicGeometry.EtaleLimitFiniteCoverDescent` is only geometric descent;
`Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientData` constructs only the
coefficient complex diagram and cocone from already supplied descended geometry
and all four comparison equations. The latter requires neither a limit cone nor a
colimit cocone, affine transitions, qcqs objects, or covering families. Both carry
complete proof descriptions and corresponding nodes. Neither restates the original
existential stage-and-complex theorem.

Source texts were read online at Stacks Tags 01ZM, 07RP, 07RR, 09YP, and 09YQ;
the local literature checkout contains only the reference lists. Searches used the
specified msearch wrapper: LeanFinder and Loogle returned partial geometric/Cech
matches, Mathlib grep found the Cech functor and pullback composition, and
LeanSearch returned Internal Server Error for both queries. Blueprint keyword
search and repository search found no matching full statements. In particular,
EtaleFiniteCoverFactorizationDescent assumes affine sources and a fixed affine
target, and ColimitSiteCechComplex requires a different strict site diagram.

The three delivery modules compile together using lcompile.py, without warnings.
Every Lean line is at most 100 characters. An attempt to omit the explicit proof
import Mathlib.CategoryTheory.Limits.MorphismProperty timed out in instance
synthesis; this import is retained to expose the needed preservation instances.
No existing statement, definition, visibility, or target signature changes.

The first deliver3.py dry run printed OK, with a note that its general axiom probe
on the main module timed out at 60 seconds. A separate scratch module importing
the compiled delivery then ran #print axioms on all three public theorems in
14.3 seconds. Each returned exactly propext, Classical.choice, Quot.sound and
sorryAx, as expected from the two named remaining holes. There is no additional
axiom. The scratch module was removed from the delivery. The merge reruns the
general probe; this initial timeout is recorded here for the second reader.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.Etale.exists_etale_limit_finite_cech_stage_data`
(node `lem-weil-pbc-etale-limit-finite-cech-stage-data`). No sorry remains in the item.
The private helpers `nerve_iso` and `pasting_fst` are fully proved from Mathlib.

Added holes, each in its own new module and exactly `:= by sorry`:

- `AlgebraicGeometry.Etale.exists_etale_limit_finite_cover_descent`
  (`lem-weil-pbc-etale-limit-finite-cover-descent`).
- `AlgebraicGeometry.Etale.exists_etale_limit_finite_cech_coefficient_data`
  (`lem-weil-pbc-etale-limit-finite-cech-coefficient-data`).

This is a decomposition: one upper hole closed and two lower holes added,
net minus one hole closed before any closure/pruning adjustment. It is not a
claim that the theorem or its new dependencies are sorry-free. The nontrivial
nerve comparisons and both pasting equations are proved without new holes.

Edge cases checked mathematically: empty K gives no positive-length tuples and
zero section products; empty covers descend by surjectivity of the empty source.
For a singleton index, the geometric maps reduce to pullbacks along identities;
no strict equality of pullback objects is assumed. Nontrivial automorphisms of
the chosen object identifications are accommodated by the arrow and projection
equations. No separation beyond the original quasi-separatedness is used.
The coefficient theorem works without directedness because it only constructs a
diagram on the given tail; it uses no cofinality or colimit universal property.

## No longer needed

Removed from the item's direct proof imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `Sheaf.AlgebraicGeometry.DescendSurjective`.

The old direct proof edges to `thm-pd-spreading-out`,
`lem-weil-pbc-descend-etale`, `lem-weil-pbc-descend-surjective`,
`lem-weil-pbc-qcqs-morphism-permanence`, and
`lem-weil-pbc-etale-base-change-continuous` now belong to the new geometric
finite-cover descent node. They are not mathematically eliminated from the
argument. The old direct proof edges to `def-weil-pbc-inverse-image` and
`def-weil-pbc-cech-complex` now belong to the new coefficient node.
These definitions remain used through that node. The original finite-limit and cartesian-pasting dependencies
remain: the private helpers now prove their concrete required comparisons.
No blueprint unit statement or realized step is bypassed. No further planned
node is pruned, and no claim is made that these removed direct imports become
unreachable globally.

The attempted temporary proof imports
Mathlib.CategoryTheory.Adjunction.Limits and
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products are redundant and
were removed before delivery. The geometric new module imports only the
small-etale-site interface; the coefficient new module uses Coherence and
ConcreteCoefficients rather than the larger TopologicalInvariance module.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or unit route was found. The source node's finite-limit
and pasting steps really are supplied by Mathlib; they do not need separate
unproved comparison statements. The remaining descent and coefficient laws do
not follow by a single application of the recorded declarations with this
interface, so they are isolated as two strictly smaller parts of the existing
argument rather than left inside a partial proof. LeanSearch was unavailable;
no negative search verdict is attributed to that unavailable service.

## New nodes

`lem-weil-pbc-etale-limit-finite-cover-descent` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-limit-finite-cover-descent.json`
states step 1 of the parent plan: stage descent, qcqs models, fixed arrow equations,
and covering at all later stages, with no sheaf or complex data. Its source is
Stacks 01ZM, 07RP, 07RR and the scheme realization of 09YQ.

`lem-weil-pbc-etale-limit-finite-cech-coefficient-data` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-limit-finite-cech-coefficient-data.json`
states step 3 with fixed descended data and comparisons supplied as hypotheses;
its conclusion contains only the diagram/cocone and two coefficient equations.
Its source is the canonical Cech comparison in Stacks 09YP, realized in 09YQ.
It proves no geometric descent and asserts no colimit property.

The parent node's proof, proof_deps, and proof_origin now follow the delivered
Lean proof. There are no change records, since no existing interface changes.


## Second reading by C1

1. Interface: compared the delivered main module with the repository using diff,
   then compared the complete existing theorem signature programmatically. It is
   byte for byte identical. All existing public imports, visibility, options,
   and the declaration docstring are unchanged. Only proof imports and the proof
   changed, with two new private proved helpers. No definitions or target
   statements changed; no change record is needed. Verdict: pass.
2. Proof: independently compiled all three modules in import order with
   lcompile.py (5.0, 2.3, and 10.9 seconds), without errors or warnings. Scanned
   every delivery module for forbidden declarations and for sorry: exactly the
   two reported named public theorems have sorry, each exactly `:= by sorry`.
   An import-only scratch probe printed axioms for all three public theorems:
   only propext, Classical.choice, Quot.sound, and sorryAx. A separate scratch
   copy of the helpers printed their axioms: only the three permitted standard
   axioms, with no sorryAx. Both scratch sources were removed. Existential
   witnesses of the open lemmas are eliminated inside a theorem of Prop; no
   definition chooses arbitrary data from an unproved existence theorem.
   Verdict: pass as a decomposition, not a sorry-free proof of the item.
3. Split statements: read both whole signatures and docstring arguments.
   Geometric descent uses finite presentation of qcqs etale sources, object and
   arrow descent, a finite common upper bound, and surjectivity descent for the
   finite union. Verified Stacks 01ZM, 07RR, 09YP and 09YQ online. The coefficient
   lemma uses fixed descended geometry, and proves no descent or universal
   property. Its arbitrary comparisons are fixed by their projection equations:
   a positive-length product has at least one coordinate, which also fixes the
   map to the covering target; the base projection of each pasting morphism is
   fixed by its being an etale-category morphism. Thus coordinate deletion and
   identity/composition transport follow by product/pullback uniqueness.
   Checked empty K, singleton K, an empty geometric target, one-stage systems,
   and nontrivial chosen object identifications. Both lemmas are true, needed,
   and strictly smaller than the item. Independent searches used LeanFinder
   queries for jointly surjective finite families and for cochain maps via
   product-preserving functors, Loogle `cechComplexFunctor` (identifier absent
   from that service), and Mathlib grep on Cech maps. Repository searches checked
   inverse-limit descent, finite-cover factorization, and varying-site Cech
   transport. No exact replacement was found: existing descent theorems provide
   individual steps, the finite-cover theorem requires affine objects, and the
   abstract site theorem requires strict diagram data. Neither open statement
   can be closed by an available single application in a few minutes.
   Verdict: pass; two remaining named holes, with complete takeover arguments.
4. Route and pruning: read the original node plan and the unit sk-thm-p1 realized
   record. The delivered reduction follows geometric descent, nerve/pasting
   comparisons, then coefficient transport. Finite-product preservation and
   pullbackComp actually prove the middle step; it is not hidden in a renamed
   copy of the item. All seven old proof edges removed from the parent are
   explicitly accounted for under No longer needed and retained in the new
   nodes where needed. The finite-limit and pasting edges remain. The new
   fibre-product edge describes the product/projection construction. The unit's
   realized statement and steps are retained. Proof-only new imports use plain
   import; new public imports provide their statements and necessary instances.
   No globally unreachable module is claimed pruned. Verdict: pass.
5. Nodes: verified that the only fields changed on the existing node are proof,
   proof_deps, and proof_origin, and that proof_deps is the union of step uses.
   Compared all three stored Lean signatures with the actual files: exact
   matches. Both new nodes have source, complete proof steps, search records,
   created/group/item, blueprint provenance, chapter, unit, and Lean records.
   Their scopes match the two remaining geometric and coefficient holes.
   Verdict: pass.

Second-reading changes: made the two inverse-image/Cech dependency identifiers
explicit in No longer needed and added this independent review and validation
record. No Lean repair was necessary. One original hole is replaced by two
strictly smaller holes (net minus one closed); the delivery is a decomposition.
