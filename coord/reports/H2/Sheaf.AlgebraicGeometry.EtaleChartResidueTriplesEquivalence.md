## What changed

Reduced `AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_functor`
by following the three steps of the node's plan. Three new statement modules separate
construction of the compatible functor, fullness, and essential surjectivity. The original
module combines their conclusions into `Functor.IsEquivalence` and `Functor.asEquivalence`.

Faithfulness is proved directly, without a new hole: a private generic lemma proves that
global sections is faithful on any faithful diagram of affine schemes, using
`AlgebraicGeometry.ext_of_isAffine`. Faithfulness transfers across the natural ring
isomorphism, and `Functor.Faithful.of_comp_iso` gives faithfulness of the chart functor.
The same assembly now proves the original upper theorem, preserving its ring isomorphism
and both compatibility formulas definitionally. All three existing signatures stay unchanged.
A local unused-variable linter setting preserves the unused diagram lets in the existing
functor theorem's signature. All new imports are proof-only.

The two existing proof nodes now record this route. No definitions, target statements,
public imports or other modules' interfaces changed. No data is chosen from an unproved
existence theorem in any definition; the existential functor is eliminated only in proofs.

## Proved and sorry left

One of the two holes originally in this module is closed:
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_functor`
(node `split-etale-chart-functor`). This is a decomposition, not a completed geometric proof.
The previously proved `etale_chart_residue_triples_equivalence` is now assembled directly
from the three parts, avoiding the disputed helper.

The unchanged original hole remains:

- `AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_ring_iso`
  (node `split-etale-chart-ring-iso`), marked STATEMENT-DISPUTED and unused by our proofs.

Three strictly smaller holes are added, each in its own module with a source and complete
natural-language construction/proof:

- `AlgebraicGeometry.Scheme.etale_chart_residue_triples_functor_construction`
  (node `lem-weil-pbc-etale-chart-functor-construction`): a functor with its ring identification
  and formulas; neither fullness nor essential surjectivity is asserted.
- `AlgebraicGeometry.Scheme.etale_chart_residue_triples_full`
  (node `lem-weil-pbc-etale-chart-full`): surjectivity on morphisms for a given compatible
  functor; no functor or equivalence is constructed.
- `AlgebraicGeometry.Scheme.etale_chart_residue_triples_essentially_surjective`
  (node `lem-weil-pbc-etale-chart-essentially-surjective`): surjectivity up to isomorphism on
  objects for a given compatible functor; no morphism lifting or equivalence is constructed.

All files compile locally. The combination proofs contain no `sorry`. This closes one hole
and adds three, for net -2 in this decomposition before pruning; no net proof gain is claimed.

## No longer needed

No existing module import is removed: the three public imports are needed by the statements.
The upper theorem no longer uses `split-etale-chart-ring-iso` or `split-etale-chart-functor`
as proof dependencies. The latter declaration is separately reduced as requested; the former
stays present with its original signature for review. Their containing module cannot be
pruned. No blueprint unit statement or realized step is bypassed.

The old direct proof-dependency list is replaced by the three new part nodes plus
`def-weil-affine-spectrum` for the proved faithfulness step. The original geometric
construction dependencies remain below the new nodes, so those modules are not claimed
as globally pruned.

The old direct proof_deps no longer used directly by either updated node are
`def-weil-open-immersion`, `def-weil-residue-field`, `def-weil-geometric-point`,
`def-weil-pbc-relative-separable-closure`, `def-weil-pbc-etale-residue-triples`,
`lem-weil-pbc-etale-composition-cancellation`, `def-weil-pbc-pointed-etale-neighbourhoods`,
and `def-weil-etale-morphism`. They remain needed in statements or the new part nodes;
`def-weil-affine-spectrum` remains a direct dependency. This is direct-dependency pruning,
not removal of their modules from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt only revalidated the already proved upper theorem. It did not
close either hole that this item actually holds and was therefore not a delivery. This attempt
closes the functor-equivalence hole through a compiling reduction following the node's plan.

STATEMENT-DISPUTED: `etale_chart_residue_triples_equivalence_ring_iso` quantifies over every
category equivalence. Its source and proof node describe the equivalence supplied by the
specific construction. A category equivalence need not preserve the ring and point diagrams.
For example take the identity chart over Q and an algebraic closure Ω of Q. A Q-automorphism
σ of Ω acts on triples by replacing φ with σ composed with φ. Compose the canonical chart
equivalence with this autoequivalence. For the non-Galois cubic field B = Q(cube_root(2)),
choose σ moving its real embedding to a nonreal embedding. Any δ satisfying both formulas
would then be a Q-automorphism of B relating these two embeddings, but B has trivial
Q-automorphism group. Thus this arbitrary equivalence cannot have the asserted δ. This is a
mathematical counterexample sketch, not a Lean-certified refutation. We leave that signature
unchanged and remove its use from the upper proof, rather than assuming the disputed claim.

New statement edge cases checked: a zero base ring cannot admit xU from the spectrum of a
field; an empty affine cannot be pointed by Spec Ω; the identity chart reduces the formulas
to affine spectrum duality; and the spectrum of any triple gives the object required for
essential surjectivity. The fullness criterion uses only the displayed formulas and
naturality, and does not silently require image containment for arbitrary objects.

## New nodes

`lem-weil-pbc-etale-chart-functor-construction`, in
`Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesFunctorConstruction`, isolates the object
and morphism assignment and its canonical ring/point formulas (source steps 1 and the
functoriality part of 2).

`lem-weil-pbc-etale-chart-full`, in
`Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesFull`, isolates morphism lifting (source
step 2). Faithfulness is proved in the item itself and is not postponed here.

`lem-weil-pbc-etale-chart-essentially-surjective`, in
`Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEssentiallySurjective`, isolates the
spectrum-of-a-triple construction and object recovery (source step 3).

The source read was the proof of Tag 04HX, label `lemma-describe-etale-local-ring`, and
Remark Tag 04HT, label `remark-etale-neighbourhoods`, in the available Stacks source.
The blueprint search found no duplicate named affine-neighbourhood/triple statement.
LeanFinder and source searches found the affine extensionality API but no completed chart
construction. LeanSearch was unavailable, and Loogle did not recognize the requested
identifier; these are recorded accurately as unavailable in the nodes. No change record
is needed because existing interfaces are unchanged.

## Second reading by H2

1. Compared the delivered item with the repository using diff and the declaration parser.
   All three existing signatures and visibility are unchanged; no definition or target
   statement changed. The new imports of the item are plain proof-only imports. Pass.
2. Compiled all four modules in import order through lcompile.py, without errors or warnings.
   Inspected every proof and searched for forbidden declarations. The only direct holes are
   the unchanged disputed ring-isomorphism theorem and the three reported part theorems.
   A scratch-copy #print axioms check gives only propext, Classical.choice and Quot.sound
   for the private affine faithfulness proof, and those plus sorryAx for the three existing
   public theorems. The delivery probe also checks every delivered declaration. Pass as a
   decomposition, not as a finished axiom-free equivalence proof.
3. Read the three new statements, their source proof descriptions and their matching nodes.
   Construction omits fullness and essential surjectivity; fullness lifts a single morphism;
   essential surjectivity reconstructs a single object. None restates the whole item.
   Checked the identity chart and Spec of a triple; empty/zero-ring neighbourhoods cannot
   have a field-valued point. Naturality of δ fixes the morphism assignment, so the fullness
   and object-recovery criteria legitimately apply to every functor satisfying the formulas.
   Independent grep, LeanFinder and Loogle searches using global-sections/full-faithfulness
   terminology found Spec.fullyFaithful and affine-scheme APIs, but no existing compatible
   chart functor or either criterion. No split could be closed in a few minutes. Pass.
4. Read the assembly from the top down and checked the faithfulness proof against
   ext_of_isAffine. The existing public imports are required by signatures and all three
   new plain imports are used. Checked dag/units/sk-thm-p1.json: this reduction stays below
   the unit's realized statement and steps, which are preserved. No globally pruned module
   is claimed. The legacy ring-isomorphism theorem is disputed and is not used. Pass.
5. Checked each node's proof steps, their uses/proof_deps union, proof_origin, source,
   chapter, unit, creation record, blueprint link and verbatim Lean statement. The two
   updated nodes describe the actual assembly and direct affine faithfulness; the three
   new nodes describe the remaining parts. Pass.

Second-reading repairs: removed the irrelevant converse-faithfulness paragraph from the
new fullness docstring and corrected the essential-surjectivity module heading. Added this
review and the explicit old-dependency accounting below; no Lean proof or interface repair
was needed.

