## What changed
Replaced the original named sorry in EtaleAffineSingletonTensorAmitsur with a
compiling proof from normalized degree comparisons and their coface equations.
The proof constructs the isomorphism in the Amitsur-to-Cech direction, distributes
composition over the alternating sums, uses preservation of sums and integer
multiples by forget/ULift, and then inverts the resulting complex isomorphism.

Added EtaleAffineSingletonTensorDegreeComparison, containing concrete abbreviations
for the two complexes and cosimplicial objects, a pure-tensor normalization predicate,
and the still-open existence theorem for normalized degree isomorphisms.
Added EtaleAffineSingletonTensorPureCofaces for the still-open equation on a single
pure tensor. Added EtaleAffineSingletonTensorCofaces, whose complete proof extends
that equation to morphism equality by ordinary and indexed tensor induction.
Updated the original node and added the three nodes corresponding to these steps.
All definitions are explicit expressions; no object is chosen from an unproved
mere-existence statement and no definition contains sorry.

## Proved and sorry left
Original hole closed:
- AlgebraicGeometry.Scheme.nonempty_etale_affine_singleton_tensor_amitsur_iso
  (new-etale-affine-singleton-tensor-amitsur).

New theorem proved:
- AlgebraicGeometry.Scheme.singletonTensorDegreeComparison_coface
  (new-etale-affine-singleton-tensor-cofaces), by two tensor inductions.

Holes added and left:
- AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison
  (new-etale-affine-singleton-tensor-degree-comparison).
- AlgebraicGeometry.Scheme.singletonTensorDegreeComparison_pure_coface
  (new-etale-affine-singleton-tensor-pure-cofaces).

This is a decomposition: one original hole closed, two strictly smaller holes
added, net -1. Neither new hole restates the complex isomorphism. The first supplies
terms with a concrete generator normalization, without differential compatibility.
The second proves only the coface equation on one pure tensor for any normalized
comparison, without an affineness hypothesis or construction of isomorphisms.
Their docstrings contain the source and full mathematical arguments. The tensor
inductions and alternating-sum assembly are supplied here in Lean, not assumed.

## No longer needed
Removed direct proof imports from the original module:
- Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
- Sheaf.AlgebraicGeometry.TensorPullback
- WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

Replaced them with the proof-only import of EtaleAffineSingletonTensorCofaces.
The affine-sections and quasi-coherence modules remain planned dependencies of
the new degree-calculation item; TensorPullback is reached through their interface.
The original five proof dependencies are no longer direct dependencies of the
original theorem, and are now reached through the normalized degree-comparison step:
- lem-weil-pbc-module-pullback-quasi-coherent
- lem-pc-module-pullback-identity-composition
- lem-weil-pbc-fibre-product-affine-spectra
- lem-weil-pbc-module-pullback-affine-sections
- def-sc-etale-qcoherent-module

All five remain required by that geometric step. No geometric node or module is claimed
to be globally pruned; none of the unit's route was bypassed.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt moved the entire isomorphism claim to existence of an invertible
morphism. That equivalent restatement remains rejected and is not used.
The node's existing affine-sections theorem does not itself provide indexed
fibre-product section isomorphisms or coface transport: those are the two genuine
geometric steps isolated here. Mathlib provides pullbackSpecIso and its binary
projection equations, productUniqueIso, and tensor induction, but searches found
no direct full singleton comparison or normalized geometric coface equation.
The source was checked at https://stacks.math.columbia.edu/tag/03P2, affine-case
paragraph identifying the singleton Cech complex with the tensor complex, and
https://stacks.math.columbia.edu/tag/03DR for tensor-section restrictions.
Edge cases checked in words: n=0 is the ordinary affine section comparison;
identity g gives the tensor-unit map; empty W gives zero tensor and section groups.
The coface calculation is valid in these cases and needs no surjectivity or
faithful flatness. No signature of any existing theorem changed; no forced
adaptations were made. Exploratory projection unfolding hit expensive definitions;
the delivered files use the compact interfaces and compile below the time limit.

## New nodes
new-etale-affine-singleton-tensor-degree-comparison: normalized degree isomorphisms,
in EtaleAffineSingletonTensorDegreeComparison; includes the explicit normalization
on m tensor tprod(b), with no differential claim.

new-etale-affine-singleton-tensor-pure-cofaces: the normalized geometric coface formula
on one pure tensor, in EtaleAffineSingletonTensorPureCofaces; the source's omitted
factor inserts one, and semilinearity/composition identify the restriction.

new-etale-affine-singleton-tensor-cofaces: proved extension from the pure-tensor
formula to all morphisms, in EtaleAffineSingletonTensorCofaces; ordinary tensor
induction and indexed tensor induction reduce every case to the pure formula.

## Second reading by Q2

1. Compared every delivered module with the repository. Only the Amitsur module
   existed there; its existing theorem signature is byte-for-byte unchanged.
   Its edits are the proof and private proof imports. The other three modules
   are new; no existing definition, public import, target, or statement changed.
2. Compiled all four modules in import order with lcompile.py: clean, each under
   seven seconds. Inspected every declaration and definition. Exactly the two
   reported public named theorems have sorry as their entire proof; there are no
   prohibited declarations, hollow definitions, or choices of arbitrary witnesses.
   A scratch #print axioms check on all four theorems and all five definitions
   returned only propext, Classical.choice, Quot.sound, and sorryAx where open
   dependencies remain. The original theorem is conditionally assembled, not
   independently axiom-free; this delivery remains a decomposition, net -1 hole.
3. Read the two split statements, their nodes and docstring arguments against
   Stacks 03P2 and the section functor of 03DR. The normalization is exactly the
   product of projection functions times normalized coefficient restriction.
   Degree zero is M tensor B, identity maps give tensor-unit comparisons, and
   empty W gives zero section groups; no faithful-flatness assumption is needed.
   The pure-coface equation assumes normalization and needs no affineness: restriction
   semilinearity, composition, and retained projection equations prove it on each
   pure generator. Both are true, needed, and strictly parts of the argument.
   Independent LeanFinder, Loogle and Mathlib grep searches with different queries,
   plus rg on both library roots, found useful affine pullback and Amitsur primitives
   but no existing normalized degree comparison or geometric coface equation.
   Neither remaining geometric hole is a few-minute closure using these interfaces.
4. Read the assembly from the original theorem downward. The two tensor inductions
   genuinely supply morphism equality; the original proof sums the equations with
   the correct signs and inverts the component isomorphism. Imports of the original
   module and coface extension are needed by their signatures or proofs. The degree
   module retains the affine sections and quasi-coherence proof-plan imports for its
   open geometric theorem. Every former direct proof dependency is now explicitly
   listed above; none is globally pruned. Read dag/units/sk-prop-h2.json: its realized
   statement and step lists are empty, so this item bypasses no realized unit step.
   The existing affine-section and composition route is retained in the new node.
5. Compared all four node records with the Lean declarations, normalization and
   proof steps. Existing node changes are restricted to the permitted proof fields.
   The new nodes supply source, docstring proofs, searches, creation/ancestry records,
   chapter/unit and verbatim Lean statements. Their proof_deps are the unions of
   the cited steps; the coface extension cites the pure formula, and the assembly
   cites the degree and coface steps. Verdict: consistent.

Changes by the second reader: corrected the pure-coface docstring's equation number
from 35.8.1 to the project server, explicitly listed all five former direct proof dependencies
under No longer needed, and added this review and its validation evidence. No proof
or mathematical statement needed repair.
