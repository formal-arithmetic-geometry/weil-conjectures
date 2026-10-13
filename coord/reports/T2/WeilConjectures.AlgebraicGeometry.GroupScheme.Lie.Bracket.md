## What changed

The assigned Bracket module now proves all four Lie-ring identities from two geometric
coefficient statements, using an explicitly constructed family of additive endomorphisms of
sections. The operator is the epsilon coefficient of the comorphism of right translation of the
universal point of G by the given tangent point. Its construction contains no choice of an
unproved witness and no missing definition data.

New module Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients constructs translation,
proves its zero-section reduction, proves that its inverse-image opens are unchanged, and
constructs the coefficient operators. It proves faithfulness by comparing constant and linear
coefficients of section maps and then restricting along the identity section. It also proves
that the identity point has zero coefficient. Only additivity of these operators under
multiplication of tangent points remains a named theorem with sorry.

New module Sheaf.AlgebraicGeometry.GroupScheme.MixedTranslationCoefficients states the
comparison of a mixed group commutator with the commutator of these explicit operators.
Its statement takes the equality of mixed points as a hypothesis and does not import Bracket,
avoiding an import cycle.

Bracket imports MixedTranslationCoefficients and Mathlib.Tactic.NoncommRing privately.
Its private helpers transport the coefficient map through lieEquiv and prove that it is
injective, additive, zero-preserving, and takes the bracket to the associative commutator.
The four original proofs then use injectivity and associative-ring calculations. All existing
signatures, definitions, instances, visibility and docstrings are unchanged.

Validation: lcompile.py --all compiled all three modules cleanly. The alternating identity uses
AA-AA=0, with no division by two. Construction and proofs impose no nonemptiness, field,
affineness or smoothness hypotheses. The empty scheme causes no exception: all the equalities
are identities of section maps and the recovery argument remains valid. The two residual
coefficient statements have complete sheafwise proof plans and matching nodes.

## Proved and sorry left

Closed all four original holes:

- AlgebraicGeometry.GrpObj.lieBracket_add (lem-ag-lie-bracket-add).
- AlgebraicGeometry.GrpObj.lieBracket_add_right (lem-ag-lie-bracket-add-right).
- AlgebraicGeometry.GrpObj.lieBracket_self (lem-ag-lie-bracket-self).
- AlgebraicGeometry.GrpObj.lieBracket_leibniz (lem-ag-lie-bracket-leibniz).

Added precisely two named holes:

- AlgebraicGeometry.GrpObj.invariantCoefficient_mul
  (lem-ag-invariant-coefficient-add; InvariantCoefficients).
- AlgebraicGeometry.GrpObj.invariantCoefficient_of_mixed_commutator
  (lem-ag-mixed-translation-coefficients; MixedTranslationCoefficients).

No sorry remains in the assigned module. This is a decomposition, not an axiom-free proof of
the Lie-ring identities: four upper holes are closed and two strictly smaller shared geometric
coefficient obligations are added. In particular, the geometric recovery/faithfulness argument,
the identity coefficient, and the algebraic combination of the two obligations are proved.

## No longer needed

No original import is removed, and no original node or module is pruned. The second reading
narrows the new InvariantCoefficients module's public import from Lie.InfPointsEquiv to
Lie.InfPoints, the module its definitions actually require. The original two
proof dependencies (def-sc-group-scheme and def-sc-dual-numbers) remain necessary definitions;
they now support the two new coefficient nodes. No separate construction of the sheaf of
left-invariant derivations or Lie-ring axioms on that sheaf is needed: families of additive
section endomorphisms suffice for all four algebraic identities. The existing unit route is
preserved; dag/units/sk-d-tangent.json has no realized statement or proof step that this
argument bypasses.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original four DAG plans name only group-scheme and
dual-number definitions while asking for nontrivial invariant-extension and mixed-coefficient
arguments. Those two missing interfaces are now explicit, shared statements; their operator
construction, faithfulness, identity coefficient and subsequent ring calculations are already
implemented. The proof needs no global choice of a merely existential invariant vector field.

Searches: Loogle found Derivation.commutator_apply and derivation Lie-ring instances; LeanFinder
found the same algebraic identities and LieDerivation results; grep found manifold invariant
derivations but no scheme coefficient bridge. LeanSearch returned Internal Server Error and is
recorded as unavailable. All search queries and digests are in searches.jsonl. Blueprint searches
for invariant derivation and mixed commutator returned no duplicate blueprint nodes.

## New nodes

lem-ag-invariant-coefficient-add records addition of the explicitly constructed invariant
coefficient operators under multiplication of infinitesimal points. Its module also contains
the completed geometric construction and faithful/zero-preserving realization. This isolates
the first coefficient step of the original proof, without asserting any bracket identity.

lem-ag-mixed-translation-coefficients records the coefficient comparison under a supplied mixed
commutator equality. It concerns explicit right translations and operator composition; it does
not assume or assert the Lie-ring identities. The defining mixedEquiv equality supplies its
hypothesis in Bracket. Both new statements work over arbitrary base schemes.

The four existing Lie-identity nodes have updated proof, proof_deps and proof_origin fields.
No definition or existing statement is changed, so there is no change record or forced adaptation.


## Second reading by T2

1. **Unchanged interfaces — pass.** Read the whole delivered Bracket diff against the
repository and checked every existing declaration's signature byte for byte using the
project declaration parser. None differs; no existing definition, abbreviation, instance,
visibility or docstring changed. The only existing proof bodies replaced are the four
reported Lie identities. Both Sheaf modules are new; no change record is needed.

2. **Kernel proof and construction — pass as a decomposition.** Compiled all three modules
in dependency order with lcompile.py, then recompiled after narrowing the import. No errors
or warnings occurred. Text inspection finds exactly the two reported named theorem sorries,
no missing definition data, and no forbidden declaration or kernel escape. A separate scratch
module prints axioms of both constructions, the reduction and open-preimage theorems, both
split obligations, the faithful-additive theorem and all four original identities: only
propext, Classical.choice, Quot.sound and, for the open obligations and their dependents,
sorryAx occur. The coefficient construction itself and the reduction/preimage proofs have
no sorryAx. The identities are not claimed to be axiom-free while their dependencies remain
open. Right translation and the coefficient family are actual constructions, not witnesses
chosen from an unproved existence theorem.

3. **Split statements — pass.** Read both complete coefficient proof docstrings and their
matching nodes. Checked the unit-point case (zero coefficient), additive/commutative groups
(zero mixed commutator), the empty base (all schemes over it are empty), and characteristic
two (no division). Checked the sign on matrix groups: right multiplication by 1+epsilon X
acts on coordinate functions by the field gX, whose operator commutator is g(XY-YX).
The comorphisms of successive right translations compose in the same product order, giving
the stated positive mixed coefficient. Both statements are strictly geometric parts of the
argument and do not restate any Lie identity. Independent msearch queries used square-zero
sections, tangent coefficients and translation/comorphism terminology, with LeanFinder,
Loogle and grep; local rg searched scheme and Lie files. No existing faithful section-operator
bridge or mixed coefficient comparison was found. Read DiagonalTangentAddition and
DiagonalDerivationCoefficients: these concern coefficients along a given base-point map,
not this explicit universal-translation family. Their use to finish the first geometric
obligation would require further base-change and section-map comparisons, not an immediate
application. Neither residual geometric proof could responsibly be closed in a few minutes.

4. **Top-down route and pruning — pass.** The original holes reduce to injectivity,
additivity, zero and mixed-commutator preservation, then associative endomorphism-ring
identities; there is no circular use of the new LieRing instance. No original module is
pruned: the old group-scheme and dual-number dependencies remain needed transitively through
the new coefficient nodes. The added Bracket imports are private and proof-only. The
InvariantCoefficients import of Lie.InfPointsEquiv was unnecessarily broad; replaced it with
the public Lie.InfPoints import and compiled successfully. The remaining public imports
supply the types or definitions of the new interfaces. Checked sk-d-tangent.json: realized
statement and step lists are empty, and this route bypasses no realized unit step.

5. **DAG correspondence — pass.** Existing node edits affect only proof, proof_deps and
proof_origin. Both new nodes have the required source, complete steps, dependency union,
searches, split status, creation, blueprint, chapter/unit and verbatim Lean statement records.
The four node routes reflect the actual coefficient reduction. Corrected the alternating
node's final step to name the actual rw/sub_self proof rather than noncomm_ring.

Second-reading changes: narrowed one unnecessary new-module import, corrected the
alternating node's tactic description, and documented the checks here. No statement,
definition or proof body was rewritten. Four original holes closed, two named holes added;
this remains a decomposition, with no module pruned.
