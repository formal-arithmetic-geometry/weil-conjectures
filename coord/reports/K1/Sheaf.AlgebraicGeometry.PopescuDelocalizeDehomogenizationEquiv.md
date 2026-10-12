## What changed

Proved `Algebra.popescu_delocalize_dehomogenization_equiv_exists` in
`lean/Sheaf/AlgebraicGeometry/PopescuDelocalizeDehomogenizationEquiv.lean`, with its
signature, visibility, docstring and three public imports unchanged. No other
library module is changed.

Four proved private helpers handle the finite-support homogenization identity,
construction of an algebra map from a localized quotient, its value on the
canonical polynomial images, and extensionality for such maps. The main proof
constructs the substitutions explicitly: the last m variables are multiplied
by w in the forward direction and by the inverse of the unit w in the reverse
direction. The coefficient membership hypothesis kills the g relations after
unit cancellation; the support identity kills the homogenized relations in
one direction and the original f relations in the other. Quotient and
localization universal properties extend both maps. Their composites fix every
polynomial generator, so extensionality gives the algebra equivalence.

This is the node's four-step route, implemented directly from Mathlib. No DAG
route change, new module, new node, interface change or forced adaptation is
needed. The unit route is preserved. The source read was the final isomorphism
in the proof of Stacks Tag 07F9, including the preceding partial-homogenization
calculation: https://stacks.math.columbia.edu/tag/07F9 .

Searches run through msearch.py: LeanFinder for equivalences of localized
polynomial quotients by variable scaling; Loogle for `IsLocalization.Away,
AlgHom`; grep for `algHom_ext|liftAlgHom|aeval_X`. Their hits provide universal
properties, not this equivalence. Also searched the source and statement roots
for homogenization/dehomogenization. The existing homogeneous-localization
results concern the degree-zero part of a different construction and do not
replace this argument.

## Proved and sorry left

Closed the one original hole:
`Algebra.popescu_delocalize_dehomogenization_equiv_exists`
(node `lem-weil-pbc-popescu-delocalize-dehomogenization-equiv`).

All four private helpers are proved. No sorry remains in the item and no hole
is added elsewhere: 1 hole closed, 0 added, 0 split off. This is a complete
proof, not a decomposition into further unproved statements.

The single-file compile through lcompile.py succeeded without warnings. The
proof makes no nonzero-ring or positive-cardinality assumptions: zero
localizations and n=0, m=0, c=0 or t=0 are included. Units used in the proof
have fixed values, obtained from proved invertibility of those values; no
arbitrary data is chosen from an unproved existence theorem.

## No longer needed

None. No import was removed and no planned dependency was bypassed. The
polynomial-ring and localization definitions and the localization universal
property are all used through the original Mathlib imports. No additional
Sheaf proof-dependency module is required; the universal-property node already
records the Mathlib declarations used here.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The planned final equivalence is
proved exactly as stated, without a Jacobian hypothesis. The named local
literature file was absent on this machine, so the Stacks Tag 07F9 source was
read online. No repository file or project tool was edited manually.

## Second reading by K1

1. Interface preservation: PASS. Read the full repository/sandbox diff and
   compared the existing theorem signature byte for byte with a script. Its
   signature, visibility, docstring and imports are identical. Only four private
   helpers and the proof body are added. No definition used by the statement is
   changed; no change record or forced adaptation is needed.
2. Proof validity: PASS. Independently compiled the delivered module through
   lcompile.py, without errors or warnings (11.3 seconds). Compiled a scratch
   copy printing the axioms of the main theorem and each private helper: all
   five depend only on propext, Classical.choice and Quot.sound. There is no
   sorry or forbidden declaration. Read both substitutions, relation-killing
   arguments, lifts, and inverse calculations. The units have specified values
   obtained from proved IsUnit facts; the private lift is an actual construction.
3. Split statements: PASS, vacuous. No statement is split off and no new public
   statement or hole is added. The finite-support helper is proved directly,
   including the exact exponent equality from hdegree. Checked empty variable
   sets and relation sets, zero polynomials, d=0, and zero localizations: no
   nontriviality or positivity assumption is used, and unit cancellation works
   in the zero ring as well.
4. Route and pruning: PASS. Read Stacks Tag 07F9 and the unit record
   dag/units/sk-thm-p1.json, including realized. The proof implements the node's
   four-step route below the unit level, with no bypass. Independently searched
   Loogle for `MvPolynomial, AlgEquiv` and searched Mathlib, upstream and Sheaf
   for scaling and homogenization results. Renaming equivalences do not perform
   this unit scaling; the upstream homogeneous-localization equivalence concerns
   its degree-zero part and does not replace these quotient maps. No shorter
   exact theorem was found. All three imports support the signature: Rename
   supplies rename, Away.Basic supplies localization ring/algebra structures,
   and Quotient.Operations supplies the quotient Algebra instance used in the
   equivalence type. No import is only for a proof. No old proof dependency is
   unused, so `No longer needed: None` is complete.
5. DAG agreement: PASS. Read the item node and all three proof-dependency nodes.
   The support expansion, explicit maps, localization extension and inverse
   identities agree with proof, proof_deps and proof_origin as already recorded.
   Polynomial evaluation/extensionality and localization universal properties
   use the recorded Mathlib matches. No node edit or new node is needed. No
   applicable record in coord/changes names this module or theorem.

Second reading changed only this report, adding the independent checks and
verdicts. The reviewed Lean proof is retained unchanged. Net holes closed: 1;
holes added: 0; split off: 0; pruned: none.
