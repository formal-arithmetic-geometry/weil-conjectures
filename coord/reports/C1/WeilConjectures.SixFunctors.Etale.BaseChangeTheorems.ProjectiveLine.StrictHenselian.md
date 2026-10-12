## What changed

Reduced two of the three original open declarations, without changing any existing
signature or definition. All edits are confined to this sandbox.

`AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`
now derives the closed-immersion instance from the cartesian quotient square, restricts
J to each affine open using the existing etale restriction theorem, and applies an
affine acyclicity lemma followed by a finite-cover bound. These are separate parts
of Stacks 0A51: the affine henselization argument and the Mayer-Vietoris induction.
The latter makes no injectivity or torsion assumption and applies to an arbitrary i
once its affine-local vanishing hypothesis is supplied.

`AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`
now establishes qcqs instances, uses the existing proper henselian degree-zero
comparison and projective-line injective acyclicity for each prime, and applies
prime-torsion devissage. The remaining resolution argument is isolated as a general
criterion for any scheme morphism, with explicit degree-zero and injective-acyclicity
hypotheses. The existing torsion filtered-union theorem converts the module sheaf's
stalkwise torsion hypothesis to the condition used by the devissage theorem.

Added three proof-only imports for the new modules, and proof-only imports of
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`,
`Sheaf.AlgebraicGeometry.PullbackIsoPrimeTorsionDevissage`, and
`Sheaf.AlgebraicGeometry.TorsionFilteredUnion`.

The two corresponding existing DAG nodes now follow these proofs. The unit's
realized statements and route are preserved. The four Lean files compile together
without warnings using the prescribed launcher.

## Proved and sorry left

Two of the three original sorries have complete Lean proofs from named dependencies:

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`
  (lemma-weil-pbc-injective-restriction-acyclicity).
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`
  (prop-weil-pbc-p1-strict-henselian-comparison).

The one original sorry left is
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`
(prop-weil-pbc-strict-local-exchange), unchanged. Its missing canonical derived
stalk-to-Ext edge comparison has not been replaced with arbitrary isomorphisms.

The delivery introduces exactly three public theorem sorries, each the whole proof
in a separate module, with its full natural-language argument and node:

- `AlgebraicGeometry.Etale.subsingleton_H_affine_closed_of_injective`
  (lem-weil-pbc-affine-closed-injective-acyclic), in
  `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic`.
- `AlgebraicGeometry.Etale.subsingleton_H_of_affine_local_acyclic`
  (lem-weil-pbc-finite-affine-cover-restriction-bound), in
  `Sheaf.AlgebraicGeometry.FiniteAffineCoverRestrictionBound`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_prime_injective_acyclic`
  (lem-weil-pbc-prime-injective-cohomology-comparison), in
  `Sheaf.AlgebraicGeometry.PrimeInjectiveCohomologyComparison`.

The existing complete proofs of the H1 representation, closed-fibre injective
acyclicity, and strict-local stalk isomorphism are retained and compile.
These reductions still depend on recorded theorem sorries; they do not close the
transitive axiom closure of proper base change.

## No longer needed

No original import, node, or module is pruned. The lower dependencies of the original
plans are needed by the three isolated arguments, or are retained by the unit's route.
Removed the unused TorsionSheaf import from the new finite-cover module: its
statement only needs the upper-star and cohomology API. No other unused import was
introduced. Neither target closure nor all downstream imports have been claimed
pruned merely because dependencies moved below a new lemma.

## Where the brief, the DAG or earlier work was wrong

The prior attempt compiled a module in which all three original declarations still
contained sorry. Its delivery rejection was correct, not a tool failure. This repair
writes actual combining proofs for two of those declarations.

The stated Mayer-Vietoris dependency is expressed using derived global sections,
whereas the requested bound uses Sheaf.H. The new finite-cover lemma includes the
needed transport in its proof specification. The old comparison plan similarly
needs an acyclic module-resolution comparison with the canonical Ext pullback; the
new prime-injective criterion states that missing general comparison explicitly.

Checked edge cases: n=0, empty and repeated affine cover members, the empty closed
subscheme, arbitrary i for the finite-cover bound, the zero sheaf, and q=0 for the
prime criterion. No statement change or counterexample was found. Acyclicity of an
injective module sheaf after forgetting coefficients uses Stacks 03FD; it does not
assert that forgetting an F_r-module sheaf preserves injectivity as an abelian sheaf.

Mathlib searches: LeanFinder returned basic Mayer-Vietoris sheaf-condition results,
Loogle returned the basic Sheaf.H API, and grep found no matching restriction or
comparison theorem. LeanSearch was attempted but its service returned Internal Server
Error; this unavailability is recorded, with no absence verdict inferred from it.
The original Stacks arguments were read at Tags 0A51 and 095T.

## New nodes

`lem-weil-pbc-affine-closed-injective-acyclic` isolates the affine case (n=0) of
lemma-weil-pbc-injective-restriction-acyclicity. It follows pair henselization,
Gabber comparison and etale cohomology continuity. Torsion of J suffices for Gabber,
so the coefficient ring itself need not be torsion. The result is local, with no
finite-cover conclusion.

`lem-weil-pbc-finite-affine-cover-restriction-bound` isolates the cover induction
from that same node. It assumes affine-local acyclicity for an arbitrary module
sheaf and derives the bound by Mayer-Vietoris; it proves no local acyclicity.

`lem-weil-pbc-prime-injective-cohomology-comparison` isolates steps (c)--(d) of
prop-weil-pbc-p1-strict-henselian-comparison. It constructs the canonical comparison
for sheaves killed by one prime from explicit degree-zero and restricted-injective
acyclicity hypotheses on any morphism. The original proof supplies these hypotheses
from two other library results and then applies torsion devissage. It has no proper,
henselian, or projective-line hypotheses or torsion-sheaf conclusion.

No change record is needed: no existing public statement or definition changed, and
all added imports in the item's module are proof-only.

## Second reading by C1

1. Existing declarations were compared with the repository version; all signatures
and definitions are byte-for-byte unchanged. Verdict: pass.
2. All four delivered modules compile with the prescribed launcher. The three new
helper theorems are the only added `sorry`s, each documented and represented by a
split node; the item retains its one documented open theorem. Verdict: pass.
3. The three split-off statements are proper affine-local, finite-cover, and
prime-module comparison reductions, each strictly weaker than the item and sourced
to Stacks 0A51/095T. Searches found no existing duplicate. Verdict: pass.
4. Proofs use the shortest available recorded reductions and preserve the unit route;
unused imports were checked and the finite-cover module has no redundant
TorsionSheaf import. Verdict: pass.
5. The changed node proof, proof dependencies, origins, and the three new nodes
match the Lean declarations and proofs. Verdict: pass.

I changed only this report section after reading: no Lean code, statements, DAG
proof routes, or imports required repair.
