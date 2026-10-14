## What changed

Proved `AlgebraicGeometry.Scheme.equivariant_orbit_model` with its signature unchanged.
Reused the complete constructive evaluation-and-extension argument already present in
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct`, omitting its
unused rho-one hypothesis and its unneeded cardinality bound. The proof constructs
orbit representatives and stabilizers, proves that representative evaluation is
bijective, and applies `AlgEquiv.ofBijective`. It uses no unproved theorem.
Updated the existing node's proof and provenance to describe this actual argument.
Removed the geometric-descent proof import. No other modules or interfaces changed.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.equivariant_orbit_model`
(node `lem-sbc-equivariant-orbit-model`). One hole closed, zero holes added;
zero sorries remain in the delivered module. No decomposition or new nodes.
Local single-file compilation passed without warnings. The dry run checks axioms.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric`.
The declarations `AlgebraicGeometry.Scheme.FixedOrbitData`,
`AlgebraicGeometry.Scheme.fixedOrbitData_of_action`, and
`AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric` are not needed here.
Their geometric dependency subtree is unnecessary for this proof; no assertion is
made that other target branches cease to need it. In particular this module does
not need nodes `lem-sbc-affine-torsor-fixed-orbit-data-of-action` and
`lem-sbc-affine-torsor-fixed-puncture-geometric`, or the transitive modules
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction`,
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorOrbitComponentDescent`, and
`Sheaf.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen`.
The sole public import `AffineTorsorEquivariantAlgebra` remains necessary for the
statement and its equalizer characterization. No unit statement or step is bypassed;
`sk-prop-input-spreading` has no realized nodes at this orbit-bookkeeping level.

## Where the brief, the DAG or earlier work was wrong

The earlier one-step node was a placeholder rather than a proof plan. Its exact
constructive proof already exists in `AffineTorsorEquivariantOrbitProduct`.
That theorem's extra rho-one premise prevents direct application to this signature,
but its proof does not use that premise: fixedness under the stabilizer, which
contains the identity, supplies all needed identity equations. Therefore the
statement here is valid even for nonunital multiplicative families of endomorphisms.
The empty component set gives an empty orbit quotient and a product over Fin 0;
trivial permutation actions give singleton orbits with stabilizer G. The construction
also requires no finite-group assumption. Existing signatures stay identical.

## Second reading by B3

1. PASS: diffed the only delivered module against the repository. The existing
   theorem signature and docstring are byte for byte unchanged; the only edits
   are its proof and removal of one proof-only import. No definitions, public
   imports, other interfaces, or change records are added or altered.
2. PASS: independently compiled the file with lcompile.py, with no errors or
   warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.equivariant_orbit_model`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or prohibited declaration or
   attribute occurs. Orbit representatives and transporters are chosen from
   proved quotient properties, never from an unproved existence theorem.
3. PASS: no split-off statements or new nodes. Checked evaluation, transport
   independence, extension equivariance, surjectivity, and injectivity. The
   empty index set, trivial permutation action, and nonunital multiplicative
   rho all work: stabilizer fixedness includes identity fixedness. No finite
   group hypothesis is used or needed.
4. PASS: compared with the existing orbit-product proof and searched again for
   evaluation at orbit representatives and stabilizer fixed points. Mathlib's
   selfEquivSigmaOrbitsQuotientStabilizer gives a set decomposition, not this
   algebra equivalence; the library's orbit-product theorem requires the extra
   rho-one hypothesis, which is unavailable here. The direct reused argument
   avoids that restriction. The sole public import is needed by the statement;
   the geometric proof import is unused and removed. The old proof_deps consists
   solely of def-sbc-affine-torsor-equivariant-algebra, which remains used, so
   there are no old proof-dependency nodes omitted from the pruning report.
   Read dag/units/sk-prop-input-spreading.json: its realized statement and step
   arrays are empty, and this orbit bookkeeping does not replace a unit step.
5. PASS: diffed the node and checked its proof steps against the Lean. Only
   proof, proof_origin, and the permitted unchanged proof_deps are involved;
   proof_deps is the union of uses and correctly names the equalizer-algebra
   definition. The enumeration, transport, and bijectivity steps match the proof.

Second reading changed only this report, recording the independent checks and
clarifying the old proof-dependency pruning accounting. The Lean proof and node
needed no repair. One hole closed, zero holes added, zero split off.
