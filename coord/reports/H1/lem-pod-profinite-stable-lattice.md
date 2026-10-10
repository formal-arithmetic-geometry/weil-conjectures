1. Files written:

- `dag/nodes/sec-poincare-duality/lem-pod-profinite-stable-lattice.json` (statement, split into four proof steps; no Mathlib leaf for the item).
- `dag/nodes/sec-poincare-duality/lem-pod-lattice-stabilizer-open.json` (statement-only helper; no Mathlib match).
- `citations.json` records the verbatim cited statements.

2. Attachments: none.

3. WANTED: none.

4. The source item was not already proved exactly in slopmaster2. `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice` has different hypotheses and conclusion (an existential finite coefficient extension and a specialized Weil-group representation), so it is not an attachment. I searched the DAG and blueprint for the item and helper; no duplicate helper was found. The existing node `lem-sc-dvr-fg-torsionfree-free` is a Mathlib leaf and is cited for the finite-free conclusion.

## Review by H1

I read the item source in Stanford Weil II seminar Lecture 19, Proposition 1.1.9, second bullet, and checked every hypothesis: E is a finite extension of Q_l, O_E is its valuation ring, V is finite-dimensional with its l-adic topology, G is compact, and the action map is continuous. Step 1 uses the new helper exactly for the openness of the stabilizer of the chosen basis lattice, then takes its continuous preimage under rho. Step 2 uses only compactness: the open cosets cover G, so a finite subcover supplies finitely many representatives. Step 3 constructs the finite O_E-span of their translates, verifies finite generation, spanning, and torsion-freeness directly, cites the existing node whose statement is precisely that finite torsion-free modules over a DVR are finite free, and proves stability by writing each product gg_i as g_jh. Applying the same inclusion to g^{-1} gives equality. Step 4 checks continuity by restriction of the given action map and identifies the subspace and m_E-adic topologies on a finite free O_E-module. I tested the construction on the trivial group and on a one-dimensional representation; both give the expected original lattice up to a finite sum of translates. The Mathlib searches for the item and helper were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

5. What could not be finished: no Lean code was written, as required for stage 1.

## Second reading by H1

- Item statement: checked against Stanford Weil II seminar Lecture 19, Proposition 1.1.9, second bullet, pp. 2-3; hypotheses and conclusions agree. Tested on the trivial group, a one-dimensional trivial representation, and dimension zero.
- Helper `lem-pod-lattice-stabilizer-open`: checked against the same proposition, p. 2; its lattice and stabilizer assertion matches. It is statement-only, self-contained, sourced, and has blueprint metadata and recorded searches.
- Step 1: checked the initial lattice and open stabilizer against the helper; added the matrix-entry argument that action continuity gives continuity of `rho` for the compact-open topology.
- Step 2: checked the finite open-coset subcover against compactness in the source; the argument is elementary.
- Step 3: checked finite generation, spanning, torsion-freeness, finite-freeness, and the `gg_i=g_jh` calculation. The finite-free claim is exactly the cited DVR node, and applying the inclusion to `g^{-1}` gives equality.
- Step 4: checked restriction continuity and the topology identification against the source; expanded the latter using the common basis `varpi_E^n O_E^r` of the subspace and m-adic topologies.
- New-node audit: no duplicate or sorry-free Lean declaration was found; the helper satisfies statement-only, self-contained, source, blueprint, and search requirements.
- Changes: expanded Steps 1 and 4 to make the implicit continuity and topology arguments explicit; no statement or citation was weakened.
