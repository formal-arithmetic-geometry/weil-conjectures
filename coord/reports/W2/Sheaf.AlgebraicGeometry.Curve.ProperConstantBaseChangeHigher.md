## What changed

Proved `AlgebraicGeometry.IsCurve.proper_constant_base_change_higher` in
`Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher`, preserving its signature,
visibility, existing public imports and docstring. Added seven proof-only imports and three
proved private helpers: `constant_killed`, `forget_killed`, and `standard_prime_comparison`.

Split on `(r : k) = 0`. In characteristic r, degree-two Artin–Schreier vanishing and
cohomological dimension make both cohomology groups zero. The proof explicitly transports
constant coefficients through forgetting modules and inverse image. In the complementary
case, existing injective-resolution comparison proves the standard base-change map bijective;
the cohomology restriction square transports it to the specified cartesian square.

The node copy records these steps and their dependencies. No definitions or public interfaces
changed. The unit's curve-calculation route is preserved: this proves the higher-degree part of
C₇ and uses neither the enclosing SmoothCalculations theorem nor either field-invariance target.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.IsCurve.proper_constant_base_change_higher`
(node `lemma-weil-pbc-smooth-curve-proper-base-change-higher`).

The item contains no remaining `sorry`. Added zero holes and zero new nodes. All three private
helpers are proved. This is a proof from existing library statements, not a new decomposition;
imported statements, in particular injective acyclicity, may still depend on existing holes.

The module compiled successfully with lcompile.py. The proof handles q = 2 and q ≥ 3 separately,
allows zero-dimensional connected curves, and does not assume finiteness of Λ/rΛ. If Λ/rΛ is
zero, the same killed-sheaf and vanishing arguments still apply. Characteristic zero falls in
the invertible-prime branch. Identity field extensions and arbitrary pullback representatives
are handled by the comparison square, without changing the map in the conclusion.

## No longer needed

The second reader removed the redundant proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`: it is already publicly
exported through `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`.
The original module had no proof-dependency imports and the original node had no
proof dependencies to remove. Every retained proof import is used. No module is claimed globally
pruned. The proof does not require any new proper-degree or Picard-coordinate statement.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof was a one-line placeholder (“apply the corresponding intermediate
theorem”), with no intermediate theorem or dependency named. It did not specify a usable
proof plan. The delivery replaces it with the actual characteristic split and transport.

The cohomological-dimension node currently records a derived-cohomology declaration, while
its `lean_candidates` explicitly records the existing Ext-cohomology theorem
`IsCurve.subsingleton_sheafH_of_three_le` used here. The proof step names that exact theorem
and its source module rather than importing the enclosing SmoothCalculations module, which
would create an import cycle.


## Second reading by W2

1. Signature and visibility: PASS. Diffed the sole delivered module and node against the
   repository. The existing theorem signature is byte for byte identical, as are its
   docstring and four public imports. Only proof bodies, private proved helpers, proof-only
   imports and the node's proof/proof_deps/proof_origin differ. No definition, statement,
   change record or adapted module is introduced.
2. Proof and trust: PASS. The module compiled locally without warnings. A scratch copy with
   `#print axioms` for all four declarations showed only `propext`, `Classical.choice`,
   `Quot.sound` for `constant_killed` and `forget_killed`, and additionally `sorryAx` for
   `standard_prime_comparison` and `proper_constant_base_change_higher` through existing
   imported open theorems. No delivered declaration contains `sorry`, and no forbidden
   trust escape or hollow definition is present. The actual cohomology map is retained:
   constant-sheaf isomorphisms transport vanishing in characteristic r; the commuting
   restriction square transports bijectivity in the complementary case.
3. Split statements and edge cases: PASS. No split-off statements or new holes exist.
   Read the three proved private helpers: quotient annihilation holds also for r = 0
   and the zero quotient; forgetting modules preserves the identity sectionwise; the
   standard comparison has the necessary prime and nonzero-characteristic hypotheses.
   For the main proof, checked q = 2, q >= 3, characteristic zero, characteristic r,
   zero coefficient ring, zero-dimensional connected curves, identity extensions and
   arbitrary isomorphic pullback representatives. None needs an added hypothesis or
   an arbitrary object chosen from an unproved existence theorem.
4. Shortest route, imports and unit: PASS after pruning one redundant import. Repeated
   LeanFinder search using scalar-extension/inverse-image terminology, Loogle search for
   bijections between subsingletons, and repository searches for constant-coefficient
   annihilation and field-extension comparison. No shorter substantive theorem was found.
   The elementary subsingleton arguments are already direct. The duplicate elementary
   annihilation fact in SmoothCalculations cannot be imported because that enclosing
   module imports this item. All retained proof imports supply used declarations and
   remain plain imports. The old node had no proof_deps, so no old dependency was omitted
   from No longer needed. Read dag/units/sk-thm-p1.json and its realized steps: this item
   stays below the curve-calculation step (the higher-degree part of C7); it does not
   bypass the enclosing unit or invoke its field-invariance targets. No globally pruned
   module or node is claimed.
5. DAG agreement: PASS. The proof steps match the characteristic split, base-change
   curve structure, constant-sheaf and cohomology transport, and injective comparison
   as written. proof_deps is exactly the union of step uses, and proof_origin describes
   the route. Checked every dependency's Lean record. For cohomological dimension the
   step explicitly names the used upstream Ext-cohomology declaration, while the node's
   lean_candidates records that declaration alongside its derived form. The topological
   invariance dependency supplies bijectivity for the identity and pullback isomorphism.
   No new nodes need validation.

Second reading changed only the redundant Geometrically.Connected proof import and this
report (including the retained import count and No longer needed). The proof and node
were otherwise left intact. Closed one existing hole and added zero holes; the theorem
still depends on existing open library proofs and is not claimed axiom-free overall.
