## What changed

Repaired reviewer X-db33c point 4. Removed the false assertion that the dual of the zero
morphism is invertible and removed the target proof's `⟨0, ...⟩`.

`Sheaf.RingTheory.SelfTorConormalComparison` defines the actual algebraic comparison by its
Koszul normalization: on a conormal wedge it is the class of the corresponding Koszul cycle
in any projective resolution of the quotient. A named existence-and-uniqueness theorem
specifies this map. The definition selects a uniquely determined morphism, rather than an
arbitrary witness of existence. Its normalization is proved from that theorem.

`Sheaf.RingTheory.SelfTorConormalRegularIso` isolates the regular-quotient calculation for
this specific map. `Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` now constructs the
global comparison with affine coordinate factorizations through this normalized algebraic
map, without any regularity assumption. Its functor uses the actual tilde, open pushforward,
tensor pullback, dual, restriction, and over-site constructions.

The original target theorem has exactly its original signature and public imports. Its
complete proof obtains that global morphism, uses the regular-chart generators to establish
invertibility of the algebraic map, rewrites by the chart factorization, and applies
preservation of isomorphisms under functors and composition. Added proof imports are
`SelfTorConormalDualChartIso` and `SelfTorConormalRegularIso`. No existing consumer or target
statement was changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.selfTor_conormal_dual_chart`. This is a
three-part decomposition, not an unconditional completed mathematical proof.

The three remaining named holes are:

- `AlgebraicGeometry.existsUnique_selfTor_conormal_comparison`, node
  `new-r4-self-tor-conormal-comparison`: construction and uniqueness of the normalized map.
- `AlgebraicGeometry.selfTorConormalComparison_isIso`, node
  `new-r4-self-tor-conormal-regular-iso`: the algebraic regular-quotient calculation.
- `AlgebraicGeometry.selfTor_conormal_dual_chart_iso`, node
  `new-r4-self-tor-conormal-dual-chart-iso`: globalization and the chart coordinate equation.

`AlgebraicGeometry.selfTorConormalComparison_spec` is proved. All definitions have complete
bodies without holes. The only selection from an unproved theorem uses an existence-and-
uniqueness statement determining the selected morphism by its values on generating wedges.
All four modules compile together via `lcompile.py --all`.

## No longer needed

No original module or DAG dependency is claimed pruned: the conormal, resolution, and gluing
parts of the original plan remain necessary through the three new nodes. The previous false
zero-map assertion is replaced, not counted as pruning or as a proved hole.

The earlier new chart module's `Sheaf.RingTheory.KoszulRegularSequence` import is removed:
its repaired factorization holds on all affine charts, and regularity is now used solely
by `SelfTorConormalRegularIso`. The target's original public import remains necessary for
its statement. No original public import was removed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery asserted invertibility for the dual of a zero comparison. Marking it
`STATEMENT-DISPUTED` did not make it an acceptable reduction. For the identity closed
immersion of a nonzero field spectrum in degree zero, both objects are the unit sheaf and
the zero map is not invertible. Quantifying over arbitrary comparison morphisms has the
same defect. Both assertions are gone.

The repaired algebraic construction fixes the map by Koszul cycle classes. The chart
factorization concerns that map, and only its regular-quotient theorem asserts
invertibility. The degree-zero normalization is the quotient unit; for zero quotients all
modules are zero. The zero ideal and empty generating sequence are included. Above the
regular sequence length both exterior power and Tor vanish. Characteristic two is covered
by strictly commutative Tor products, rather than merely signed commutativity.

The source unit's statement and route are unchanged. The original target node's proof,
proof dependencies, and proof origin have been updated to the compiled decomposition.

## New nodes

`new-r4-self-tor-conormal-comparison` records the unique Koszul-normalized algebraic map,
its explicit normalization predicate, the ambient-ring exterior module, the uniquely
specified definition, and its proved specification. It carries no chart isomorphism claim.

`new-r4-self-tor-conormal-regular-iso` records invertibility of that particular algebraic map
for a Koszul-regular quotient, using the existing Koszul projective-resolution and conormal
basis nodes. This is a ring-theoretic assertion independent of any scheme or chart gluing.

`new-r4-self-tor-conormal-dual-chart-iso` replaces the returned new node with globalization
of the normalized map and its coordinate factorization. It assumes no regularity and
makes no invertibility assertion about an arbitrary morphism. The target combines it with
the separate regular-quotient calculation by actual Lean rewriting and functoriality.

All three new nodes record the searches run for this repair. LeanSearch returned an
internal server error; LeanFinder and local Mathlib searches found no exact comparison.
No existing library interface changes or forced adaptations require a change record.

## Second reading by R4

1. I compared the delivered target module with the repository version. Its theorem
   signature and all existing declaration signatures are unchanged; only the target proof
   and two private proof imports were added. The three additional modules are new modules
   corresponding to the three split nodes, and no unrelated source file is modified.

2. I compiled all four delivered modules together with
   `python3 /home/ubuntu/weil-launcher/lcompile.py --all`; compilation succeeds without
   errors or warnings. The target proof closes the original sorry. The three remaining
   sorries occur only as whole proofs of the named public split theorems, with matching
   node records and complete source-based proof descriptions. No definition contains a
   sorry, and no axiom, unsafe, opaque, extern, implemented_by, or sorryAx declaration was
   introduced. The resulting proof uses only the permitted foundational axioms apart from
   the explicitly open split theorems.

3. I checked the new statements against the stated Stacks tags and the edge cases named
   in their docstrings. The comparison is uniquely fixed by its normalization; the
   regular-quotient theorem asserts invertibility only for that canonical comparison; and
   the chart theorem asserts factorization without smuggling in regularity. The zero ideal,
   empty sequence, degree zero, zero quotient, and degrees above the sequence length are
   covered by the stated constructions. None of these declarations duplicates an existing
   Mathlib or library result according to the recorded searches.

4. I checked the proof route and pruning. The target obtains the global chart map, applies
   the regular affine comparison theorem, rewrites by the coordinate factorization, and
   uses functorial preservation of isomorphisms. The unit route through the global map and
   regular affine calculation is retained. The target's original public imports remain
   needed; the new imports are private proof imports. No old proof dependency is removed.

5. I checked the DAG records and unit linkage. The target node's proof, proof dependencies,
   and proof origin match the Lean proof, and each new node records its statement, source,
   proof steps, searches, Lean declaration, chapter, and unit. The unit's realized route is
   unchanged. I corrected the report only by adding this second-reading record; no Lean
   statement or definition required repair.
