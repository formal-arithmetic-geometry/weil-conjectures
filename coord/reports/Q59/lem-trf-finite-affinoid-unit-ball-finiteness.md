## Worker report

The module `Sheaf.RingTheory.FiniteAffinoidUnitBallFiniteness` states
`RestrictedSeries.finite_affinoid_unit_ball_finiteness` with one postponed proof.
Its auxiliary real-valued definition `RestrictedSeries.characterSupremum` is the
function rho explicitly introduced by this node itself, not a replacement of any
recorded dependency. It is the actual supremum of the norms of evaluations under
continuous unital K-algebra homomorphisms; it contains no postponed data.

Hypothesis and clause correspondence:

- The field K is `K : Type u` with `NontriviallyNormedField K`; its inherited
  `Field` is the Mathlib match of def-weil-field. `CompleteSpace K`,
  `IsUltrametricDist K`, and `IsAlgClosed K` render completeness,
  nonarchimedeanness and algebraic closedness respectively. The norm is real-valued.
- A and B are `NormedCommRing` types in independent universes v and w, with
  `Algebra K A` and `Algebra K B`. `Nontrivial A` and `Nontrivial B` give A,B != 0.
- `_hA` and `_hB` use the recorded `RestrictedSeries.IsAffinoidQuotient`
  at `algebraMap K A` and `algebraMap K B`. These supply finite-variable Tate
  quotient presentations and completeness with their quotient Gauss norms, hence
  their affinoid Banach topologies. A representative quotient norm is chosen for
  each affinoid topology, as in the recorded dependency; the spectral function and
  continuity conditions depend only on this topology, not on the representative
  norm. No isometry or normed-algebra structure on the given map is assumed.
- Reducedness is exactly `[IsReduced B]`; A is not required to be reduced.
- The character function is `characterSupremum K H h`, whose defining set is
  `{r : R | exists chi : H ->_a[K] K, Continuous chi and r = norm (chi h)}`.
  Here R denotes the real numbers. `AlgHom` preserves the unit and K-scalars.
  Its supremum is finite and nonempty on the nonzero affinoids in this statement;
  the general definition makes no claim about non-affinoid algebras.
- `phi : A ->_a[K] B` and `_hphi : Continuous phi` give the specified map.
  `_hcontract` is the node's pointwise inequality rho_B(phi(a)) <= rho_A(a).
- `_hfinite : phi.Finite` is Mathlib `AlgHom.Finite`, reducing to
  `RingHom.Finite`, namely `Module.Finite A B` for `phi.toRingHom.toAlgebra`.
  The scalar action is therefore the action through phi, not an independent one.
- The conclusion gives `n : N` and `y : Fin n -> B`, each satisfying rho_B <= 1.
  Every b with rho_B(b) <= 1 has coefficients `a : Fin n -> A`, each with
  rho_A(a_i) <= 1, and `b = sum i, phi(a_i) * y_i`. This is exactly finite
  generation over the restricted scalar map. Spectral contraction and the
  ultrametric/product inequalities ensure all these linear combinations lie in
  the target ball. The explicit expansions avoid introducing an additional
  subring or module structure whose closure would need another postponed theorem.

Dependencies read and used:

- def-weil-field: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, inherited
  from the normed-field structure.
- def-trf-restricted-series-presentation:
  `Sheaf.RingTheory.RestrictedSeriesPresentation`,
  `RestrictedSeries.IsAffinoidQuotient` (full declaration and docstring read).
  Its complete quotient-Gauss-norm formulation is used directly.
- def-weil-finitely-generated-module:
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`, via `AlgHom.Finite`.
  Both bridge definitions and the class signature/docstring were read.

All six proof-dependency nodes were read. None currently has a recorded Lean
module, so there are no proof-only imports available to add. The theorem
docstring contains all nine proof steps, with every named analytic input:
character/maximal-ideal comparison, common Tate normalization, minimal-prime
components, fraction-field orthogonal norms, denominator clearing and scaling,
component controlled generators, concatenation, controlled generators on the
inverse image of B, and passage to the unit balls. No proof is supplied in Lean.

Edge cases checked before writing:

- Zero rings are excluded by the node and by the two Nontrivial instances.
- Zero-variable Tate presentations are admitted by IsAffinoidQuotient's n : N.
- Nilpotents in A and a noninjective phi remain allowed.
- The coefficient characteristic is unrestricted, including positive
  characteristic and inseparable normalization extensions.
- b = 0 is covered; the finite family may have length zero, as in the module
  definition, although a nonzero target requires a nonempty generating family.
- The source and target may have different universes; characters are functions
  from H to K, with no independent test-object universe restriction.
- Reducedness of B is essential: K -> K[e]/e^2 has spectral ball
  K^circ + K e and need not be finite over K^circ. The stated hypothesis excludes it.
- The identity K -> K and a reduced quotient map satisfy the intended conclusion;
  no injectivity, surjectivity, or norm equality of phi was introduced.

Searches made:

1. msearch.py leanfinder: "Finite affinoid maps over an algebraically closed
   complete nonarchimedean field with reduced target induce finite maps of
   spectral unit balls". Eight hits, all finite scheme maps; no match.
2. msearch.py loogle: "RingHom.Finite, Module.Finite". One hit,
   `RingHom.finite_algebraMap`, confirming the algebraic finiteness interface.
3. msearch.py grep: "affinoid|spectralUnitBall|power[Bb]ounded". No hits.
4. msearch.py leansearch: "Supremum of norms of values of continuous algebra
   homomorphisms to a complete algebraically closed normed field". Eight hits
   about C-star continuous functional calculus and operator norms; no match.
5. msearch.py loogle: "RingNorm.toNormedCommRing". No hit; no such declaration.
6. msearch.py grep: "character.*[Ss]up|spectral.*[Bb]all|[Ss]pectral.*[Cc]haracter".
   Twelve hits about unrelated characteristic subgroups and documentation.
7. rg over project Sheaf and WeilConjectures for IsAffinoidQuotient,
   spectralUnitBall, characterSupremum, spectralSeminorm, ContinuousAlgHom,
   spectral norm/character patterns, and unit-ball finiteness found only the
   existing quotient-presentation definition and unrelated declarations.
8. The exact node id and proposed declaration names were searched in
   WeilConjectures and the upstream name index; no existing declaration found.
9. DAG character/supremum/spectral searches found the related analytic proof
   nodes, none with a Lean record supplying this theorem or character function.

Source check: opened the primary Conrad Lecture 12 PDF at
https://virtualmath1.stanford.edu/~conrad/Perfseminar/Notes/L12.pdf,
PDF page 2, immediately after Example 12.2.5. It explicitly states finiteness
on power-bounded subrings over an algebraically closed field for reduced target,
and cites BGR 6.4.1 Corollaries 5 and 6. The current blueprint unit and ancestor
were also read. No change to the node statement, dependencies, or proof.
No STATEMENT-DISPUTED flag and no dependency interface repair.

The standalone server compilation and delivery preflight are run through the
prescribed scompile.py and deliver2.py wrappers. The only expected diagnostic
is the theorem's declaration-uses-sorry warning.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
