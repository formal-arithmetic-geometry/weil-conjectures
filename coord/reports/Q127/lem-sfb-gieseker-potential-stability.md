## Worker report

The module `Sheaf.AlgebraicGeometry.GiesekerPotentialStability` states
`AlgebraicGeometry.gieseker_potential_stability`, with exactly one postponed proof,
`sorry`. It defines the conclusion structure and a concrete classification predicate
for the supplied Hilbert point. Neither definition contains postponed data. The item
statement is unchanged; no new DAG nodes or dependency repairs are necessary.

Source read: Ian Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and
Maps*, https://arxiv.org/pdf/0810.2340, printed pp.13--15, Section 3.2 Definition 7,
Theorem 8 and Section 3.3 equation (6). The source's claimed equivalence of numerical
bounds is not used: the node already correctly assumes d > 9(g-1). The complete
fifteen-step DAG proof, including the integral-gap uniformization, is in the theorem
docstring. This is a prerequisite node, not the blueprint unit's own statement.

Clause-by-clause correspondence:

- Integer genus g >= 2 and degree d > 9(g-1) are `g d : ℕ`, `hg` and `hd`.
  The inequalities force both integers to be positive, so natural parameters lose no
  integer case. The number r is written `n + 2`, with `hn : n + 2 = d + 1 - g`.
  Under the hypotheses r >= 9, so every permitted r has this presentation; the
  ambient space is precisely P^(r-1), with r coordinate indices.
- The field-independent M is `∃ M : ℕ` before `∀ (k : Type u) [Field k]
  [IsAlgClosed k]`; `M ≤ m` is the required sufficiently high Hilbert degree.
  A natural bound is equivalent to an integer bound here: Hilbert degrees are
  nonnegative and a negative integer bound can be increased to zero.
- A connected closed subscheme is the universally quantified `C`, its embedding
  `i`, `IsClosedImmersion i`, and `ConnectedSpace C`. The structure morphism `f`
  is fixed by `i ≫ projection = f`; it is not an unrelated field action. No
  projectivity hypothesis is added: projectivity follows from the closed embedding.
- The exact polynomial dm+1-g is the equality on `P.1`; the eventual homogeneous
  coordinate predicate is the recorded `IsCoordinatePolynomial k (n + 1) i P.1`.
  `HilbertPlucker.Coordinates n` has n+2 indices, hence this is the correct
  projective dimension n+1.
- Semistability uses the recorded `HilbertPlucker.Hilbert`, `Presentation`, and its
  semistable open `E.semistable` at the actual k-valued point `x`. The real helper
  `HilbertPointRepresents C i D x` requires an isomorphism of C with the closed
  subscheme of the universal ideal pulled back along x, commuting with the
  embedding. It does not replace the given C by an arbitrary curve. Quantifying
  over presentations and Hilbert representatives is invariant presentation data
  of the dependency's specified linearization, not an extra geometric assumption.
- The conclusion's `reduced` and `pure` fields state `IsReduced C` and
  `C.IsPureDimension 1`. Its `nodal` field tests every nonsmooth point and uses
  exactly `AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) ...`
  and `MvPowerSeries (Fin 2) k / Ideal.span {X 0 * X 1}`. Over an algebraically
  closed field on this reduced curve, these are the singular points. The output
  locally-finite-presentation witness is a consequence of the closed projective
  embedding; it is included only to type the existing smooth-locus API.
- `hyperplane_iso` identifies L with the actual tensor pullback of the recorded
  `ProjectiveSpace.twist ... 1`. `complete_nondegenerate` says the actual linear
  combination of its pulled-back coordinate sections is bijective from k^r to
  Γ(C,L). Thus no linear relation is allowed, and every section belongs to this
  linear system: nondegeneracy and completeness are both explicitly included.
- `h0` is finrank of the recorded `RingedSpace.moduleCohomology ... 0`, restricted
  to k through f, and equals n+2 = r. `h1` is `Subsingleton` of the actual H¹
  module. This is zero cohomology, not the potentially insufficient assertion
  that an arbitrary module has finrank zero.
- `omega` and `dualizing : NodalDualizingDatum f omega` use the existing normalized
  dualizing-line interface publicly imported by nodal-log-canonical-reconstruction.
  With no marking, the dualizing line itself is the requested omega_C. It is
  constrained by the fundamental class and actual local Ext modules, not an
  arbitrary invertible module.
- `component`, `integral`, `inclusion`, `closed`, `distinct`, `exhaustive` enumerate
  all reduced integral component subschemes exactly once. `rational_component_branches`
  uses the recorded `markedNodalComponentGenus` on each canonical normalization
  and counts every preimage of a singular point. This counts two branches at a
  self-node and one on each component at an intersection node. It requires at
  least two whenever the normalized genus is zero.
- `balanced` quantifies every nonempty proper `Finset` of component indices. Its
  lY and wY are sums of the recorded `markedNodalComponentDegree`, which unfolds
  to the recorded `Scheme.Modules.degree` on the component normalization.
  The coefficient d/(2g-2), absolute value, and right side kY/2 are in ℚ.
  kY is exactly the cardinality of the intersection of the two complementary
  component unions. On the concluded nodal curve those are exactly the boundary
  nodes. This covers disconnected subcurves as well as connected ones.
- `rational_two_point_degree` quantifies every smooth component with normalized
  genus zero and exactly two intersections with the other components, and gives
  its normalized hyperplane degree equal to one. Projectivity and algebraic
  closedness identify smooth genus-zero components with smooth rational ones.

Dependencies used (module, declaration):

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic:
  `IsAlgClosed` (available through the public dependencies).
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar:
  `Scheme.Modules.degree`, `Scheme.arithmeticGenus`.
- Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization:
  `HilbertPlucker.Coordinates`, `HilbertPlucker.Hilbert`,
  `HilbertPlucker.Presentation` and its normalized semistable open.
- Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction:
  `exists_nodal_log_canonical_reconstruction`; its public dependency
  Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees:
  `markedNodalComponentDegree`, `markedNodalComponentGenus`; its public dependency
  Sheaf.AlgebraicGeometry.NodalDualizingDatum: `NodalDualizingDatum`.
- Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality:
  `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist:
  `ProjectiveSpace.twist`, `ProjectiveSpace.twistOneSection`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- WeilConjectures.Topology.RingedSpaceModuleCohomology:
  `RingedSpace.moduleCohomology`.
- WeilConjectures.Mathlib.AlgebraicGeometry.Normalization:
  `Scheme.normalization`, `Scheme.fromNormalization`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`, through the existing
  `Scheme.IsPureDimension` predicate from Sheaf.AlgebraicGeometry.PureDimension.
- Mathlib.RingTheory.AdicCompletion.Algebra (and Basic): `AdicCompletion`.
- Mathlib.RingTheory.MvPowerSeries.Basic: `MvPowerSeries`, `MvPowerSeries.X`.

All already stated proof-dependency modules are imported with plain imports,
unless already needed publicly for the statement. Unstated proof prerequisites
(component-projection estimates, singular-point jet estimates, subcurve-span bound,
coherent zero-dimensional support, component interpolation) have no module to import.
No statement-only proof prerequisite was duplicated.

Edge cases checked: g=2 and minimum degree d=10 give r=9; no denominator zero is
possible. Arbitrary characteristic is allowed, including characteristic dividing r:
semistability uses the dependency's full group-scheme construction. The field and
schemes share the established universe u without excluding algebraic closure or
small-site cases. The empty scheme cannot satisfy the connected/nonempty curve
hypothesis or the nonzero linear Hilbert polynomial. There is no subcurve to test
on an irreducible curve; `balanced` is then vacuous as intended. Disconnected
component unions are included. A self-node contributes two normalized branches,
whereas its point contributes nothing to the boundary unless the components are
on opposite sides. The final degree-one clause excludes singular rational
self-nodal components by its explicit smoothness assumption.

Searches for an existing statement:

- msearch.py leanfinder, "Hilbert semistable projective curves have balanced
  normalized component degrees and nodal singularities": eight Weierstrass curve
  results, none an exact match.
- msearch.py loogle, `"Hilbert", "Semistable"`: zero hits.
- msearch.py grep, `Gieseker|potential.*stabil|balanced.*subcurve`: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, Gieseker,
  potential stability and balanced subcurve: the codegree polygon and Clifford
  subcurve prerequisites only; no existing potential-stability declaration.
- tools/blueprint_refs.py search "potential stability": zero blueprint nodes.
  Existing DAG node is this item. No new notion independent of its clauses was
  introduced; helper declarations belong to the owning item.

Validation: scompile.py compiled both the sandbox and final module cleanly under
60 seconds. All binders are explicit (`autoImplicit` and `relaxedAutoImplicit`
are false); definitions have real data; the only theorem has the required sorry.
No STATEMENT-DISPUTED fault or statement correction is needed.

## Second reading by Q127

This is an explicit self-reading, not a claim that a second agent reviewed it:
the dispatch brief prohibits starting other agents and assigns the independent
reading to the maintainer. The node and final Lean file were reopened together.
The first draft was corrected before delivery: it had an existential unrelated
curve, lacked a fixed polynomial equality, omitted coordinate-section
nondegeneracy, and did not constrain boundary count by complementary components.
The final universal C and `HilbertPointRepresents` preserve the same subscheme;
the polynomial equality fixes g,d; the coordinate-section bijection fixes the
complete embedding; normalized-component sums and actual intersection counts fix
the complete inequality. The genus-zero two-point clause now explicitly requires
a smooth component, so a self-nodal rational component is not misclassified.
Each final hypothesis and clause is matched above. No change to the natural-language
node, its dependencies or proof was made. Independent maintainer review remains
the delivery's external check, as required by the dispatched brief.
