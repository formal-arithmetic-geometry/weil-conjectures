## Worker report

This delivery states `AlgebraicGeometry.HilbertCoefficient.exists_regularHilbertCoefficientDatum`
in `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientData`. Its proof is `sorry`, and its
full thirteen-step DAG proof is copied into its docstring. It imports the three Mathlib
modules used by the two already stated Mathlib proof dependencies. The other five
proof-dependency nodes have no Lean declaration in the current DAG and therefore no
module to import. No theorem other than the item's theorem is postponed or introduced.
The module mode header and `set_option autoImplicit false` enforce explicit bindings.

The source read was Bierstone--Milman, *Canonical desingularization in characteristic
zero*, Invent. Math. 128 (1997), pp.261--264 and 278--282: (7.1), all five parts of (7.2),
Theorem 9.6, and Remark 9.9. The final published PDF was read from
https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf .
The arXiv version was also fetched, but its extraction did not preserve the theorem
numbers; the published PDF is the detailed input used here. These reference copies
remain in the sandbox and are not part of the delivery. The statement is unchanged.

Clause-by-clause correspondence:

- Characteristic-zero field: `(k : Type u) [Field k] [CharZero k]`.
- Schemes over that field: `(X M : Scheme.{u})` and
  `[M.Over (Spec (CommRingCat.of k))]`, with the structure morphism passed to the datum.
- Reduced closed subscheme: `(i : X ⟶ M) [IsClosedImmersion i] [IsReduced X]`.
- Smooth finite-type ambient scheme: `[Smooth (M ↘ Spec ...)]`,
  `[LocallyOfFiniteType (M ↘ Spec ...)]`, and `[QuasiCompact (M ↘ Spec ...)]`.
- Any point of X: `(a : X)`, without a closed-point or rational-point hypothesis.
- Étale-local shrinking: the datum's `U`, `affineU`, `e`, `etale_e`, `center`, and
  `center_eq`. The one `U` is shared by all coefficients and all equations.
- Smooth closed coefficient scheme and its point: `N`, `affineN`, `j`, `closed_j`,
  `smoothN`, `b0`, and `b0_eq`. Affineness is a permitted further local shrinking.
- Regular coordinates: `coord`, `etale_coord`, and `over_k` specify the original
  étale coordinates `(w,z)` over k; `etale_w` specifies their restriction w on N.
- Formal coordinates: `taylorU_spec` and `taylorN_spec` use `isTaylorMap`, which fixes
  the residue map, the scalar image, and every coordinate image. Thus these are
  actual Taylor homomorphisms for the étale coordinates, not arbitrary ring maps.
- The formal transverse coordinates of Remark 9.9 are specified by `straight_k`,
  `straight_w`, `straight_z`, and `straight_residue`: the regular z-coordinate maps
  to its implicit Taylor value on N plus the formal transverse variable Z. In
  particular, the construction does not replace Z by the equations cutting out N.
- A finite diagram and ordered vertices: the existential `m n s α`, `orderedVertices α`,
  and `fullVertex m`. The latter inserts zero W components. Minimality is the
  pairwise divisibility-antichain condition; degree-lexicographic ordering is
  Mathlib's `Finsupp.DegLex`. Every transverse variable must occur in a vertex.
  `inDiagram` is the union of the vertex orthants, and `inDelta` excludes exactly
  the orthants of earlier vertices after translation by the current vertex.
- Regular coefficients and the displayed formal series: `coeff` takes values in
  `Γ(N, ⊤)`. The field `expansion` equates each coefficient of `f b l` with the
  W coefficient of the Taylor expansion of `coeff l γ`, splitting the exponent
  by the two injections of the sum of variable sets. This determines the full
  series coefficient by coefficient and has no algebraization assertion.
- The vertex exponents at the distinguished point are certified by `first_coeff`
  and `first_minimal`. They are not required to be an arbitrarily preselected basis.
- The coefficient order locus is the antecedent of `conditions`.
  `center_order` ensures the distinguished point belongs to it. All orders there
  mean germ containment in actual powers of the stalk's local maximal ideal.
- (1) The first conjunct of `formalConditions` states both membership in the Taylor
  ideal and `(f i).order = (α i).degree`. The Taylor ideal is `Ideal.map` of the
  kernel of `(pullback.snd i e).appTop.hom`, so it is the ideal of the given X.
- (2) `homogeneousDivision` quantifies over both the degree-prefix bound q and the
  homogeneous degree t. Its `∃!` is over the entire tuple of quotients and remainder.
  `MvPowerSeries.homogeneousComponent` gives the initial forms. Homogeneous series
  in finitely many variables are polynomials; this is exactly polynomial homogeneous
  division. Active quotients have degree t-d_i and support in Delta_i; inactive
  quotients, including t<d_i, are zero. Remainders are homogeneous of degree t and
  have support outside the prefix diagram. Thus uniqueness has no free inactive terms.
- (3) The third conjunct of `formalConditions` quantifies over every element of the
  actual Taylor ideal, and gives a finite sum with all quotient supports in Delta_i.
- (4) `essential α q` is precisely the variables occurring in the prefix blocks.
  `pick_vertex` gives α_i(j)=beta_j+e_j, and `pick_prefix` chooses the derivative
  from the first block in which its variable occurs. At each attained block degree,
  the fourth conjunct states all the required memberships in `transverseIdeal`
  and that the Jacobian determinant on the corresponding finite subtype is a unit.
  The entries are constant coefficients of the partial derivatives of g_j.
- (5) The final conjunct quantifies over attained block degrees q, later generators,
  and transverse exponents δ with degree ≤Q. It requires δ to be in the prefix
  diagram and supported on its essential variables. The derivative lies in exactly
  the ideal generated by those variables. `iteratedPartial` iterates the existing
  `MvPowerSeries.pderiv`, using ordinary derivatives, not divided derivatives.
- The Q quantifier is `∃ m n s α, ... ∧ ∀ Q, (∀ i, d_i - 1 ≤ Q) → Nonempty ...`.
  The diagram is chosen before Q; charts and normalized generators may depend on Q,
  as in the proof following Theorem 9.6. For a finite nonempty vertex set the bound
  is exactly Q ≥ max d_i - 1; the empty case has no restriction.
- N is cut out by regular equations: `equations_ideal` and `equations_jacobian`
  specify its regular ideal and transverse Jacobian on the same U, while the
  fourth formal condition specifies the Jacobians of the chosen g_j.
- Hilbert--Samuel upper bound on the whole neighbourhood: `hilbert_bound` quantifies
  over every y in U and every degree. `extendedHilbert` is the module length of
  the quotient by the Taylor ideal plus the (q+1)-st power of the variable ideal.
  It keeps all relative variables after passing to κ(y), thus uses the extended
  Taylor-module convention at nonclosed points. The source explicitly orders
  Hilbert functions pointwise (p.220), and the Lean inequality is pointwise.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`, lines 68--70:
  reduced rings of sections, the recorded equivalent form of reduced stalks.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, lines 41--46: closed embedding and surjective stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`, lines 16--26
  and 57--63: affine-locally smooth ring maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, lines 39--46, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`,
  lines 38--46: finite type is their conjunction, as the dependency node records.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`, lines 37--45:
  affine-locally étale ring maps. The coordinates additionally use `RingHom.Etale`
  from `Mathlib.RingTheory.RingHom.Etale`, lines 26--30, the same affine notion.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, lines 84--87:
  the actual coefficient families with the Cauchy-product ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`, `MvPowerSeries.pderiv`, lines 114--135:
  the R-derivation and its coefficient formula. This dependency is a Mathlib leaf
  with no lean record; its mathlib_match is used directly, without a repair.
- The new definition node additionally uses the recorded scheme and residue-field
  declarations `Scheme`, `Scheme.Hom`, `Scheme.residueField`, and
  `Scheme.Hom.residueFieldMap` (the residue-field source was read at lines 40--55).
  It uses `Module.length` from `Mathlib.RingTheory.Length`, lines 29--34, the
  mathlib_match of `def-weil-pbc-module-length` (no lean record needed).
- Proof imports: `Algebra.FiniteType.isNoetherianRing` in `Mathlib.RingTheory.FiniteType`
  lines 187--195; `Module.IsNoetherian.finite` in `Mathlib.RingTheory.Noetherian.Basic`
  lines 125--128; `Module.finitePresentation_of_finite` in
  `Mathlib.Algebra.Module.FinitePresentation` lines 118--121.

Edge cases checked before and during writing:

- Empty X: the theorem has a point a:X, so there is no nonexistent-center obligation.
- X=M locally: choose the empty vertex set, n=0, N=U. The supported expansion then
  says the Taylor ideal is zero, and all block clauses are empty, as required.
- n=0 is allowed. There is no Nonempty/positive-dimension hypothesis on Fin n;
  equations and Jacobians of size zero are allowed (empty determinant equals 1).
- Zero coefficients: every maximal-ideal-power condition holds for their zero germs;
  zero formal series have infinite order under Mathlib's MvPowerSeries.order.
- Homogeneous degree below a generator's degree forces its quotient to zero;
  a missing degree prefix leaves exactly the original polynomial as remainder.
- No division by a multi-index factorial is hidden in iteratedPartial; the field's
  characteristic zero is required by the existence theorem, not added to an input map.
- Nonclosed points are retained. No equality between site universes or any rationality
  assumption appears. Schemes and residue fields have arbitrary common universe u;
  the finite coordinate index sets are small, for every finite number of variables.
- Only finite matrices are inverted in the source proof. The datum keeps all infinitely
  many coefficient functions on one N rather than asking for infinitely many opens.

Searches actually run (full logged JSON is used in the new node's mathlib_searches):

1. msearch leanfinder: `regular coefficient data for formal standard bases Hilbert Samuel
   stratum division Jacobian smooth maximal contact characteristic zero` gave eight
   univariate Weierstrass-division hits, no multivariate geometric coefficient datum.
2. msearch loogle: `MvPowerSeries.pderiv, Ideal.span` gave zero hits.
3. msearch grep: `HilbertSamuel|Taylor|[Ss]tandard[Bb]asis|[Cc]oefficient[Dd]ata`
   in RingTheory gave 17 polynomial-Taylor/Henselian hits, no exact notion.
4. msearch leansearch: `etale Taylor coordinate charts and division adapted regular
   coefficient presentations of Hilbert Samuel strata` gave eight results on
   étale maps/formal étaleness, no packaged datum or existence theorem.
5. rg in lean/WeilConjectures and lean/Sheaf with the same concept patterns found
   unrelated polynomial Taylor and coefficient-system declarations only. The item-id
   search in WeilConjectures found nothing. No existing Taylor/Hilbert chart interface.
6. rg on dag/nodes for Taylor charts/maps, regular coefficient data and unique division
   found this theorem and its analytic statement/proof inputs, not a definition node
   of this notion. `python3 tools/blueprint_refs.py search 'Taylor coefficient'` found
   zero blueprint nodes; `ancestor` returned `lem-trf-local-term-locality`.

No statement correction or disputed assertion is introduced. All definition data are real
ring maps, schemes, sections, series, finite sums or explicit predicates; there is no
`sorry`, theorem-derived arbitrary choice, or placeholder construction in the new datum.
The existential maps in the theorem's conclusion are characterized by the actual étale
coordinate and residue identities, so no arbitrary map is substituted for Taylor expansion.

Validation: both delivered modules compiled independently in dependency order with
scompile.py, in sandbox and library module modes. The definition module compiled without
warnings; the theorem module compiled without errors or non-sorry warnings. The final
delivery dry run also compiles both modules and checks the node records.

## New nodes

`def-trf-regular-hilbert-coefficient-datum` defines the one combined datum required to
state the existence theorem, including its formal predicates and canonical coordinate
identities. It has its own module `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`.
Every helper declaration is listed in lean.declarations, and each has a source and blueprint
docstring. Its self-contained statement specifies the chart and every formal condition;
it asserts no existence theorem and has no proof or proof dependencies. The sources are
BM (7.1)--(7.2), Theorem 9.6 and Remark 9.9. The searches above found no existing DAG,
Mathlib or upstream declaration for this combined notion. Existing schemes, ring maps,
étale/smooth/closed immersion predicates, MvPowerSeries, derivatives, and Module.length
are used directly. The new definition does not introduce a second underlying ring or
geometric notion. Its ancestry is that of the item's regular-coefficient input to the
Hilbert--Samuel local presentation route under `lem-trf-local-term-locality`.

## Second reading by Q80

This is the worker's own final rereading, not an independent agent review. The dispatch
brief prohibits starting other agents and specifies independent maintainer review after
self-delivery. Reading the file against the source and node found three interface details
that needed care: quotient components for inactive vertices must be zero for uniqueness;
the original transverse z-coordinates must be straightened by the implicit Taylor graph,
not replaced by N's regular defining equations; and the Hilbert upper bound must use
pointwise comparison and retain all relative variables at nonclosed points. The final
files contain all three. The finite degree bound is outside the existence of normalized
generators but inside the existence of the fixed diagram, matching the source proof.
No hypothesis, condition (1)--(5), common-neighbourhood requirement, or zero-variable
case is omitted by the final interface. This rereading makes no claim that the theorem's
proof has been formalized.
