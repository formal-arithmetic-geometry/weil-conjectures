## Worker report

The module `Sheaf.AlgebraicGeometry.SmallDegreeDivisorSections` states
`AlgebraicGeometry.Scheme.smallDegreeDivisor_sections`. Its sole theorem has proof
`sorry`; there are no new definitions, proof obligations, or dependency repairs.
The node is unchanged except for `lean`.

Source read: Milne, Abelian Varieties, Chapter III, printed pp.92–93 (PDF pages
98–99), proof of Proposition 2.3, and printed pp.101–102 (PDF pages 107–108),
Lemma 5.2(a),(b) and proof. The former excludes distinct linearly equivalent
points in positive genus; the latter repeatedly decreases h1 from g to g-r and
uses Riemann–Roch. The node asks for existence of a divisor, rather than a
parameter-space open. Its accepted five-step proof is carried into the docstring.

Hypotheses and conclusions, checked against the node and file:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The curve and its specified k-structure are `{C : Scheme.{u}}` and
  `f : C ⟶ Spec (.of k)`. `[IsConnectedCurve f]` includes separatedness, local
  finite type, quasi-compactness, connectedness/nonemptiness and dimension exactly
  one; `[Smooth f]` is smoothness. `[IsHProjective f]` is exactly the recorded
  finite-projective-space embedding convention. Properness, regularity,
  integrality, or a chosen rational point have not been added as assumptions.
- `(g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)` gives the stated positive genus.
  The recorded `Scheme.Hom.genus` is dimension of global differentials; its
  docstring and `Scheme.genus_eq_arithmeticGenus` identify it with h1(O) on the
  smooth proper curves here, exactly the equivalence allowed in def-sc-genus.
- A rational point is precisely
  `Q : {q : Spec (.of k) ⟶ C // q ≫ f = 𝟙 _}`. The first conjunct quantifies
  over every such Q. `pointEquivClosedPoint f Q` is its underlying closed point,
  and `Finsupp.single (pointEquivClosedPoint f Q) 1 : C.Divisor` is [Q].
- Every occurrence of O(D) is the dependency's
  `Divisor.moduleOfSmoothConnectedCurve k C f D`, the actual module of rational
  functions satisfying the divisor's valuation inequalities, including at zero.
- Each h0 is `Module.finrank k` of the object obtained by
  `RingedSpace.moduleCohomology C.toRingedSpace 0` followed by
  `ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom`.
  This uses exactly the recorded module cohomology, with the k-action induced
  by f on global functions. No abelian-sheaf cohomology comparison is assumed.
- The second conjunct quantifies `∀ r : ℤ, 0 ≤ r → r ≤ (g : ℤ) → ...`, retaining
  the node's integer range. Its existential divisor has nonnegative coefficients
  (`∀ P : closedPoints C, 0 ≤ D P`), degree `Divisor.degree C D = r`, and h0=1.
- The third conjunct asserts h0(O(0))=1 for the actual zero of C.Divisor. Since
  its coefficients and degree are zero by their definitions, it gives exactly
  the explicit degree-zero witness in the final sentence of the node.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, commutative ring with multiplicative
  inverses for nonzero elements (lines 170–180).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, polynomial splitting
  (lines 58–64), equivalent to existence of roots (following declarations).
- WeilConjectures.AlgebraicGeometry.Curve: `IsCurve`, `IsConnectedCurve`, and
  `Scheme.Hom.genus` (full signatures and docstrings, lines 65–143).
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`
  (lines 30–43), finite coordinate type and closed projective-space embedding.
- Sheaf.AlgebraicGeometry.DivisorModule:
  `Scheme.Divisor.moduleOfSmoothConnectedCurve` (lines 285–300); its full
  construction `associatedModule`, `sectionModule`, `sectionCondition` was read.
  Its upstream import WeilConjectures.AlgebraicGeometry.Curve.Divisor supplies
  `Scheme.Divisor` and `Scheme.Divisor.degree`, the finitely supported integer
  functions and coefficient sum (lines 57–79).
- WeilConjectures.AlgebraicGeometry.PQFCohomology:
  `sheafCohomologyAndHigherDirectImages` (full docstring and signature), recording
  `RingedSpace.moduleCohomology`. The latter's definition and docstring were read
  in WeilConjectures.Topology.RingedSpaceModuleCohomology, lines 72–86.
- Mathlib.AlgebraicGeometry.AlgClosed.Basic: `pointEquivClosedPoint`, lines 64–87,
  is the actual rational-point/closed-point equivalence under the stated field
  and local-finite-type hypotheses. It introduces no extra notion.

All distinct published proof-dependency modules are imported without `public`:
ProjectiveSpace, SmoothConnectedCurveLocalRings, DivisorModuleLocal,
Curve.RiemannRoch, Modules.Differentials, Modules.Dual,
CochainTensorUniverses, InvertibleModuleGenericStalk, and DensePoints.
The Curve and DivisorModule statement imports also cover def-sc-genus,
def-sc-pic0 and def-sc-divisor. The proof node
`lem-sfb-linear-series-degree-dimension-bound` has no recorded Lean module in the
read repository, so it supplies no import yet. It is only a proof prerequisite,
not needed to type this statement; the existing proof_deps entry is retained.

Edge cases checked: r=0 has its separate literal-zero witness; r=g permits the
final induction step with h1=0; g=1 includes both r=0 and r=1; arbitrary rational
points and repeated points are retained. Genus zero is excluded as intended
(on P1 the degree-one h0 would be two). Empty or zero-dimensional schemes are
excluded by connected-curve, rather than silently by a new assumption. No
characteristic is restricted. Universes are explicit (`universe u`) and
`set_option autoImplicit false` forbids hidden binders. No file-local notation,
instance or helper is used. No node fault or disputed statement was found.

Searches performed using the prescribed msearch wrapper:

- LeanFinder: "On a smooth projective connected curve of positive genus each point
  divisor has one global section and there exists an effective divisor of every
  degree at most the genus with one section". Eight results: Weierstrass-curve
  point/class-group declarations and FunctionField.classNumber, no match.
- Loogle: `"finrankH", "Divisor"`. Zero results.
- grep: `Riemann.Roch|riemannRoch|smallDegreeDivisor|small_degree_divisor`.
  Zero Mathlib results.
- LeanSearch: "A smooth projective curve of positive genus has an effective divisor
  of each degree at most its genus with dimension of global sections equal to
  one". Eight results about division polynomials, Weierstrass curves and
  ProjectiveSpectrum fractions, no match.
- Direct rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the item id and `smallDegreeDivisor|small_degree_divisor`: only the
  SymmetricAbelImageGeometry proof docstring cites the item; no declaration.
- Direct rg for `h⁰|h^0|finrankH.*1|finrankH.*single|divisor.*sections` and for
  point divisors located upstream RiemannRoch, EffectiveDivisorCount and the
  canonical divisor construction. None states these three conclusions.
- The full candidate declaration name `smallDegreeDivisor_sections` and intended
  module name were checked by rg against the project and upstream name index:
  no previous declaration or module.

Validation: scompile.py compiled the single file both as a sandbox module and as
Sheaf.AlgebraicGeometry.SmallDegreeDivisorSections, cleanly (2.1 s each). The first
attempt exposed a namespace typo for closedPoints and a line break inside field
notation; both were corrected before the clean run. The JSON signature is
extracted verbatim from the final file. All lines are at most 100 characters.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
