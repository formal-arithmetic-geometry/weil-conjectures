## Worker report

The module `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` states
`WeilConjectures.finiteGeometricSectionsAndPointOrbits`, with its sole proof `sorry`.
All auxiliary definitions contain their actual data; the three structures unpack this
node's conclusions and are not alternative coefficient categories or chosen comparison maps.
The mathematical node is unchanged. There are no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- The global finite-field tuple is `D : FiniteFieldDatum.{u}`, including its positive
  exponent, cardinality and specified algebraic closure. `Z₀ : Over (Spec (.of D.k₀))`
  with `[IsFinite Z₀.hom]` is exactly the finite model. Properness and finite type
  follow by existing instances; they are not added assumptions. `D.geometricFiber Z₀`
  is its recorded base change with second projection.
- `l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]` give the prime-to-characteristic
  coefficient prime. The rational clause quantifies over every finite-dimensional
  field extension `E` of `ℚ_[l]`. The coefficient closure is arbitrary `Ω : Type v`
  with its specified algebra and `IsAlgClosure`; site and closure universes remain
  independent. Rational constructions do not depend on a chosen embedding into Ω,
  so quantifying all E also covers each E embedded in that closure.
- `sfRationalHeart` and `sfCommonStageHeart` are the recorded full constructible hearts.
  No Weil object, action, or Frobenius identification of M is assumed anywhere.
- `Points` is the subtype of actual arrows `s ⟶ Z` satisfying `z ≫ a_Z = 𝟙 s`.
  `projection` evaluates the first projection at the unique point of Spec k.
  `PointsOver x` is its fibre over the actual closed point `x`.
- `PointOrbits.finite_points` and `.finite_closedPoints` give both finite sets.
  `.projection_closed` gives the map to closed points, and `.projection_surjective`
  gives all its fibres nonempty, including when the whole target is empty.
- `Embeddings` consists of ring embeddings of the actual residue field (injectivity
  follows because the source is a field) commuting with the structural k₀ map.
  `.embeddings` is the equivalence P_x with these embeddings, and `.embeddings_spec`
  fixes it by the actual residue-field Spec map, rather than an arbitrary bijection.
  `.cardinality` and `.degree_pos` state `Nat.card P_x = degreeOver x ≥ 1`.
  `degreeOver` is exactly finrank for `residueFieldAlgebraMap.toAlgebra`.
- `.permutation_spec` fixes T as h⁻¹ followed by z followed by g in Lean's composition
  order. `.preserves_projection` says it preserves every P_x. `.embedding_frobenius`
  gives postcomposition by arithmetic Frobenius γ⁻¹, with the required sign.
  `.single_cycle` gives a unique exponent in `Fin d_x` between every two points in
  one fibre, exactly one cycle of length d_x. `.period_square` is g^d z = z h^d.
  Powers use the actual automorphism and endomorphism monoids, including exponent zero.
- `sections` is H⁰ of `ProperSemilinearGerms.rationalSections`, i.e. H_c⁰ at the identity
  compactification. `fibre` is H⁰ of the recorded `rationalFibre = Lz* ⋙ Fib_s`.
  `evaluation` is H⁰ of the dependency's exact `rationalGerm`, retaining its actual
  proper comparison and whole-system counit. `StalkSum` is the displayed double sum.
- `RationalEvaluation.iso` is a linear equivalence to that sum and `.component` fixes
  every component to `evaluation`. `.naturality` quantifies over all full-heart
  morphisms. `.finite_sections` and `.finite_fibres` assert the two finiteness clauses.
- `realizedSections`, `realizedFibre`, and `realizedEvaluation` are H⁰ after the
  recorded derived scalar realization from a finite field to Ω. The last is literally
  the image of the finite-stage canonical germ, not an arbitrary isomorphic map.
- `CommonEvaluation.iso` and `.component` give these isomorphisms at every finite
  stage whose object is in the rational heart; `.naturality` covers every stage arrow.
  `.common_iso` and `.common_component` cover every object of the recorded common
  heart, including those represented initially by a different stage presentation.
  The common and stage finite-dimensionality fields give all the same finiteness
  conclusions over Ω.
- `sectionsStageComparison` is H⁰ of the recorded compact source comparison, and
  `fibreStageComparison` is H⁰ of the recorded point scalar comparison followed by
  the recorded pullback scalar comparison. `.changeStage` asserts that the germs
  commute with those exact comparisons at EVERY larger stage. `.common_naturality`
  states the conjugated naturality equation for any two common-heart objects, any
  common stage L, and EVERY arrow at L. This covers arbitrary morphisms in the
  common-stage category by its recorded representative calculus. It includes L equal
  to either or both original stages; no strict-extension hypothesis is used.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `.geometricFiber`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfRationalHeartProperty`,
  `sfCommonStageHeart`, `sfCommonStageHeartProperty`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` publicly retains
  `OrdinaryCompactCohomology`; the identity-compactification source here is the
  exact source of the recorded proper germ, as exposed by
  `Sheaf.Paper.ProperSectionsSemilinearGerms`:
  `ProperSemilinearGerms.rationalSections`, `.rationalFibre`, `.rationalGerm`,
  `.stageRealization`, `.realizedSourceComparison`, `.realizedPointComparison`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre` and its normalized scalar
  comparison, used through the recorded germ and realized point comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; its restriction to the finite-dimensional point
  target is `DerivedCategory.coefficientFdCohomology`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `.fromSpecResidueField`, and `Scheme.SpecToEquivOfField` (in the proof plan).
- `WeilConjectures.ZetaSeries`: `Scheme.Hom.residueFieldAlgebraMap`, `.degreeOver`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `D.geometricFrobenius`;
  `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso` (through the germ).
  `FiniteField.frobeniusAlgEquivOfAlgebraic` is the arithmetic field map.
- Plain imports retain all recorded non-Mathlib proof-dependency modules. The sf/PBC
  heart-model bridge has no recorded Lean module yet, so no import is invented for it.

Source and edge checks: read Stacks etale-cohomology.tex,
`proposition-finite-higher-direct-image-zero` (Tag 03QP), including the actual restriction
components and its finite-product/direct-sum formulas. Read the latest blueprint finite
boundary weight statement and proof. The blueprint's arithmetic-invariants display is
not the geometric formula; this node already explicitly corrects that distinction.
Checked the empty scheme (no base points, empty sums, zero sections), nonreduced
`Spec(k₀[ε]/ε²)` (one point, degree one), `Spec F_(q^d)` (d embeddings and one d-cycle),
and disjoint unions with different degrees and stalk ranks. No connectedness, reducedness,
nonemptiness, equal rank, or Weil descent is added. Identity coefficient extension and
exponent zero remain available. No statement dispute or correction was needed.

Existing-declaration searches:

- `msearch.py ... leanfinder "finite scheme over finite field geometric points Frobenius
  orbits global sections direct sum stalks"`: eight hits. Mathlib finite fibre and
  `Scheme.SpecToEquivOfField` are useful ingredients, not the combined statement.
- `msearch.py ... loogle "FiniteField.frobeniusAlgEquivOfAlgebraic,
  Scheme.SpecToEquivOfField, DirectSum.linearEquivFunOnFintype"`: no combined hit;
  Loogle reported the unqualified Scheme name unknown. The fully qualified declaration
  was then located and read directly in Mathlib/AlgebraicGeometry/ResidueField.lean.
- `msearch.py ... grep "finite.*(geometric|orbit)|globalSections.*(stalk|fibre)|
  SpecToEquivOfField" AlgebraicGeometry`: 23 hits, principally the residue-field
  equivalence and consumers, none stating this node.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for finite geometric sections,
  point orbits, finite sections, and rationalGerm found the existing proper germ and
  finite Weil-point cohomology ingredients. None gives the no-Weil-structure,
  rational/common-stage normalized evaluation and orbit statement. `grep -rn` for
  the exact node id in WeilConjectures and search of `dag/lean_names_upstream.json`
  found no attachment. A final declaration-name search in Mathlib, upstream, and
  Sheaf found no duplicate `finiteGeometricSectionsAndPointOrbits` or namespace.

Validation: all compilation uses the prescribed scompile.py, with every file compiled
separately against the published live library. No live source or Git mutation was made.
The sole postponed theorem is the node's main declaration, with its ten-step proof plan
in its docstring. Final dry-run and delivery results are recorded below.

## Second reading by Q26

Self-review performed in the dispatcher worker; no other agent was started, as instructed.
Opened the node and final module side by side and matched the clauses above. This is not
an independent second-agent review; the delivery is left for the maintainer's independent
review. The rereading found that stage-level isomorphisms and a scalar square alone did
not explicitly give a statement for every object of the common-stage heart or every
common-stage morphism representative. Added `common_iso`, `common_component`, common
finite-dimensionality fields, and `common_naturality` with arbitrary L and arbitrary f.
Checked that the equality uses the inverse source comparison and forward point comparison
in the required directions. Checked the geometric Frobenius sign on b tensor c and the
reversed Lean composition order in the period square. No dependency record changed.

Final scompile.py check: clean in both sandbox and actual library module mode
(46.6 seconds and 31.0 seconds respectively). The expanded common-stage statement
initially timed out; explicit helper result types and disabling unused generated
constructor metadata repaired elaboration without changing the statement or limit.
