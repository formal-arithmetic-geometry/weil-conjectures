## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.RetractAssertions` states
`AlgebraicGeometry.IsCurve.assertions_of_isIso_comp`, with its proof `sorry`.
There are no new definitions, dependency modules, or statement corrections.

Hypothesis and clause correspondence:

- The algebraically closed base field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The scheme X and its structure morphism are `P.C` and `P.toSpec` in
  `(P : CurveCoefficientPair k)`. The field `P.isCurve` asserts separation,
  local finite type, quasi-compactness (together finite type), and
  `topologicalKrullDim P.C ≤ 1`. There is no smoothness, connectedness or
  properness assumption.
- G is `P.F`; its torsion hypothesis is `P.isTorsion`. H is
  `Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}`, and its torsion
  hypothesis is `(hH : P.C.IsTorsionAbelianSheaf H)`. The pair used for H is
  `⟨P.C, P.toSpec, P.isCurve, H, hH⟩`, so both pairs have exactly the same base
  scheme and structure morphism.
- The two abelian-sheaf maps are `(a : P.F ⟶ H)` and `(b : H ⟶ P.F)`.
  `[IsIso (a ≫ b)]` is precisely that b after a is an automorphism of G;
  categorical composition uses diagram order.
- Constructibility transfers in the direction required by the node via
  `hconstructible : P.IsConstructible →
  (⟨P.C, P.toSpec, P.isCurve, H, hH⟩ : CurveCoefficientPair k).IsConstructible`.
  This uses the dependency's recorded predicate rather than replacing it
  by the upstream module-valued constructibility predicate.
- The local expression E is verbatim the coefficient functor used in the
  landed `AlgebraicGeometry.IsCurve.finite_pushforward_assertions`
  (`Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions`): inverse of
  forget from integer modules to abelian groups, then restriction of scalars
  along `ULift.ringEquiv`. G' and H' are its sheaf compositions applied to G
  and H. This is a change of coefficient category, not extra scalar data.
- The prime-to-characteristic condition is the implication between
  `Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G'` and the same
  predicate on H'. An integer is invertible over k precisely when it is
  prime to its positive characteristic; in characteristic zero every
  positive integer is invertible, so this imposes no extra restriction
  on torsion sheaves.
- The primary condition is the implication between
  `Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G' p` and the predicate on
  H', quantified over `(p : ℕ) [Fact p.Prime] [CharP k p]`. Positive field
  characteristics are exactly the primes. This excludes neither any
  positive characteristic nor any primary torsion sheaf, and introduces
  no characteristic-zero condition.
- The assumption C(X,H) and conclusion C(X,G) are the last implication
  `IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec H' →
   IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G'`. Its existing eight fields
  express respectively C1, C2, C3, C4, C5, C6, C7, C8: vanishing above two;
  affine vanishing above one; characteristic-primary vanishing above one;
  constructible prime-to-characteristic finiteness; proper constructible
  finiteness; prime-to-characteristic extension bijectivity; proper
  extension bijectivity; degree-two open restriction surjectivity.
  The characteristic, properness and constructibility conditions remain
  inside these assertions; the theorem makes none unconditional.

Dependency declarations read and used:

- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic (the relevant part of
  def-weil-algebraic-closure; AlgebraicClosure and IsAlgClosure also read).
- `AlgebraicGeometry.CurveCoefficientPair`,
  Sheaf.AlgebraicGeometry.CurveCoefficientPair: the curve and torsion data.
- `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`,
  Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf.
- `AlgebraicGeometry.Scheme.IsPrimaryTorsionSheaf`,
  WeilConjectures.AlgebraicGeometry.Curve.Assertions.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`, reexported by
  the same module, defined in
  WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf.
- `AlgebraicGeometry.IsCurve.Assertions` and `assertions_iff`,
  WeilConjectures.AlgebraicGeometry.Curve.Assertions. The definition is used;
  its iff theorem was read to check all eight clauses.

The proof docstring carries all eight DAG proof steps and names the
categorical, cohomology and pullback inputs needed for stage 3. In particular,
constructibility of the abelian-sheaf pair and of its equivalent module
sheaf must be identified in stage 3; this is an equivalence of the existing
notions, not an additional theorem hypothesis here.

Edge cases checked before writing: the empty scheme has dimension bottom
and is allowed by IsCurve; zero-dimensional and disconnected curves are
allowed. Zero sheaves and identity maps are included; a ≫ b need not equal
identity, only be invertible. There is no common finite annihilator, no
finiteness assumption on G or H, and no prime-to-characteristic restriction
unless the conditional clause calls for one. In characteristic zero the
primary condition is vacuous and the invertible-order condition is ordinary
torsion. In characteristic p the only relevant positive characteristic
binder is that p. All universe variables are explicitly declared, and the
field/scheme and group universes follow CurveCoefficientPair's signature.

Searches for an existing statement:

- `msearch.py ... leanfinder "Eight etale curve cohomology assertions pass to
  a retract of torsion abelian sheaves"`: eight unrelated cotangent-complex
  and formally etale algebra hits; no match.
- `msearch.py ... loogle "CategoryTheory.Retract,
  AlgebraicGeometry.IsCurve.Assertions"`: no hits; the remote Mathlib-only
  index does not know the project's Assertions declaration.
- `msearch.py ... leansearch "etale cohomology curve assertions retract
  torsion sheaf"`: service unavailable, Internal Server Error.
- `msearch.py ... grep "Assertions.*retract|assertions.*retract|
  IsStableUnderRetracts" CategoryTheory`: generic retract stability hits
  only, including ObjectProperty and MorphismProperty; no curve assertion.
- `rg` of the project's `lean/Sheaf/AlgebraicGeometry` and source
  `WeilConjectures/AlgebraicGeometry/Curve` for curve pairs and retract/summand
  assertion names found the existing finite-pushforward bridge and
  Assertions definitions, but no theorem stating this node.
- `grep -rn "lem-weil-pbc-curve-assertions-retract"` on the entire source
  WeilConjectures tree found no declaration.
- `rg` for the proposed name `assertions_of_isIso_comp`, `assertions_retract`
  and `retract_assertions` on dag/lean_names_upstream.json, the full source
  WeilConjectures tree and lean/Sheaf found no declaration.

Source checked at https://stacks.math.columbia.edu/tag/03SD, proof first
paragraph, because literature/stacks-project is not present in this clone.
It explicitly reduces to the larger sheaf using a composite isomorphism.
The node expands that implicit summand argument into C1–C8. No node fault
or STATEMENT-DISPUTED issue was found.

## Second reading by J1

The node introduces the following data and clauses, matched against the Lean
signature `AlgebraicGeometry.IsCurve.assertions_of_isIso_comp`:

- `k` is a field with `IsAlgClosed k`; rendered by `{k : Type u} [Field k]
  [IsAlgClosed k]`.
- `X` and its curve structure, and torsion sheaf `G`, are rendered by
  `P : CurveCoefficientPair k`; this supplies `P.C`, `P.toSpec`, `P.isCurve`,
  `P.F`, and `P.isTorsion`.
- `H` is a torsion abelian sheaf on the same small etale site, rendered by
  `H : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}` and
  `hH : P.C.IsTorsionAbelianSheaf H`.
- The maps `a : G ⟶ H` and `b : H ⟶ G`, with `b ∘ a` invertible, are rendered
  by `(a : P.F ⟶ H) (b : H ⟶ P.F) [IsIso (a ≫ b)]`; categorical composition
  has exactly the node's order.
- Constructibility transfer is exactly the node's implication, rendered by
  `hconstructible` between the two `CurveCoefficientPair.IsConstructible`
  predicates.
- Prime-to-characteristic transfer is the first implication after the local
  coefficient equivalence `E`; primary transfer is the quantified implication
  over `(p : ℕ) [Fact p.Prime] [CharP k p]`.
- The final hypothesis and conclusion are respectively
  `IsCurve.Assertions ... H'` and `IsCurve.Assertions ... G'`, where `G'` and
  `H'` are the canonical abelian-group-to-`ULift ℤ` module sheaf images. This
  is the project's recorded coefficient bridge used by the Assertions node,
  and preserves all eight C1--C8 clauses.

Edge cases were checked: `P.C` may be empty, zero-dimensional, disconnected,
or zero-dimensional; zero sheaves and identity/retract maps are admitted; no
properness, smoothness, connectedness, finite annihilator, or finiteness
hypothesis was added. The primary binder is only present for positive
characteristic, while the invertible-order implication is vacuous in
characteristic zero as required. Universes are explicit and the test-field
universe is the one supplied by the curve pair and Assertions declarations.

I searched the DAG, `lean/Sheaf`, the slopmaster2 source, and Mathlib with
`rg` and `msearch.py` (LeanFinder, Loogle, and grep queries for curve
assertions/retracts, `assertions_of_isIso_comp`, and generic retract
stability). No existing declaration states this theorem; all hits were
generic categorical retract results or unrelated Weierstrass declarations.

No mismatch was found. The worker's module already compiles cleanly with the
node's statement verbatim, contains no hollow definition, and has the source
and blueprint docstrings and the complete proof-step documentation. No files
were changed in the second reading.
