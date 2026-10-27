## Worker report

The module `Sheaf.Paper.CompletedCoefficientRegularQuotients` states
`AlgebraicGeometry.ProEtale.sp_completed_coefficient_regular_quotients`, with a
`sorry` proof. It also constructs the scalar section, the commutative version of
the existing ell quotient sheaf, its actual completed projection, and the two
families of quotient transitions. Every construction has real data. There are
no extra hypotheses, statement corrections, new nodes, or dependency repairs.
The existing landed node `def-pe-principal-power-ring-quotients` is added to
stmt_deps to reuse its actual sheafified quotient rather than duplicate it.

Hypotheses and clauses, with the node and module both open:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- O and chosen pi: `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`, imported unchanged from the
  recorded coefficient-extension module.
- Arbitrary scheme T and its small pro-etale site: `(T : Scheme.{t})` and
  `Scheme.ProEt.topology T`. The object universe is t+1 and the morphism universe
  t. Coefficient values are in `max u (t+1)` using ULift; no universes are equated.
  There is no field datum, characteristic, finiteness, or nonemptiness hypothesis
  on T.
- R: the actual `WeilConjectures.completedIntegralCommRingSheafUnrestricted`.
  This retains the same underlying recorded completed ring sheaf, rather than
  replacing it by the constant sheaf of O.
- C_(n+1): `integralCoefficientCommRingSheaf l E T n`.
  B_(n+1): `spEllCommRingSheaf l E T n`, definitionally the commutative-ring
  version of the dependency's `spCoefficientRing`. Both are constant sheaves
  of the actual lifted quotient rings.
- Actual projections: `completedIntegralCommRingProjectionUnrestricted` is the
  existing uniformizer limit projection. `spCompletedEllProjection` retains the
  ring map `(sp_completed_coefficient_limit l E T).choose.hom ≫ limit.π ...`.
  This choice is allowed: the dependency asserts existence and uniqueness of the
  comparison with normalization on every constant scalar. It is not an arbitrary
  map or a choice from a bare Nonempty type.
- Factorization: the first conjunct quantifies `v : Oˣ` and `e : ℕ`, requires
  `1 ≤ e`, and states `l = (v : O) * pi ^ e`.
- Cofinality: the next conjunct gives both directions of positive power ideal
  containment, using the existing `spEllIdeal` and `coefficientExtensionIdeal`.
- Finiteness: `∀ n`, both `Finite (coefficientExtensionRing ... (n+1))` and
  `Finite (O ⧸ spEllIdeal ... ^ (n+1))`.
- Constant scalars: `spCompletedScalarSection` first applies the sheafification
  unit to the constant integral section, then applies the recorded
  `integralConstantToCompletionOfUniverses`. Naturality is supplied by the
  existing `Functor.sectionsFunctor` map. Its values are exactly the scalar
  formula in `completedIntegralScalar_regular` and projection divisibility.
- Regularity: the fourth conjunct is `∀ (n : ℕ) (U : T.ProEtᵒᵖ)`, two
  `Function.Injective` assertions for multiplication by the specified constant
  pi or ell section to exponent n+1. The explicit `@id` exposes the section's
  ring type to elaboration; it introduces no extra object or hypothesis.
- Epimorphisms: the fifth conjunct requires `Epi` for each actual projection in
  the category of commutative ring sheaves.
- Kernels: for every U it equates each projection's `RingHom.ker` with the
  existing `sectionPowerIdeal R scalar (n+1) U`. This is equality of ideals,
  stronger in precision than merely describing the kernel's elements. Because
  multiplication is injective, sectionwise scalar multiples form a sheaf:
  unique local preimages glue. Thus these sectionwise ideals are precisely the
  ideal sheaves pi^(n+1)R and ell^(n+1)R, not an unsaturated presheaf image.
- Ring-sheaf quotient isomorphisms: the last conjunct supplies whole families
  `a n` and `b n` from `principalPowerRingQuotient` to C_(n+1) and B_(n+1).
  `principalPowerRingQuotient` is the pre-existing CommRingCat sheafification
  of sectionwise quotients, not the sectionwise quotient itself.
- Projection normalization: two equalities say the existing
  `principalPowerRingProjection` followed by `(a n).hom` or `(b n).hom` is the
  corresponding actual completed projection.
- Every quotient transition: `∀ (m n : ℕ) (h : m ≤ n)` supplies quotient maps
  r and s. Their composites with the higher canonical quotient projections
  are the lower projections, fixing them as the canonical transitions.
  The last two equalities state the transition squares for a and b commute
  with `spUniformizerQuotientTransition` and `spEllQuotientTransition`.
  These reductions use `Ideal.Quotient.factorPow` and `RingHom.ulift`, hence
  are induced by the identity on O. The existential r/s are not unconstrained:
  quotient projection normalization uniquely determines each map.

Dependencies read and used:

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, theorem
  `Padic.finite_coefficientExtensionRing`, importing the full recorded
  `CoefficientExtension` constructions, whose signatures and docstrings were read.
- `sk-def-sp-coefficient-towers`:
  `Sheaf.Paper.SmoothPurityCoefficientTowers`, especially `spEllIdeal`,
  `spCoefficientRing`, `spCoefficientRings`, `sp_completed_coefficient_limit`,
  and its normalization. The complete module was read.
- `def-weil-pbc-constant-sheaf`:
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`;
  the full signature and docstring were read. Exported by the tower dependency.
- Added landed construction `def-pe-principal-power-ring-quotients`:
  `Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients`,
  `sectionPowerIdeal`, `principalPowerRingQuotient`, `principalPowerRingProjection`.
  The whole module and node statement/lean record were read.
- Proof-only imports include the two recorded completed scalar/projection lemmas,
  the recorded upstream local-sheafification-sections module, the valued finite
  quotient module, and the ring underlying-set sheafification comparison module.
  The other stated proof dependencies are already public imports through the
  recorded coefficient and tower modules. The docstring contains all seven
  original proof steps, including the local-lift and local-class gluing argument.

Edge cases checked before writing: n=0 represents exponent one, so every positive
exponent is covered exactly once and there is no omitted first level. T may be
empty, and U may be empty: injectivity on a subsingleton is appropriate; ring
sheaves then have the expected zero value. No claim says all global sections
of a sheaf quotient are sectionwise quotient classes. Characteristic ell on T
is harmless: scalars come from O, not the structure sheaf of T. Ramification
index e=1 and ramified e>1 are both included. Transition m=n includes identities;
all nonadjacent transitions are covered, not only successor maps. Independent
site and coefficient universes are retained.

Searches for existing notions/statements:

- `msearch.py ... leanfinder`: "Completed integral coefficient sheaf regular
  scalar powers and canonical finite quotient projections on every pro-etale
  site" returned eight hits, including BDeRham, BDeRhamPlus, and
  StandardEtalePresentation; none states this sheaf projection/kernel package.
- `msearch.py ... leansearch`: "The quotient of the completed integral coefficient
  ring sheaf by a uniformizer power is the constant finite quotient ring sheaf"
  returned eight arithmetic hits, including
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`,
  `WittVector.quotientPEquiv`, and `IsLocalRing.finite_quotient_iff`.
  They do not supply the actual completed coefficient-sheaf comparison.
- `msearch.py ... loogle`: `Ideal.Quotient, presheafToSheaf` returned zero
  hits, with unknown identifier Ideal.Quotient (a namespace rather than a
  declaration). Local source searches below supplied the usable quotient API.
- `msearch.py ... grep`: `PrincipalPowerQuotient|completedIntegralScalar|sp_completed_coefficient`
  and `completedIntegral|principalPowerRingQuotient` each returned no Mathlib hit.
- `rg -n` in lean/WeilConjectures and lean/Sheaf for completed-integral,
  scalar, projection, quotient, and prospective declaration names found the
  existing scalar regularity and projection divisibility lemmas, the coefficient
  tower comparison, and the principal-power quotient construction; all are used.
  There is no theorem stating this combined node. Searching the item's id in
  lean/WeilConjectures returned no match. Searching dag/nodes for
  principalPowerRingQuotient located its existing definition node, now cited.

Validation: `scompile.py N6 lem-sp-completed-coefficient-regular-quotients <file>`
passed in sandbox and library modes (6.2 s and 3.8 s). No unexpected warnings.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by N6

This dispatcher assignment prohibits additional agents; this is the author's
separate second reading, with independent review deferred to the maintainer as
specified by the brief, not a claim of another worker's review.

Reopened the node and the final file and checked all clauses above. Initially,
section values needed explicit `@id` coercions, and constructing the commutative
ell projection needed the existing completed commutative ring instance. These
elaboration issues were repaired without changing the mathematical statement.
The second reading specifically checked that B is the existing ell coefficient
object (only commutativity is retained), that its map uses the uniquely normalized
comparison rather than an arbitrary isomorphism, that kernel equalities are on
every object, that quotients are sheafified, and that arbitrary-level transition
compatibility includes the quotient projections. No mathematical mismatch found.
