## Worker report

The delivery states `WeilConjectures.FiniteFieldDatum.geometric_fibre_comparison_hypotheses`
in `Sheaf.Paper.GeometricFibreComparisonHypotheses`. Its only proof is `by sorry`.
There are no new notions, helper definitions, dependency repairs or statement corrections.
Only the item's `lean` field changes. The source is the final coefficient-category reference
in main-20261015 `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, with the
five inherited proof steps and their cited Stacks/Deligne sources retained in the docstring.

Hypothesis and conclusion audit:

- The full tuple `(p,a,q,k₀,k)` is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields give `D.prime`, `D.exponent_pos`, `D.cardinality_eq`, arbitrary finite
  field `D.k₀` with `D.card_base`, and an arbitrary fixed algebraic closure `D.k`.
  No particular finite field or closure model is substituted.
- A prime different from `p` is `(l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)`.
- A separated finite-type model is `X₀ : Over (Spec (CommRingCat.of D.k₀))` with
  `[IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.
  Finite type means the last two hypotheses together, not finite presentation or properness.
- `X` is exactly `(D.geometricFiber X₀).left`; `a_X` is its `.hom`, the second
  projection of the chosen pullback defining the dependency's geometric fibre.
- The first three conjuncts assert `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` for this same `a_X`.
- The fourth conjunct is `IsNoetherian (D.geometricFiber X₀).left`. Mathlib's class
  extends `IsLocallyNoetherian` and `CompactSpace`, exactly the stated meaning.
- The fifth conjunct is `∃ d : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤
  (d : WithBot ℕ∞)`. This is the dependency's chain-length Krull dimension,
  retaining bottom for the empty scheme, rather than dimension truncated to zero.
- The sixth conjunct quantifies over every point `x` of this same scheme and gives
  a unit `t` in its actual structure-sheaf stalk. The equality `↑t = l` says that
  the integer is a unit; `↑(t⁻¹) = ... ((l : D.k)⁻¹)` specifies its inverse.
  The map in that equality is the canonical ring-map composite
  `(Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ (D.geometricFiber X₀).hom.appTop ≫
  (D.geometricFiber X₀).left.presheaf.Γgerm x`, from the base field to global sections
  of the base, then to global sections of X, then to the actual stalk. Thus it is
  precisely the structure homomorphism k → O_{X,x}, with no arbitrary map or algebra
  instance supplied. Existence of this unit is equivalent to IsUnit plus the
  specified inverse, by uniqueness of multiplicative inverses in a commutative ring.
- The last two conjuncts assert that `(D.geometricFrobenius X₀).hom` and
  `D.galoisMap X₀.hom (FiniteField.frobeniusAlgEquivOfAlgebraic ...)` compose to
  the identity in both orders. The first is the recorded id × Spec(geometric
  Frobenius); the second is id × Spec(arithmetic Frobenius). These equations
  express the claimed automorphism and its explicit inverse as scheme morphisms.
  The finite enumeration is supplied by `Fintype.ofFinite D.k₀` directly, without
  an additional assumption. The different implicit-argument orders of the
  arithmetic and geometric field-Frobenius declarations were checked in source.
- There is no `[FiniteDimensional D.k₀ D.k]`, `[Nonempty X]`, assumption of
  k-linearity, smoothness, reducedness or properness. All universes are explicit.

Dependency declarations used (full signatures and docstrings read):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, `galoisMap`, and the
  proved `galoisMap_inverse`/`galoisMap_projections` identifying these maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`
  (in its imported Separated module), whose diagonal is a closed immersion.
  The dependency's proper/universally-closed clauses are not extra assumptions here.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imported QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: reexports the recorded
  `topologicalKrullDim` from Mathlib.Topology.KrullDimension. The pointwise
  `topologicalKrullDimAt` is not needed for this node's global conclusion.
- Proof imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.exists_topologicalKrullDim_le`; and
  `Sheaf.SixFunctors.FrobeniusSquareCartesian`,
  `WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian`.
- The Mathlib matches for the remaining proof dependencies are already exposed:
  `IsSeparated.isStableUnderBaseChange`, `locallyOfFiniteType_isStableUnderBaseChange`,
  `quasiCompact_isStableUnderBaseChange`, `LocallyOfFiniteType.isLocallyNoetherian`,
  `QuasiCompact.compactSpace_of_compactSpace`, and `IsNoetherianRing`.
  No separate theorem is invented for these exact Mathlib interfaces.

Edge cases checked before writing:

- Empty X₀ and empty X: bottom Krull dimension is at most zero, the stalk clause
  is vacuous, and the inverse equations are equations of the empty scheme's maps.
- X₀ = Spec k₀: fibre Spec k is zero-dimensional; the stalk unit is l in k and
  the coefficient inverse is literally l⁻¹. Frobenius can be semilinear, and the
  inverse equations do not assert that it fixes the projection to Spec k.
- Affine line and arbitrary finite-dimensional affine schemes: the bound d is
  existential, not a fixed zero bound. Nonreduced schemes (e.g. dual numbers)
  satisfy the same conditions; no integrality or reducedness hypothesis appears.
- Infinite algebraic closure extension: neither base-change permanence nor the
  field dimension theorem requires k/k₀ to be finite. Only k₀ is a finite field.
- l = p is excluded essentially: in nonzero characteristic-p stalks its image
  would be zero and cannot be a unit. All distinct primes, including l = 2 when
  p differs from 2, are allowed.

Searches, all through the prescribed tools or read-only rg:

1. msearch.py leanfinder query: "A finite type scheme over a finite field after
   base change to its algebraic closure is Noetherian of finite Krull dimension,
   primes different from the characteristic are units in its stalks, and geometric
   Frobenius has arithmetic Frobenius inverse". Eight hits, including
   `finite_appTop_of_universallyClosed`, `IsArithFrobAt.arithFrobAt`,
   `Algebra.IsGeometricallyReduced`; none states the complete conjunction.
2. msearch.py loogle: `AlgebraicGeometry.IsNoetherian,
   AlgebraicGeometry.LocallyOfFiniteType`. Zero hits.
3. msearch.py grep under AlgebraicGeometry:
   `geometricFrobenius|geometricFiber.*[Nn]oetherian|[Nn]oetherian.*geometricFiber`.
   Zero Mathlib hits.
4. msearch.py leansearch: "The geometric fibre of a separated finite type scheme
   over a finite field is Noetherian and finite dimensional, with primes different
   from its characteristic invertible in every local ring". Eight hits, including
   `Scheme.Hom.fiber`, `LocallyOfFiniteType.isLocallyNoetherian`, `isProper_eq`;
   none states the complete conjunction.
5. rg over lean/WeilConjectures and lean/Sheaf, the item id and
   `geometric_fibre_comparison_hypotheses|GeometricFibreComparisonHypotheses`:
   no existing declaration or matching module.
6. Broader rg for geometric-fibre Noetherianity found
   `sfRecollementGeometricNoetherian` in SfOpenClosedTriangleAllStages (only the
   Noetherian conclusion), `geometricFiber_coefficientPrimeInvertible` in
   SfWeilSheafComplex (only residue-field invertibility, not stalks or a specified
   inverse), and the parent `frobeniusFixedPairComparison` (existence of admissibility
   proofs for a comparison, with additional coefficient/stage data, not the same
   theorem). Their full relevant signatures were read; none matches this item.
7. Read-only rg in Mathlib and the project for `ΓSpecIso`, `Γgerm`, `stalkMap`,
   `topologicalKrullDim`, and both field Frobenius names supplied their canonical
   definitions and signatures. No duplicate canonical construction was needed.

Validation: scompile.py compiled the scratch-module view and the final library module
cleanly (2.8 s and 2.4 s); no errors or warnings. The first attempt exposed the
arithmetic Frobenius explicit-argument order, which was corrected using its source.

## Second reading by Q73

This is an in-session second reading by the dispatched worker; no other agent was
started, as explicitly required by the dispatcher. The maintainer's independent review
will read this delivery. I reopened the node and final module and checked each clause:
D carries the entire global datum, l is prime and different from p, X₀ is separated
and finite type, the actual geometricFiber supplies both X and a_X, the first three
conjuncts give a_X's properties, IsNoetherian includes quasi-compactness, the dimension
bound retains bottom, and the stalk unit has exactly the prescribed field-image inverse.
Both inverse equations use the recorded geometric scheme map and the arithmetic
coefficient action; neither asserts k-linearity. No hypothesis or clause mismatch was
found. The arithmetic field Frobenius argument order was the only compilation repair.
No statement correction or new/dependency node was needed. All proof bodies remain sorry.
