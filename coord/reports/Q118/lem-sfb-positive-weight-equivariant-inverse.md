## Worker report

The item is stated as `AlgebraicGeometry.isIso_of_positive_tangent_weights` in
`Sheaf.AlgebraicGeometry.PositiveWeightEquivariantInverse`. Its only proof is `by sorry`.
No existing statement, source, proof, or dependency was corrected or removed. A single
new definition node supplies the positive-weight predicate for arbitrary affine points.
Its two definitions have explicit data and contain no postponed proofs or choices.

Clause-by-clause correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Arbitrary affine F-schemes X and Y: arbitrary `A B : Type u`, commutative rings with
  `Algebra F A` and `Algebra F B`, represented by `StandardGroupSchemes.affine F A/B`.
  This is the recorded affine-spectrum construction: Spec A/B with the given structural
  map. Every affine F-scheme admits this presentation, and morphisms and points are exactly
  algebra homomorphisms by the fully faithful `algSpec` correspondence. These are arbitrary
  algebras, not polynomial rings or chosen coordinate charts; thus no affine scheme case
  is excluded and no extra geometric hypothesis is imposed.
- Smoothness: both `[Smooth (StandardGroupSchemes.affine F A/B).hom]`.
- Connectedness, including nonemptiness: both `ConnectedSpace ... .left` instances.
- Finite type: both `LocallyOfFiniteType ... .hom` and `QuasiCompact ... .hom` instances,
  exactly as the finite-type node's existing record specifies. Affineness is intrinsic to
  the Spec presentation. Neither a dimension nor a dimension-equality assumption is added.
- G_m actions: two `ModObj (StandardGroupSchemes.multiplicative F) ...` instances. Mathlib's
  `ModObj` contains the scheme morphism and the unit and associative action laws, in the
  Cartesian monoidal category `Over (Spec F)`. This is a regular scheme action rather than
  an action of the abstract group F-units.
- Rational points x and y: `x : A →ₐ[F] F` and `y : B →ₐ[F] F`.
- Fixedness: `hxfixed` and `hyfixed` identify the orbit map from G_m with the constant point
  section, as an equality in `Over (Spec F)`. They test the full scheme action.
- F-morphism f: `φ : B →ₐ[F] A`, with actual morphism `StandardGroupSchemes.map F φ`.
- f(x) = y: `hpoint : x.comp φ = y`.
- Equivariance as scheme identity: `IsModHom (StandardGroupSchemes.multiplicative F)
  (StandardGroupSchemes.map F φ)` contains exactly action followed by f = id × f followed
  by the target action. It is not only an equality on F-points.
- Cotangent spaces m/m² and tangent duals: `(RingHom.ker x/y).Cotangent →ₗ[F] F` uses the
  actual evaluation ideals. Mathlib `Ideal.Cotangent` is I/(I times the module I), equivalent
  to I/I²; the latter identity is `Ideal.map_toCotangent_ker`. No local-ring residue-field
  choices or rationality assumptions beyond x/y are introduced.
- Differential is the dual of cotangent pullback, and is invertible: `hdf` asserts a linear
  equivalence e between these two exact dual spaces and characterizes it by
  `y.cotangentDerivation (e v) b = x.cotangentDerivation v (φ b)` for every v and b.
  The existing cotangentDerivation has formula v([a - x(a)]). Given `hpoint`, on b in ker y
  the formula is e(v)([b]) = v([φ(b)]); this is the dual of `Ideal.mapCotangent`, and every
  cotangent class has a representative in ker y. Conversely that dual map satisfies the
  displayed equality for arbitrary b by subtracting its scalar value. Thus hdf asserts
  precisely invertibility of df, without a freely chosen auxiliary tangent map or an added
  condition. It also avoids an opaque proof-dependent transport between kernel ideals.
- Positive character subspaces: `hweights : AffinePointTangent.HasPositiveWeights x`.
  This predicate requires a finite basis of the tangent dual and positive natural exponents,
  with the differentiated action acting on each basis vector as t to that exponent.
  Positive natural exponents are exactly positive integer characters. Finite type makes
  the cotangent quotient finite dimensional, so the finite homogeneous basis formulation
  is equivalent to the node's direct sum of positive-weight subspaces.
- Exact action on tangent vectors: `pointOver` applies the existing `AlgHom.toDualNumber`
  and `DualNumber.mapAlgebraMap`. The equation in `HasPositiveWeights` compares the given
  action on the constant lift of a G_m(R)-point with precomposition by
  `DualNumber.scale (g(t)^n)`, where g(t) is obtained by `algSpec.fullyFaithful.preimage`.
  It is quantified over every commutative F-algebra R, including nonreduced and zero R.
  The exponent is never cast into F as a derivative of a character. `restrictScalars F`
  retains the specified F-structure on that actual scaling map.
- Conclusion f is an isomorphism of F-schemes: `IsIso (StandardGroupSchemes.map F φ)`
  in `Over (Spec F)`, so its inverse is also over F.
- Zero tangent space: `d : ℕ` in the predicate may be zero, with `Module.Basis (Fin 0)`
  and vacuous positivity/eigenvector equations. No nonempty index instance occurs.
- Arbitrary characteristic: no `CharZero`, `CharP`, perfectness, or prime-to-weight binder.

Dependency declarations read and reused:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`, the
  algebraically-closed clause of the recorded match (no chosen algebraic closure is needed).
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `Scheme`, `Scheme.Hom`.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, `ConnectedSpace`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  QuasiCompact, `LocallyOfFiniteType`, `QuasiCompact`.
- def-sc-gm-ga: Sheaf.AlgebraicGeometry.StandardGroupSchemes, `affine`, `map`,
  `identitySection`, `multiplicative`, `multiplicativeGroup`. Read their full definitions;
  the action uses this exact Laurent Hopf group law.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Mod and Monoidal.Mod: `ModObj`, `IsModHom`,
  `Hom.smul`, `CartesianMonoidalCategory.lift` and `toUnit`.
- Mathlib.RingTheory.Ideal.Cotangent: `Ideal.Cotangent`, `Ideal.toCotangent`,
  `Ideal.mapCotangent` and their representative formulas.
- WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent: `AlgHom.cotangentDerivation`,
  `AlgHom.toDualNumber`, their representative formulas and inverse cotangent-form maps.
- WeilConjectures.Mathlib.Algebra.DualNumber: `DualNumber.scale`, `mapAlgebraMap`.
- def-sc-dual-numbers: Mathlib.Algebra.DualNumber, `DualNumber`.
- def-weil-pbc-free-module: Mathlib.LinearAlgebra.Basis.Defs, `Module.Basis`.
- def-weil-pbc-algebra-hom-quotient: the existing `Algebra`, `AlgHom`, `Ideal` and powers.
- Proof dependencies def-weil-pbc-mv-polynomial-ring (`MvPolynomial`, `aeval`,
  `algHom_ext`) and def-weil-affine-spectrum (`Spec`, `Spec.map`) are imported privately
  through Mathlib.Algebra.MvPolynomial.Basic and Mathlib.AlgebraicGeometry.Spec.
- The two remaining proof dependencies, lem-sfb-fixed-point-homogeneous-cotangent-lifts and
  lem-sfb-positive-weight-luna-coordinates, currently have no Lean record or Mathlib match,
  so there is no module to import. They are not required for elaborating this statement;
  their complete proof roles remain in the theorem docstring. The maintainer can add their
  proof imports when those statements land. There is no import cycle.

Edge cases checked before writing: X = Y = Spec F gives zero cotangent spaces and the
empty basis; empty schemes have no F-point and fail the connected hypothesis. A weight
n divisible by char F still uses the character g^n, not its zero differential. Trivial or
zero weights on a nonzero tangent space fail positivity. Testing on nonreduced R retains
infinitesimal scheme action information; R = 0 is permitted. A finite basis is obtained
from the finite-dimensional cotangent space in the finite-type setting and imposes no
uniform dimension bound. Schemes and coefficients share the usual ambient universe u;
any given field and affine pair can be represented in a common larger universe, and no
independent smaller test universe creates a vacuous condition. Universal Laurent and dual
number test algebras live in u, so the test identities determine scheme morphism identities.

Searches made with the required msearch wrapper (raw query/results retained in searches.jsonl):

1. LeanFinder: equivariant morphism of smooth connected affine schemes with positive
   multiplicative group tangent weights and invertible differential at a fixed point is an
   isomorphism. Eight results: IsEtale, IsSmooth, FormallyUnramified and affine-isomorphism
   interfaces. None states the global positive-weight inverse criterion.
2. Loogle: `"AlgebraicGeometry", "IsIso", "tangent"`: zero hits.
3. Mathlib grep in AlgebraicGeometry: `Luna|positive.{0,25}weight|equivariant.{0,25}inverse`:
   zero hits. Project-wide rg for the item id and weight/tangent/action names found no
   existing theorem. Existing group-specific weight predicates were read and rejected as
   interfaces for arbitrary affine X; the existing algebraic constructors are reused.
4. LeanSearch on rational-point cotangent duals and induced maps: eight hits including
   `Ideal.mapCotangent`, stalk maps and algebra-extension cotangents. Read mapCotangent
   in full and used the explicit derivation formula to characterize its dual.
5. For the new positive-weight notion, LeanSearch returned cotangent-space bases and an
   unrelated manifold tangent instance, LeanFinder returned character modules and affine
   coordinates, Mathlib grep returned zero hits. Full queries and raw results are in the
   new node's mathlib_searches. Local project/DAG and blueprint searches are recorded there.

Source verification: read the actual Milne PDF at printed pp.267--270, including
Definition 13.40, Theorem 13.41, and Corollary 13.42 and its diagram. Read the current latest
blueprint direct-image stability statement/proof (3) at the item's inherited route. No
statement dispute or correction is needed. The source corollary is specialized exactly
as already prescribed by the node: both schemes smooth, G_m and positive characters.

Validation: both delivered files compiled separately via scompile.py against the live
published library, with the definition module supplied first. Both sandbox and library
module checks were clean, with no warnings or errors. No global or local Lake build ran.
All variables and universes are explicit and autoImplicit is disabled.

## New nodes

`def-sfb-affine-point-positive-tangent-weights` records the genuinely missing arbitrary
fixed-point predicate in `Sheaf.AlgebraicGeometry.AffinePointTangent`: `pointOver` is the
explicit dual-number point of a cotangent functional, and `HasPositiveWeights` is its finite
positive character-basis condition on all test algebras. Source is Milne Section 13e,
Definition 13.40 and Theorem 13.41. All constituent notions use their existing declarations.
The existing def-sfb-torus-character-tangent-weights concerns Lie spaces of group schemes,
not an arbitrary affine scheme with a chosen rational point; GmRepresentation.weightSpace
accepts an abstract coaction and does not construct this tangent action. Searches of all
three kinds, the DAG, blueprint and both source roots found no exact existing interface.
The new node's statement dependencies are its cited standard definitions. It is cited by
the item. No dependency module is repaired and no old node's non-owned fields are changed.

Preflight repair: the first dry run found the recorded signature truncated at a named
argument `:=` inside a hypothesis. The record now contains the entire actual theorem
signature through its conclusion. No Lean statement or mathematical hypothesis changed.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
