## Worker report

The module `Sheaf.AlgebraicGeometry.TorusFiniteCharacterSeparation` states
`AlgebraicGeometry.exists_torus_point_injOn_characters` with one `sorry` proof.
It introduces no definitions. The node statement, proof, and source are unchanged;
`stmt_deps` gains the already landed definition node
`def-sfb-tori-multiplicative-type`, whose recorded `splitTorus` construction is used.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The nonnegative integer rank is `(r : ℕ)`, including zero.
- The k-group scheme is `(T : Grp (Over (Spec (.of k))))`. This bundles exactly
  the recorded `GrpObj` on a scheme over k, with no affineness, smoothness,
  connectedness, or finite-type assumption added.
- The split hypothesis is `hT : Nonempty (T ≅ MultiplicativeType.splitTorus k r)`.
  The isomorphism lies in the category of group objects, so it respects the group law.
  The recorded split torus is recursively a product of the recorded G_m, with the
  monoidal unit (the trivial group over Spec k) as the empty product.
- Characters are `T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)`.
  Morphisms in `Grp` are precisely underlying morphisms over k compatible with
  multiplication and identity; inverse compatibility follows from the group laws.
  No arbitrary abstract character of the group T(k) is substituted.
- The finite set is `Ω : Set (T ⟶ Grp.mk ...)` with `hΩ : Ω.Finite`.
  A set already has distinct elements; no separate injectivity hypothesis or
  enumeration is needed, and the empty set is allowed.
- The rational point is `s : StandardGroupSchemes.affine k k ⟶ T.X`.
  By the recorded definition of `affine`, its source is Spec k over Spec k.
- Evaluation is the actual composite `s ≫ χ.hom.hom`, a k-point of G_m.
  G_m is Spec k[t,t⁻¹] with its canonical Laurent Hopf law, so its A-points
  are units of A. Equality or inequality of these point morphisms is exactly
  equality or inequality of their corresponding units. The statement therefore
  does not need a second coordinate-evaluation construction.
- `Set.InjOn (fun χ ↦ s ≫ χ.hom.hom) Ω` says that equal evaluated values for
  two members imply equal characters, equivalently that distinct members have
  unequal values. This is exactly both concluding formulations in the node.
- There is no characteristic restriction or extra field extension. The universe
  `u` is arbitrary; `autoImplicit false` ensures every variable is bound.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`: the recorded field definition.
- `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`: every polynomial splits,
  equivalently every nonconstant polynomial has a root (the recorded match's
  explanatory `how` explicitly names this class).
- `CategoryTheory.GrpObj`, `Grp`, `Grp.homMk`, and `Grp`'s induced category,
  `Mathlib.CategoryTheory.Monoidal.Grp`: the recorded group-scheme structure and
  group-scheme morphisms. Also read the terminology documentation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `StandardGroupSchemes.affine`, `multiplicative`, `multiplicativeGroup`,
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: actual spectra and the recorded
  Laurent Hopf group structure.
- `MultiplicativeType.splitTorus`, `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  the already landed finite-product model, used directly without a private copy.
  Its import publicly exposes the preceding field/group/G_m dependencies.
- Proof imports: `Mathlib.Algebra.MvPolynomial.Funext` provides the recorded
  `MvPolynomial.funext`, and exposes the polynomial-ring/domain definitions used
  by the proof. `lem-sfb-split-torus-hom-matrices` currently has no Lean record or
  source module, so there is no module to import for that proof dependency;
  its use is retained in the complete five-step proof docstring. It is not
  needed to type this statement.

Sources read: the local Milne iAG2017 PDF, Definition 12.14 (printed p.236),
Theorem 12.9 conventions and Lemma 16.42 proof (printed p.339), in particular
its finitely many proper character-equality loci and the point outside their union.
The module docstring carries the node's five-step coordinate proof: unique
exponent vectors; infinitude and denominator clearing; a nonzero product;
polynomial evaluation; and transport and cancellation.

Edge cases checked before writing and in the final reading:

- Rank zero: the split torus is the trivial group, there is at most one character,
  and its identity k-point satisfies injectivity on every subset.
- Empty or singleton Ω: the injectivity condition is vacuous and an identity
  k-point exists, so the existence quantifier remains meaningful.
- Positive characteristic, including the algebraic closure of a finite field:
  no characteristic hypothesis occurs. Distinct exponent vectors still give
  a nonzero Laurent difference; a p-th-power difference is not the zero
  polynomial, and an algebraically closed field is infinite.
- Negative exponents: G_m and the group-scheme morphism type retain the Laurent
  interpretation; no restriction to nonnegative exponents is imposed.
- Arbitrary group-scheme presentation isomorphic to the product: hT is an
  isomorphism, not an equality with the chosen model.

Searches on 2026-10-24 (the wrapper also logs exact results in searches.jsonl):

- LeanFinder via `msearch.py`: "Finitely many distinct algebraic characters of a
  split torus over an algebraically closed field take distinct values at one
  rational point". Eight hits: analytic UnitAddTorus separation, Ax-Grothendieck,
  normal bases, finite monoid characters, root pairings, and character modules.
  Read returned signatures; none is this algebraic group-scheme statement.
- Loogle via `msearch.py`: `Grp, IsMonHom, piObj`. No hits; unknown `Grp` in the
  search index. Read the local Mathlib declarations directly instead.
- LeanSearch via `msearch.py`: "Finite distinct algebraic characters of a split
  torus can be separated at one rational point". Eight hits, including analytic
  torus and polynomial-function separation, finite AddChar and separable-field
  facts. These separate points with functions or concern different objects,
  not simultaneous separation of a finite character family by one torus point.
- Mathlib grep via `msearch.py`: `torus|character.*separat|separat.*character`
  in AlgebraicGeometry. Zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: torus, splitTorus, algebraic
  character and character-separation searches found the existing splitTorus
  definition and downstream `TorusRegularSemisimpleElement` proof reference,
  but no existing declaration of the assigned statement. The coherent-torus
  Character abbreviation is an additive alias of the same Mathlib morphism
  type, not a different missing notion. No alias is copied here.
- The item-id search in upstream Lean found no assigned theorem; the upstream
  declaration index likewise has no matching torus-separation declaration.

No node fault or disputed statement was found. Server compilation through
`scompile.py Q69 lem-sfb-torus-finite-character-separation <module>` passed for
both sandbox and final module (1.8 seconds each), with no errors or unexpected
warnings.

## Second reading by Q69

This is the dispatcher's single-worker delivery. No second worker was started,
as the assignment expressly prohibits other agents; this section is an author's
second reading, not a claim of independent review. The maintainer supplies the
independent review.

Reopened the node and final Lean file together. Matched algebraic closedness,
rank (including zero), the group scheme over k, its group-scheme splitting
isomorphism, the finite set of algebraic characters, the single k-point and
injectivity of evaluation as detailed above. In particular, the values are
composites to the actual G_m, not the underlying characters as abstract group
homomorphisms. The `Set.InjOn` condition has precisely the quantifiers over two
members of Ω in the node's pairwise formulation. Neither smoothness nor a
characteristic assumption has been inserted. The landed split-torus node was
added to stmt_deps because its definition is used. No mathematical statement
correction, new node or dependency repair was needed.
