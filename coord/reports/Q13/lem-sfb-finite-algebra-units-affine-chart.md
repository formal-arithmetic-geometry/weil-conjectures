## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteAlgebraUnitsAffineChart` states
`AlgebraicGeometry.FiniteAlgebraUnits.affineChart`, with proof `sorry`. Its four
helper definitions give the actual multiplication matrix, determinant polynomial,
principal open, and that open as an object of `Over (Spec k)`. All four have real
data; no representing scheme or comparison map is chosen from an existence axiom.
These are the specific constructions introduced by this lemma, not new independent
notions. No additional DAG node or dependency repair is needed. The original
statement and dependency lists are unchanged.

I read Milne, Algebraic Groups (2017), Proposition 12.60 and proof, printed p.250
(PDF extraction including pp.250–251), and the node's full six-step proof. The
source's phrase “norm ... is nonzero” must mean invertible when evaluating on
arbitrary algebras, as the existing node already explicitly records. For example,
for A=k and R=k×k, the element (1,0) is nonzero but not invertible. The Lean uses
`IsUnit`, so this inherited source error is already resolved without a new
statement correction.

Hypotheses and clauses, in the order of the node:

- The field is `{k : Type u} [Field k]`. The commutative k-algebra is
  `{A : Type u} [CommRing A] [Algebra k A]`. Nonzero and finite dimensional are
  `[Nontrivial A] [FiniteDimensional k A]` on `affineChart`.
- The basis and positive dimension are `e : Module.Basis (Fin d) k A` and
  `hd : 0 < d`. Indexing by `Fin d` is the relabelling of 1,...,d by 0,...,d−1.
- The structure constants are `e.repr (e i * e j) h`. Uniqueness of basis
  coordinates identifies these with every family c_hij satisfying the displayed
  expansion in the node; there is no extra assumption on these constants.
- The polynomial algebra is `MvPolynomial (Fin d) k`.
  `multiplicationMatrix e h j` is the exact finite sum
  `∑ i, MvPolynomial.C (e.repr (e i * e j) h) * MvPolynomial.X i`.
  `normPolynomial e` is `(multiplicationMatrix e).det`, using `Matrix.det`.
- `openSubset e` is `PrimeSpectrum.basicOpen (normPolynomial e)` in the
  polynomial spectrum. Its points are precisely the primes not containing N.
  `chart e` is `Over.mk` of the open inclusion followed by the spectrum of the
  constants inclusion. Thus its left scheme is exactly U, with the specified
  k-structure. This is the affine-base polynomial-spectrum presentation of
  affine space in `def-sbc-affine-space`; `AffineSpace.SpecIso` supplies that
  presentation (with universe-lifted coordinate indices and their renaming).
  `IsAffine (chart e).left` records that this principal open is affine.
- “For every commutative k-algebra R” is `R : CommAlgCat.{u} k`. An R-point is
  the actual morphism in `Over (Spec k)` from `(Spec R).asOver (Spec k)` to
  `chart e`. This is exactly Hom_k(Spec R,U), not an arbitrary function from R.
  One common, arbitrary universe is used for the field, algebras, and schemes;
  in particular the test algebra universe is not smaller than the base's.
- The witness `E R` is an equivalence from these R-points to
  `{a : Fin d → R // IsUnit (MvPolynomial.aeval a (normPolynomial e))}`.
  Its evaluation characterization is the first conjunct after E,V:
  `p.left ≫ (openSubset e).ι = Spec.map (ofHom (aeval (E R p).val).toRingHom)`.
  This forces the specific evaluation coordinates, rather than allowing an
  arbitrary set bijection. Equivalence inverse laws give the inverse evaluation
  description of every tuple where N is a unit.
- `V R` is an equivalence from exactly these tuples to `(A ⊗[k] R)ˣ`.
  The next conjunct fixes its value as
  `(V R a : A ⊗[k] R) = ∑ i, (e i) ⊗ₜ[k] (a.val i)`.
  Hence the composite `V R (E R p)` is the precise rule in the node.
- Naturality of E is the equality of coordinate functions after precomposition
  with `Spec φ`; naturality of V is equality in the unit group after the map
  `Algebra.TensorProduct.map (AlgHom.id k A) φ.hom`. The tuple b in this
  clause is any tuple whose coordinates are φ(a_i). Such a tuple always exists
  because algebra maps carry units to units and commute with polynomial
  evaluation. Thus the implication formulation of this equality drops no map
  and no test algebra. Naturality of the inverse maps follows from E,V being
  equivalences, so the composite equivalence is natural in both directions.
- An arbitrary affine k-scheme P is `P : Over (Spec (.of k))` with
  `[IsAffine P.left]`. The given `β R` are equivalences between P(R) and the
  tensor units, and their naturality hypothesis uses the same Spec and tensor
  maps. The result `∃ ι : chart e ≅ P` is an isomorphism in the category of
  k-schemes, not merely an underlying-scheme isomorphism. Its displayed equation
  `β R (p ≫ ι.hom) = V R (E R p)` says that this very isomorphism induces the
  given point bijections.
- The clause about any expansion of 1 is rendered literally as
  `∀ b : Fin d → k, (∑ i, b i • e i) = 1 → aeval b (normPolynomial e) = 1`.
  `Nonempty (chart e).left` is nonemptiness of the underlying topological space,
  stronger than just nonemptiness of an unrelated set of tuples and exactly
  the geometric nonemptiness in the node.
- No separability, reducedness, algebraic closedness, or characteristic
  hypothesis occurs. There is no nontriviality condition on a test algebra R.

Dependency declarations and source interfaces read:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, definition at line 180.
- `def-weil-pbc-algebra-hom-quotient`: `Algebra` in
  Mathlib.Algebra.Algebra.Defs, line 95, and `AlgHom` in
  Mathlib.Algebra.Algebra.Hom, lines 30–33. Only the algebra and algebra-map
  portions of this multi-clause dependency are used by this node.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs, lines 73–76.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  Mathlib.Algebra.MvPolynomial.Basic, lines 80–83; `MvPolynomial.aeval`,
  Mathlib.Algebra.MvPolynomial.Eval, lines 591–594; and `algHom_ext`,
  Mathlib.Algebra.MvPolynomial.Basic, lines 431–438.
- `def-weil-pbc-matrix-determinant`: `Matrix.det` and `det_apply`,
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic, lines 59–64.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, lines 469–480.
- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace`,
  Mathlib.AlgebraicGeometry.AffineSpace, lines 41–45; its structure projection
  at lines 65–67 and `AffineSpace.SpecIso` at lines 227–232 identify the
  polynomial-spectrum realization used here. `SpecIso_inv_over` at lines
  253–256 identifies its constants inclusion.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  Mathlib.AlgebraicGeometry.OpenImmersion, lines 34–39. The open inclusion is
  Mathlib's actual `Scheme.Opens.ι`, and its target is that recorded spectrum.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, and `ext`, Mathlib.RingTheory.TensorProduct.Basic, lines
  478–480, 155–157, 311–312, 323–327, and 353–356; `productMap` and
  `productMap_apply_tmul`, Mathlib.RingTheory.TensorProduct.Maps, lines
  803–816. The actual tensor product and its canonical map under φ are used,
  with the latter's signature read at Maps lines 540–549.

I also read the records of every proof dependency, including the upstream
`Matrix.scalar_left_inverse_maximal_minors` declaration and proof docstring
in WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors. Its module is an
ordinary proof-only import. The other proof-only imports provide the basic-open
residue/localization interface, `Module.Basis.baseChange`, localization lifting,
adjugate identities, and `CategoryTheory.Coyoneda.fullyFaithful`. All six proof
steps, with their dependency node names, are in the theorem docstring.

Edge cases checked before writing:

- A=k, d=1: M=x, N=x, and the tuple map is the usual G_m functor.
- A=k×k in the product basis: N=x₀x₁. Its unit locus gives a pair of units
  over every commutative R, including rings with zero divisors.
- A=k[ε]/(ε²), basis (1,ε): M has diagonal entries x₀ and N=x₀².
  Its unit condition is exactly that the constant term be a unit. Thus a
  nonreduced A and a nonreduced R are both covered.
- R the zero ring: 0=1 is a unit, the tuple subset and tensor-unit group are
  singletons, and Spec R is empty, with its unique morphism into U. Every
  equivalence and naturality clause remains meaningful and true.
- Every field characteristic and inseparable algebra is allowed; no denominator
  or separability argument is present. Finite fields still give the identity
  point, so nonemptiness does not use density of rational points.
- d=0 and zero A are excluded exactly by the hypotheses in the node; no
  additional cases are excluded. For arbitrary b expanding 1, basis uniqueness
  makes its coordinates canonical and multiplication by 1 is the identity.
- The comparison tests all commutative k-algebras, not just fields or reduced
  algebras. Thus the affine co-Yoneda step has the correct test category.

Searches performed in this session, through the prescribed msearch wrapper:

- LeanFinder: “The units of a finite dimensional commutative algebra are
  represented by the determinant principal open subset of affine space”.
  Eight hits, including `LinearMap.isUnit_iff_isUnit_det`,
  `FiniteDimensional.isUnit` and smooth-locus statements. None represents the
  unit functor or specifies the natural affine-chart maps.
- Loogle: `Algebra.norm, IsUnit`. Zero hits.
- Mathlib grep: `isUnit_iff_isUnit_det|Spec_basicOpen|units.*[Ss]cheme`.
  Hits include `Matrix.isUnit_iff_isUnit_det`, `LinearMap.isUnit_iff_isUnit_det`
  and `IsAffineOpen.Spec_basicOpen`. They are ingredients, not this statement.
- LeanSearch: “A finite free commutative algebra has a scheme of units given by
  the open where the determinant of multiplication is invertible”. Eight
  determinant-invertibility hits, no full statement.
- Local rg over `lean/Sheaf` and `lean/WeilConjectures` for unit schemes,
  affine units, and finite-algebra units found sheaf/unit comparison modules,
  no representation of this functor. The prescribed literal node-id grep
  over WeilConjectures and the node-id search in dag/lean_names_upstream.json
  returned no hit. A subsequent search for `unitChart|normPolynomial|namespace
  FiniteAlgebraUnits` over both libraries and Mathlib found unrelated formal
  monoid unit charts, and no duplicate of these declaration names.
- Source searches identified existing `AlgebraicGeometry.points` in the group
  Lie-algebra framework. The module therefore writes point sets directly as
  morphisms in `Over`, and does not introduce a second definition of points.

The server compile through scompile.py succeeded with no warnings or errors
for the initial complete module (2.1 seconds for both sandbox and final-path
compiles). A subsequent final compile/dry-run validates the literal arbitrary-b
identity clause and the final import list. No statement is disputed.

## Second reading by Q13

This is a second pass by the same dispatcher worker, as this assignment
explicitly forbids starting another agent. The maintainer supplies the
independent review; no independent worker review is claimed here.

I reopened the node and final Lean file and compared the binders and each
conjunct. The field, nonzero commutative finite algebra, basis and d≥1 match.
The basis repr fixes the very c_hij in the statement; the determinant and
basicOpen constructions use them with exactly the specified row/column order.
The chosen k-structure uses the constants inclusion, so all morphisms in Over
are genuinely k-morphisms. E's equality with Spec of evaluation prevents an
unconstrained coordinate identification. V's value equality enforces the
required sum of pure tensors. Both naturality clauses use arbitrary algebra
homomorphisms and include zero and nonreduced rings. The affine P comparison
preserves its given β on points and is an isomorphism over k. Finally the b
clause has precisely the source's expansion hypothesis and the conclusion 1,
and Nonempty refers to the open scheme itself.

The only refinement found in this second pass was that the initial identity
clause used the canonical coordinates `e.repr 1`. It was equivalent by basis
uniqueness, but I replaced it by the literal universally quantified b with its
expansion hypothesis, to make the source comparison direct. I also made the
recorded statement-dependency imports explicit. No node text, definition,
mathematical hypothesis, or conclusion was changed.

Final verification: the final module compiled cleanly through scompile.py. The first
dry run found only a metadata delimiter mismatch: lean.statement included the
proof-opening :=. I removed that delimiter from the recorded signature to match
the preflight signature convention; no Lean source or mathematics changed.
