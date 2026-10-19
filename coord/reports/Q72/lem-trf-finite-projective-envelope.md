## Worker report

The module `lean/Sheaf/TraceFormula/FiniteProjectiveEnvelope.lean` states
`AlgebraicGeometry.exists_finite_projective_envelope`. It introduces schemes
`B` and `T` in one universe, the affine-base hypothesis `[IsAffine B]`, a natural
number `d` (so the source condition `d >= 0` is represented without excluding any
case), and a morphism
`h : T ⟶ 𝔸(ULift.{u} (Fin d); B)` with `[IsFinite h]`.
The conclusion is the existential triple `(P, j, p)` with `P : Scheme`,
`j : T ⟶ P`, and `p : P ⟶ B`, followed by exactly these conjuncts:

* `IsOpenImmersion j` renders the open immersion `j : T ↪ P`;
* `IsProjective p` renders projectivity in the H-projective and quasi-compact
  convention of `def-pc-projective-morphism`;
* `IsProper p` renders properness of `p`;
* `j ≫ p = h ≫ (𝔸(ULift.{u} (Fin d); B) ↘ B)` says that the composite is the
  given structural morphism of `T` over `B`;
* `∀ b : B, topologicalKrullDim (p.fiber b) ≤ (d : WithBot ℕ∞)` renders the
  bound on every scheme-theoretic fibre, including the empty-fibre bottom case.

The statement dependencies and declarations used are:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
* `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.AffineScheme`,
  with the affine scheme predicate `IsAffine` (and `Spec` available);
* `def-nagata-relative-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace`;
* `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`;
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`;
* `def-pc-projective-morphism`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` (built from `IsHProjective` and `QuasiCompact`);
* `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`;
* `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`;
* `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`.

The theorem docstring records all six proof stages. It uses the standard projective
charts, affine-chart quasi-compactness and the quasi-compact-open permanence lemma
in stage 1; finite-map affine and quasi-finite facts, finite-type composition, and
both readings of quasi-finiteness in stage 2; Zariski main factorization, finite-map
properness and proper-composition in stage 3; ample invertibility, finite-map
projective-bundle projectivity, conversion to H-projectivity, and H-projective
composition in stage 4; finite base change, residue-field projective charts and
finite affine-chart algebras in stage 5; and the polynomial-algebra dimension bound,
scheme sobriety, and the open-cover dimension bound in stage 6.

Edge cases checked against the source statement and its reviewed split are `d = 0`,
empty `T`, empty fibres (dimension `-∞`), non-dominant finite maps, zero algebras,
non-surjective finite maps, and an arbitrary non-Noetherian affine base. No
Noetherian, surjectivity, finite-presentation, or nonempty-fibre hypothesis was added.

Searches made before writing:

* `msearch.py ... leanfinder "finite morphism to affine d-space admits projective
  compactification with fibre dimension at most d"`: returned Proj properness,
  affine-space, and finite-morphism declarations, with no envelope theorem.
* `msearch.py ... loogle "IsFinite, IsProjective, topologicalKrullDim"`: the
  service returned `unknown identifier IsFinite` and zero hits (unavailable for
  this query).
* `msearch.py ... grep "projective.*envelope|finite.*projective|compactification"
  AlgebraicGeometry`: zero hits.
* `msearch.py ... leanfinder "finite scheme over affine space open immersion into
  projective scheme fibre dimension bound"`: returned only affine-space and Proj
  infrastructure, with no matching theorem.
* `msearch.py ... grep "finite.*projective.*envelope|projective.*compactification"
  WeilConjectures`: zero hits.
* `rg` over the source `WeilConjectures/` and project `lean/Sheaf/` for
  `exists_finite_projective_envelope`, `finite_projective_envelope`, and the
  corresponding plain-language phrases found no existing declaration.
* `grep -rn "lem-trf-finite-projective-envelope"` in the source checkout found no
  upstream declaration.

The source location is Orgogozo, Proposition 2.3, proof, printed page 4 of the
28-page author version named by the node. The module has no local copy of that PDF;
the node's `proof_origin` and WANTED note are retained. There are no new definition
nodes, dependency modules, statement corrections, or disputed clauses.

## Second reading by Q06

I reopened the node and the module and checked the signature clause by clause. The
hypothesis `[IsAffine B]` is exactly the affine-base condition; `d : ℕ` covers every
nonnegative integer; `h` has the exact relative affine-space codomain and
`[IsFinite h]` is the finite-morphism hypothesis. The existential objects have the
same types as the node. The three property conjuncts render open immersion,
projective, and proper respectively. The fourth conjunct has the correct category
composition orientation and the canonical affine-space structural map. The final
universal quantifier ranges over all points of `B`, and `p.fiber b` is the recorded
scheme-theoretic fibre with the `WithBot ℕ∞` dimension comparison. No mismatch was
found and no change was needed in this second reading.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
