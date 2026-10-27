## Worker report

The module `Sheaf.AlgebraicGeometry.MultiplicativeTypeFibralCriterion` states
`AlgebraicGeometry.multiplicativeType_fibral_criterion`, with its only proof `sorry`.
It adds no definitions and preserves the node's statement and proof plan.
Conrad's original Theorem B.4.1 and the opening of B.4 were read online in
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.297--299.
The source does not assume commutativity; its power-map identity fibre is explicitly
used before commutativity is established. The source's sufficiency proof and the node's
seven-step refinement are included in the theorem docstring.

Clause-by-clause correspondence:

- The scheme S is `S : Scheme.{u}`. The S-group scheme is `G : Grp (Over S)`;
  its group-object structure includes multiplication, identity and inverse and their
  diagrams, with no `IsCommMonObj` assumption.
- Affineness and flatness are `[IsAffineHom G.X.hom]` and `[Flat G.X.hom]`.
  Finite presentation is exactly the three explicit assumptions
  `[LocallyOfFinitePresentation G.X.hom]`, `[QuasiCompact G.X.hom]`,
  `[QuasiSeparated G.X.hom]`. The last two also follow from affineness; they are
  retained because the node writes them out as its finite-presentation convention.
- The residue-field fibre at s is the underlying object of
  `(Over.pullback (S.fromSpecResidueField s)).mapGrp.obj G`.
  `mapGrp` transports the actual group law by the finite-product-preserving pullback
  functor, rather than choosing an unrelated structure on the fibre product.
- For each natural integer `n` with `1 < n`, `torsionSubgroupScheme ... n` is the
  upstream construction `GrpObj.ker (𝟙 G ^ n)`, the scheme-theoretic identity inverse
  image. Its definition requires only `GrpObj`, not commutativity or `IsMonHom`
  for the power map. Natural n > 1 are exactly the positive integer indices in the node.
- Hypothesis (a) is `hgeom`: for every s it existentially binds Ω, `Field Ω`,
  `IsAlgClosed Ω`, `Algebra (S.residueField s) Ω`, M, `AddCommGroup M`, and
  `AddGroup.FG M`, and a `Nonempty` isomorphism of bundled group schemes from the
  specified base change to `ringDiagonalizableGroup Ω M`. The structure map is
  `Spec.map (CommRingCat.ofHom (algebraMap ... Ω)) ≫ S.fromSpecResidueField s`.
  There is no `IsAlgClosure` or algebraicity assumption on Ω.
- The finiteness clause of (b) is `hfinite`, for every n > 1 and every s, using
  `IsFinite` on the structure morphism of the actual torsion scheme.
- The order is that morphism's `finrankΓ`, the upstream definition of the dimension
  of global sections over the residue field using its canonical Γ-algebra structure.
  `horders` says for each n > 1 and d : ℕ that its level set is open. This is exactly
  the node's stated meaning of locally constant, with each n treated separately.
- The conclusion gives an index type I (not required nonempty), rings R i, morphisms
  `f i : Spec (R i) ⟶ S`, and membership of their `Presieve.ofArrows` in the recorded
  `Scheme.fppfPrecoverage S`. By the definition of this precoverage these are flat,
  locally finitely presented and jointly surjective, exactly the required covering.
  For each i it gives a finitely generated additive abelian group N and an
  isomorphism of group schemes of the actual pullback to `ringDiagonalizableGroup (R i) N`.
  The affine members express the same existence condition as arbitrary U_a:
  refine any splitting family by all affine open charts of its U_a, restricting the
  given group isomorphism; on each affine chart the node's glued D_U(N) is D_R(N).
  Conversely the displayed family is already a family of U_a of the required kind.
  This is an equivalent encoding of local splitting, not a new hypothesis or a
  correction to the node. It avoids duplicating D_R or introducing hollow gluing data.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its documented stalkwise equivalence.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` / `QuasiSeparated`: the two
  classes required by `def-weil-pbc-scheme-conventions`, a convention node with no own module.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  underlying the canonical `Over.pullback` functor.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; only algebraic closedness
  from the algebraic-closure dependency is needed, as the node explicitly allows
  nonalgebraic extensions.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`: `ringDiagonalizableGroup`,
  constructed by `hopfSpec` from `AddMonoidAlgebra`, with the exact prescribed Hopf maps.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` (the recorded
  declaration alongside `Scheme.fppfTopology`).
- Added the already recorded dependency `def-sc-mult-n`, whose current blueprint
  statement explicitly permits arbitrary group schemes and n ≥ 0:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.torsionSubgroupScheme`
  (declaration namespace `AlgebraicGeometry`), using its generalized upstream signature.
  No dependency record or source file was modified.
- The same upstream module imports `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  whose `Scheme.Hom.finrankΓ` is used for the dimension.
- Plain proof imports include the recorded strict henselization and its local-structure
  theorem, finite abelian group structure, common extension fields, finite-presentation
  colimit descent, and the directed-index reindexing module. The recorded affine
  tensor-product, closed/open-immersion and etale-composition interfaces are already
  transitively imported. The clopen-lift and diagonalizable-geometric-criteria proof
  nodes currently have no recorded modules and therefore supply no import yet.

Edge cases checked: the empty base admits the empty family I, since joint surjectivity
is then vacuous. The trivial group is M = 0 and its torsion length is 1. In positive
characteristic, nonreduced μ_p is included by scheme-theoretic identity fibres and
coordinate dimensions, not rational-point counts. Disconnected, nonreduced and
non-Noetherian bases are allowed; no reducedness, connectedness or smoothness class
is bound. The condition is required for every n > 1 without any prime restriction.
All objects and all existential extension fields live in the same universe u as S;
there is no independently smaller test-object universe and no universal test-algebra
quantifier. An arbitrary large splitting extension yields a small algebraically closed
splitting extension by the extension-independence stated at the opening of Conrad B.4.
Finitely generated groups can likewise be represented in u. A cover indexed in u
exists since S has u-small points and affine neighbourhoods suffice.

Searches for existing declarations:

- `msearch.py ... leanfinder`: “An affine flat finitely presented group scheme with
  diagonalizable geometric fibres and locally constant orders of all n torsion is fppf
  locally diagonalizable”. Eight hits about ordinary affine morphism properties and
  diagonals; no multiplicative-type criterion.
- `msearch.py ... loogle '"diagonalizable"'`: zero hits.
- `msearch.py ... grep 'multiplicativeType|MultiplicativeType|Diagonalizable|torsionSubscheme|powMap'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures` found the exact reusable torsion scheme construction;
  the item id has no upstream theorem match. `rg` on `lean/Sheaf` found ring and field
  diagonalizable groups and field-only multiplicative-type predicates, but no relative
  fibral criterion. The field-only definitions are not substituted for the arbitrary-base
  fppf conclusion. The recorded ring construction is used directly.
- `tools/blueprint_refs.py search 'multiplicative type'`: zero matches.
  DAG searches found the relative fpqc-descent consumer, the strict-local clopen-lift
  proof prerequisite and field-only multiplicative-type statements, not a duplicate.

No statement fault or disputed assertion was found. The withdrawn CompactObject example
module currently has no declarations; its node record and the explicit stage-2 conventions
were read, and this module follows the live `module` / `public import` / exposed-section form.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
