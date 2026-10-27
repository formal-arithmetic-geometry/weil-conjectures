## Worker report

The module `Sheaf.AlgebraicGeometry.CubicalAmpleNormReflection` states
`AlgebraicGeometry.CubicalRigidifiedLine.isAmple_of_isAmple_inversionNorm`.
Its only proof is `sorry`. There are no new definitions, dependency repairs,
statement corrections, or changes to the accepted split.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. `[IsIntegral S]` includes nonemptiness,
  reducedness and irreducibility. `[IsNoetherian S]` is Mathlib's conjunction of
  local Noetherianness and quasi-compactness. `[IsAffine S]` imposes affineness.
- Normality is exactly `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`. This is the stipulated local-ring
  condition, using the recorded normal-domain notions without a new predicate.
- The structure morphism is `G.hom` for `G : Over S`. `[CommGrpObj G]` is the
  existing class abbreviation for `GrpObj G` and `IsCommMonObj G`. Its actual
  multiplication, unit and inverse are morphisms in `Over S`, hence S-morphisms,
  with the associativity, unit, inverse and commutativity equations in the classes.
  Inversion is `(ι[G]).left`, not a freely supplied endomorphism.
- Smoothness and separation are `[Smooth G.hom]` and `[IsSeparated G.hom]`.
  Mathlib's separation class is exactly closed immersion of the fibre-product
  diagonal. Finite presentation is `[LocallyOfFinitePresentation G.hom]` and
  `[QuasiCompact G.hom]`, together with quasi-separatedness supplied by separation.
  Thus this is finite presentation, rather than merely local finite presentation.
- `hG : HasSemiabelianGeometricFibres (Grp.mk G)` uses the given group law.
  The definition quantifies over all algebraically closed fields and geometric
  points in the scheme universe, with an abelian-variety quotient, an arbitrary
  finite-rank split torus as scheme-theoretic kernel, and fppf local surjectivity.
- `P : CubicalRigidifiedLine G` carries the module `P.line`, its rank-one local
  freeness proof `P.invertible`, identity rigidification, the exact eight-factor
  cube trivialization, and its symmetry, identity-slice and cocycle conditions.
- The line N is written out as
  `P.line ⊗ (Scheme.Modules.tensorPullback (ι[G]).left).obj P.line`.
  Thus it is exactly the supplied global inversion norm. `⊗` is the existing
  sheaf tensor, and `tensorPullback` is the actual tensor inverse image.
- `hN` says this module is ample on `G.left`. The existential `h` only binds its
  invertibility proof, which the type of `IsAmple` requires. It neither chooses
  module data nor assumes any extra geometry: invertibility of this tensor
  follows already from `P.invertible` and `invertible_pullback_tensor`. The
  ampleness proposition is independent of its proof argument by proof
  irrelevance. This witness form avoids local instances or hidden lets in the
  signature. It uses the same full-scheme affine-section-locus criterion as the
  recorded ampleness definition, never a fibrewise criterion.
- The conclusion `@Scheme.Modules.IsAmple G.left P.line P.invertible` is
  absolute ampleness of P on the whole group scheme. No generic-fibre extension
  or residue-field-only conclusion has been introduced.

Recorded dependencies read and used (some imported transitively):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, applied to the actual local rings.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, supplemented by `QuasiCompact` and separation.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.mk`, `GrpObj.inv`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_`: `CommGrpObj`.
  These specialize the recorded general group-object API to `Over S`, as
  documented also in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`:
  `AlgebraicGeometry.CubicalRigidifiedLine` and all its defining fields.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and its module tensor structure.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, through the cubical
  module: the recorded section-normalized tensor inverse image, whose underlying
  `tensorPullback` is publicly imported from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, through the
  cubical module: the recorded existing sheaf tensor infrastructure. No tensor
  construction is duplicated.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  projections, used by the supplied group and semiabelian-fibre interfaces.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  used in `IsSeparated` from `Mathlib.AlgebraicGeometry.Morphisms.Separated`.

Proof dependencies with recorded Lean modules are plain imports:
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and
`WeilConjectures.AlgebraicGeometry.AmplePullback`. The ampleness definition is
already a public statement import. The antisymmetric-frame-extension and
semiabelian-Gm-extension-reflection nodes currently have no Lean record; their
future use is included explicitly in the full five-step proof docstring. They
are proof inputs, not missing notions needed to type this statement.

Edge cases checked before writing:

- The empty base is excluded exactly by integrality, not by an additional binder.
  The identity over a nonempty base forces a nonempty group scheme.
- Rank-zero torus fibres and purely abelian fibres remain allowed by the existing
  semiabelian definition. There is no rank, dimension or characteristic bound.
- The trivial group over S is included. An invertible sheaf on the affine base
  is ample, so the assertion remains compatible with this case.
- Over a field the normal, integral, Noetherian, affine assumptions have their
  expected specialization. For an abelian variety the familiar symmetrization
  criterion is retained; for an affine torus all invertible lines are ample.
- Cubical data and rigidifications are retained even though only the underlying
  line appears in the positivity conclusion. No symmetric-line assumption is
  added, and inversion is not replaced by multiplication by a fixed integer.
- No extra universe equality is imposed: all schemes and geometric fibres use
  the universe of the recorded scheme and semiabelian interfaces.

Searches for an existing declaration:

- `msearch.py ... leanfinder "An invertible cubical rigidified line on a smooth
  semiabelian group scheme is ample if its inversion norm is ample"`: eight
  results, chiefly `AmpleSet.image_iff`, `AmpleSet.preimage`, `AmpleSet.image`,
  `AmpleSet.preimage_iff`, `ampleSet_univ`, `AffineSpace.instIsAffine`,
  `AmpleSet.vadd_iff`, and an elliptic-curve fractional-ideal identity. Their
  returned types concern convex ample sets, affine space, or ideals; none is
  this line-module theorem.
- `msearch.py ... loogle "IsAmple, cubical, inversion"`: zero hits;
  `IsAmple` is not in the service's Mathlib index.
- `msearch.py ... grep "cubical|cubist|ample.*inversion|inversion.*ample"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `norm.reflection|normReflection|[Ii]sAmple.*[Cc]ub|[Cc]ub.*[Aa]mple` and the
  full item id: no matching existing theorem. Inspection of the actual cubical,
  semiabelian, ample and pullback modules supplies precisely the existing notions.

Source limitation retained from the node: this is an explicitly agent-formulated
input, not a claimed numbered Raynaud theorem. The original Raynaud ampleness
chapters and the supporting relative quotient assertion remain marked WANTED in
its source/proof metadata. No source claim, statement, proof plan or dependency
has been changed. No STATEMENT-DISPUTED issue was identified in these checks.

Validation: `scompile.py` compiled both the sandbox and final module names cleanly
on the server. The sole postponed theorem is the named item theorem above.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
