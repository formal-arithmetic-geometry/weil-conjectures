## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen defines
AlgebraicGeometry.AlgebraicSpace.localFibreDimension by the actual supremum over
all affine representable étale charts and their lifts. Its theorem
localFibreDimension_chart_finite_isOpen states exactly the three conclusions of
the node, with a sorry proof. The definition contains no postponed data or proofs.
The node's accepted stage-1 statement, split, and dependencies are preserved.

Hypothesis and clause correspondence:

- A scheme target is the explicit binder `{T : Scheme.{u}}`.
- The morphism from an algebraic space to this scheme is encoded by
  `X : AlgebraicSpace T`. This is the category of algebraic spaces over T; its
  structural map is the given f. No representability of f is imposed. A scheme
  chart has `U : Over T` and `a : yoneda.obj U ⟶ X.obj.obj`, so `U.hom` is the
  composite U → X → T. Encoding the target as the base imposes no condition on f.
- Point classes with atlas topology are the existing `Point X.obj.obj` and
  `pointTopologicalSpace` instance, imported from AlgebraicSpacePointTopology.
- Local finite type on étale scheme charts is precisely hft:
  `∀ (U : Over T) (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a →
  LocallyOfFiniteType U.hom`. This is a substantive finite-type hypothesis,
  not a hypothesis asserting a property of identity morphisms.
- An affine chart at x is indexed in localFibreDimension by U, `IsAffine U.left`,
  a, `IsEtale a`, v, and `schemePointMap a v = x`. IsEtale already includes
  representability by definition; there is no surjectivity restriction on a.
- At such a lift v, t=f(x) is `U.hom v`. Its scheme fibre is
  `U.hom.fiber (U.hom v)`, the canonical residue-field pullback, and the unique
  point above v is `U.hom.asFiber v`. Thus no arbitrary base point, lift, map,
  or algebraically closed field is substituted. The algebraic-space fibre X_t
  in the informal statement is contextual notation, never an extra assumption
  or an additional conclusion; the actual numerical definition uses U_t.
- Local dimension means the existing `topologicalKrullDimAt`, the infimum of
  topological Krull dimensions of open neighbourhoods. Its value type is
  `WithBot ℕ∞`, allowing both empty-space dimension and infinity before the theorem.
- The supremum over all charts is exactly the nested indexed supremum in
  localFibreDimension, including every affine scheme chart in the fixed scheme
  universe. It makes no atlas choice and does not substitute a local-ring dimension.
- The first conjunct asserts equality with that supremum for every x and every
  affine étale chart lift v. The order of IsAffine and IsEtale hypotheses does
  not affect the domain of quantification.
- The second conjunct, `∀ x, ∃ d : ℕ, localFibreDimension X x = (d : WithBot ℕ∞)`,
  says the value is finite and nonnegative at every point. It imposes no uniform bound.
- The third conjunct quantifies `d : ℕ`, equivalently all integers d≥0, and uses
  `IsOpen {x | localFibreDimension X x ≤ (d : WithBot ℕ∞)}` in the existing topology.
- No quasi-compactness, properness, flatness, finite-presentation, or Noetherian
  assumptions occur, either explicitly or as typeclass binders.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom,
  Spec, Spec.map, and the standard category of schemes (def-pc-scheme,
  def-weil-affine-spectrum).
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.IsAlgebraicSpace, IsRepresentableWith, IsRepresentable, IsEtale.
  IsEtale is the scheme-test condition including representability.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses, reexported by
  AlgebraicSpacePointTopology: Point, PointRepresentative.Rel, schemePointMap;
  AlgebraicSpacePointTopology: pointTopologicalSpace, the final topology for all
  representable étale scheme-source maps (def-a1-space-point-topology).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and
  Scheme.Hom.residueFieldMap. The latter is used by the canonical fibre framework,
  rather than by a new residue-field construction.
- Mathlib.AlgebraicGeometry.Fiber: Scheme.Hom.fiber, fiberι,
  fiberToSpecResidueField, fiberHomeo, and asFiber. The definitions were read:
  fiber is the residue-field pullback and asFiber is the inverse fibre homeomorphism.
- WeilConjectures.Mathlib.Topology.KrullDimension: topologicalKrullDimAt;
  Mathlib.Topology.KrullDimension: topologicalKrullDim. Their full definitions
  implement precisely the neighbourhood infimum and irreducible-chain dimension.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback, etale_fibreProduct_isScheme.
  Its module is imported for the existing proof plan, not replaced privately.

Proof-only imports retain every already stated proof dependency: the modules
AlgebraicSpaceAffineEtaleCover (exists_affine_etale_cover_and_point_topology),
AlgebraicSpaceFibreProductPoint (exists_scheme_fibreProduct_point),
ChartwiseEtalePermanence (chartwise_etale_permanence),
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
(exists_topologicalKrullDim_le), and LocalFibreDimensionOpen
(isOpen_localFibreDimension_le). The finite-type base-change input is Mathlib's
locallyOfFiniteType_isStableUnderBaseChange. The existing proof dependency
lem-sfb-etale-topological-dimension-at-point has no Lean record yet; consequently
there is no module to import for it. It is not needed to type this statement and
its future use is explicitly retained in the theorem's complete proof docstring.

Edge cases checked before writing: empty X has no pointwise obligations and its
bounded loci are empty; for any actual point the affine chart family is nonempty
by an atlas refinement. d=0 includes étale zero-dimensional fibres. The definition
permits infinity before the finite-type theorem and permits no global finiteness
assumption. Nonclosed points use topological neighbourhood dimension of the
scheme fibre, not the Krull dimension of the stalk. Non-surjective charts, arbitrary
residue fields, positive characteristic and inseparable structural morphisms are
included. T is arbitrary and need not be affine or Noetherian. All universes and
variables are explicitly bound; no independent small test universe is imposed.

Searches actually run:

- msearch.py leanfinder: "For an algebraic space locally of finite type over a
  scheme local fibre dimension is independent of etale chart finite and its bounded
  dimension locus is open". Eight hits, including Algebra.isOpen_etaleLocus,
  Algebra.etaleLocus and scheme LocallyOfFiniteType.stalkMap. None concerns this
  algebraic-space assertion or defines its chart supremum.
- msearch.py loogle: "topologicalKrullDimAt, AlgebraicSpace, IsOpen".
  Zero hits, with diagnostic "unknown identifier 'topologicalKrullDimAt'";
  this is not evidence that the upstream definition does not exist.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `(localFibreDimension|localFiberDimension|AlgebraicSpace.*[Dd]im|[Dd]im.*AlgebraicSpace)`.
  Zero hits.
- msearch.py leansearch: "For algebraic spaces locally of finite type over a scheme
  the local relative dimension is finite and the bounded dimension locus is open".
  Eight hits: scheme smooth/finite-presentation and LocallyOfFiniteType APIs,
  IsProper.toLocallyOfFiniteType, and Algebra.IsStandardSmooth.relativeDimension.
  None states this assertion or defines the algebraic-space chart supremum.
- rg in lean/WeilConjectures and lean/Sheaf for localFibreDimension,
  localFiberDimension, fibreDimension, fiberDimension, and dimension/chart/fibre
  combinations. Found only the scheme isOpen_localFibreDimension_le and consumers;
  the algebraic-space chart-invariance module concerns stalk dimension, a different
  invariant. No existing declaration gives this theorem or supremum definition.
- grep -rn for the item id in lean/WeilConjectures: no hits.

Sources read: Stacks spaces-morphisms.tex definition-dimension-fibre (04NM),
including its displayed dim_u(U_v) interpretation, and
lemma-openness-bounded-dimension-fibres (04NT), including the étale chart proof.
The item is their stated specialization to a scheme target. No statement fault,
correction, or STATEMENT-DISPUTED flag is needed.

Validation: the prescribed scompile.py compiled the delivered module alone
against the live server build, successfully in both its sandbox and library-name
checks (6.5 and 6.2 seconds); no errors or warnings were printed. Only the named
theorem has a sorry proof. The direct supremum definition needs no missing
notion, new node, or dependency-interface repair.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
