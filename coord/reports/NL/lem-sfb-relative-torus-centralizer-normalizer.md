## Worker report

Statement-only delivery of `lem-sfb-relative-torus-centralizer-normalizer` in
`lean/Sheaf/AlgebraicGeometry/GroupScheme/RelativeTorusCentralizerNormalizer.lean`.
The only postponed theorem is
`AlgebraicGeometry.RelativeTorusCentralizerNormalizer.relative_torus_centralizer_normalizer`.
All helper definitions contain real data or explicit predicates. No node statement,
proof, or proof dependency was changed. Statement dependencies gained published nodes
for the relative split-torus model, Lie construction, relative differentials, finite
local freeness, dual numbers, and the canonical Lie/infinitesimal-point equivalence.

The source was read online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf : Proposition 2.1.2,
printed pp.56--60; Definition 2.2.1 and Lemma 2.2.4, pp.64--66; Remark 2.2.7;
Appendix B.1 and Corollary B.2.7. In particular Proposition 2.1.2 gives the normalizer
as a finitely presented closed subgroup, smooth for a multiplicative-type subgroup
of a smooth ambient group; Lemma 2.2.4 gives the centralizer and its invariant
identity tangent bundle. No field, connectedness, reducedness or Noetherian
assumption is present in the delivered statement.

Hypothesis and clause correspondence:

- An arbitrary base scheme is `{S : Scheme.{u}}`. `G : Grp (Over S)` carries
  multiplication, inverse and identity obeying precisely the group-object diagrams.
  `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
  `LocallyOfFinitePresentation G.X.hom` give smooth affine finite presentation over S.
  An affine morphism is quasi-compact and separated, so no extra quasi-compactness
  hypothesis is needed to turn local finite presentation into finite presentation.
- The nonnegative rank is `r : ℕ`. The torus is the existing
  `(RelativeSplitTorus.model S r).toGrp`, defined by base change of the integral
  Laurent Hopf algebra with character lattice `Fin r → ℤ`. It has the precise
  multiplication on units required by the node; no unspecified torus is introduced.
- The specified closed subgroup immersion is the group morphism `j` and
  `[IsClosedImmersion j.hom.hom.left]`. Bundled group morphisms already preserve
  the group structures.
- `centralizerPoints j W` says, literally, that for all `V : Over S`,
  `a : V ⟶ W` and `t : V ⟶ T.X`, `Commute (a ≫ g) (t ≫ j.hom.hom)`.
  Thus the commuting condition is universal, including nonreduced extensions.
- `normalizerPoints j W` says the image subgroup on every extension V is equal
  to its conjugate under `a ≫ g`. Equality of sets imposes both containments,
  rather than replacing preservation by only one direction or by geometric points.
- The existential groups `C N` and their actual inclusions `iC iN` are closed
  immersions, smooth and affine and locally finitely presented over S. Together
  these are precisely the finite-presentation properties in the node.
  `RepresentsCentralizer j iC` and `RepresentsNormalizer j iN` identify their
  images on all test schemes with C(W) and N(W). These are functorial image
  identifications induced by scheme morphisms, not arbitrary bijections.
- The quantified clause `∀ (B : Scheme.{u}) (b : B ⟶ S), ...` says the pullbacks
  of these same inclusions represent the functors for the pulled-back torus
  inclusion. The torus here is the actual pullback, so an extra arbitrary
  comparison with a split model is unnecessary. This is arbitrary scheme base
  change, including nonflat changes and the identity map.
- `GrpObj.lieAlgebraSheaf G.X` is exactly the existing dual of the identity
  cotangent module `GrpObj.omega G.X = e*Ω`. Its `IsFiniteLocallyFree` conclusion
  is local freeness of finite, possibly varying rank.
- `lieMap iC` is defined using the canonical published `GrpObj.lieEquiv` and
  `GrpObj.infPointsMap`, hence is the actual tangent map, with no chosen linear
  map as a substitute. `Set.range (lieMap iC) = lieInvariants j` is the equality
  inside the actual Lie module. The same equality for every `b : B ⟶ S`
  expresses it on every test base, and thus as the invariant subbundle.
- `lieInvariants` requires the dual-number point to commute with the whole torus
  after every extension of the dual-number scheme. This is equivalently invariance
  under the full adjoint coaction; it does not use the Lie algebra of the torus
  or merely the torus's points over the original ring. Testing the universal
  Laurent algebra extension detects exactly the zero-weight coefficient condition.
- `HasCanonicalLieBaseChange G b` and `HasCanonicalLieBaseChange C b` give the
  cotangent base-change isomorphism sending pulled-back `da` at the identity to
  `d(p-sharp a)` at the pulled-back identity, for every open and section. The
  accompanying Lie-sheaf isomorphism is its dual, fixed by the evaluation-pairing
  equation. Thus base change asserts the canonical comparison, not only existence
  of isomorphic bundles. `HEq` transports across the ordinary equality of the
  two pulled-back identity opens; it does not discard a section condition.
- For each `σ : (Matrix (Fin r) (Fin r) ℤ)ˣ`, the open `U σ` is closed as well;
  `iSup U = ⊤` says these opens cover N. Matrix units are exactly GL_r(ℤ).
  The all-tests criterion `Set.range n.left ⊆ U σ ↔ ... ∈ matrixPoints j σ W`
  characterizes the represented locus, whose conjugation sends units `t_i` to
  `∏ i, t_i ^ σ.val k i`. The coordinate map is the published point equivalence,
  uniquely normalized by pullback of each named Laurent coordinate. Its selection
  from `matrix_sheaf_classification` does not introduce arbitrary data: the theorem's
  coordinate equations determine that equivalence uniquely on every point.
- The final clause uses the actual inverse image under `pullback.fst N.X.hom b`
  of each `U σ`, and the actual adjunction identification of points. It gives
  precisely the same matrix locus after every scheme base change. A point on a
  disconnected test scheme need not have one constant matrix; the opens cover N
  as schemes, and no assertion says their W-points cover all N(W).
- For `r = 0`, `Fin 0` is empty, the Laurent lattice and split torus are trivial,
  matrix units have exactly one element, and all products are empty products.
  The predicates reduce to C=N=G and all tangent vectors are invariant. The
  theorem does not exclude that case or require a positive rank.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, and group morphisms;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `Hom.group`, the group law
  on all test-scheme points. These are the recorded group-scheme notions of
  `def-sc-group-scheme`, used over an arbitrary base as the item explicitly requests.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf`:
  `RelativeSplitTorus.model`, `coordinate`, `matrix_sheaf_classification` and the
  underlying integral Laurent Hopf model. The full theorem and its docstring were read.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`: `unitSection`,
  `omega`, `lieAlgebraSheaf`, `Lie`; publicly supplied through the recorded
  `def-wf-lie-algebra-derivation` module `...Lie.Bracket` as well as
  `...Lie.Functoriality`. The actual Lie module declarations are general in S;
  the later field-specific bracket is not used to restrict the base.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv`:
  `lieEquiv`; `...Lie.InfPoints`: `infPoints`; `...Lie.Functoriality`: `infPointsMap`.
  These and `Scheme.dualNumbersOver` are owned by the new existing-definition node
  `def-sfb-group-scheme-infinitesimal-points`; the unused `lieEquiv_mul` theorem
  is not a statement dependency.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`;
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`. The cotangent sheaf used by upstream Lie
  is definitionally this differential sheaf, as its source explicitly verifies.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`:
  `Scheme.Modules.pullbackUnitApp` and the ordinary module pullback adjunction;
  `...Modules.Dual`: `dualEvaluation`; `...Mathlib.AlgebraicGeometry.Modules.Sheaf`:
  `pullbackObjUnitIso`. These supply the canonical normalization, not new pullbacks.
- `Mathlib.Algebra.DualNumber`: the recorded `DualNumber`; the existing scheme
  version is `Scheme.dualNumbersOver` from upstream `...DualNumbers`.

Proof-dependency imports retained for stage 3:
`WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree`,
`Sheaf.RepresentationTheory.RelativeTorusBundleWeights`,
`Mathlib.RingTheory.FinitePresentation` (kernel finite-generation lemma),
`Mathlib.RingTheory.Kaehler.TensorProduct` (canonical base-change equivalences).
The affine spectrum, group-object and smoothness modules are already public imports.
The genuine proof prerequisite `lem-sfb-split-torus-infinitesimal-conjugacy` has no
recorded Lean module at this reading, so there is no module to import yet. It is
not needed to type this statement; its exact use remains in the theorem docstring.
No downstream theorem was used as a prerequisite for an introduced map.

Searches for existing declarations:

- `msearch.py ... leanfinder "Relative smooth affine group scheme centralizer and
  normalizer of split torus Lie algebra invariants base change"`: eight hits, all
  Lie algebra normalizers or Cartan-subalgebra constructions, no relative scheme theorem.
- `msearch.py ... loogle "GrpObj, centralizer"`: no hits; Loogle reported unknown
  identifier `GrpObj` (that server does not expose this categorical identifier).
- `msearch.py ... grep "centralizer|normalizer|LieAlgebra" AlgebraicGeometry/Group`:
  zero Mathlib hits.
- `msearch.py ... leansearch "scheme group scheme relative Lie algebra sheaf
  centralizer normalizer split torus"`: eight hits, abstract Lie normalizers and
  subgroup normalizers; none states the relative scheme result.
- `rg` in live `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for centralizer, normalizer, relative torus and
  Lie/cotangent names found field-specific centralizers and normalizers and the
  relative split model. Reading their signatures excluded an exact match.
- `grep -rn "lem-sfb-relative-torus-centralizer-normalizer" lean/WeilConjectures`:
  no declaration tagged with this item.
- Reading upstream `GroupScheme/Lie/Basic.lean`, `InfPoints.lean`,
  `InfPointsEquiv.lean`, `Functoriality.lean`, `TangentSpace.lean` and
  `Modules/Dual.lean` located the existing arbitrary-base Lie sheaf and canonical
  tangent description. They are reused, not reconstructed.
- Parsed all DAG Lean records for `lieAlgebraSheaf`/`GrpObj.omega`, and read
  `def-wf-lie-algebra-derivation` and `lem-ag-lie-equivalence-multiplication`.
  `blueprint_refs.py search "relative Lie"` gave no separate definition node.
- Searched the new theorem and helper names in project and Mathlib AG sources:
  no full-name collision. All msearch outputs are logged by the prescribed wrapper.

Edge cases checked before finalizing: empty S, zero-ring affine tests, rank zero,
nonquasi-compact and disconnected bases, nonreduced extensions, positive
characteristic (especially Frobenius weights), the identity base change and arbitrary
nonflat base changes. The normalizer condition uses equality, and the cover is a
scheme cover, so it permits matrix variation on disconnected tests. No hypothesis
adds a chosen trivialization of Lie(G) or a globally constant Lie rank.

Validation: scompile.py compiled the sandbox and the actual module, each in under
five seconds, with no errors or warnings. The expected postponed statement is the
single sorry theorem. No global build or direct repository writes/Git mutations
were performed. No STATEMENT-DISPUTED issue or statement correction is needed.

## Second reading by NL

The dispatcher explicitly forbids starting another agent; this section records an
in-thread second pass, not a fictitious independent worker review. The maintainer
performs the independent review of the delivered statement.

I reopened the node and the completed module and checked all clauses above. The
first version only asserted representation after base change; direct representation
and direct Lie-image equality were then added as well, so consumers need not
transport along identity pullback. A bare existence of Lie-bundle isomorphisms was
replaced by `HasCanonicalLieBaseChange`, normalized on every differential generator
and by the dual evaluation equation. The set-preimage of the matrix open now uses
the actual pullback projection, resolving an elaboration/coercion mismatch. Relative
differentials are publicly imported because the generator formula is part of the
public predicate. No mathematical statement correction was required.

The final statement keeps arbitrary S, all ranks, closed subgroup j, smooth affine
finite presentation, universal C and N, arbitrary-base-change representation,
finite locally free Lie(G), full-torus Lie invariants, clopen matrix pieces, the
cover and its arbitrary-base-change identification. Definitions of the same notion
are helpers in the owning module under the human's missing-helper authorization;
the returned-delivery repair below adds DAG ownership for four existing definitions,
without duplicating them or adding any Lean module.


## New nodes

`def-sfb-group-scheme-infinitesimal-points` records, with `existing: true`,
`AlgebraicGeometry.GrpObj.infPoints`, `AlgebraicGeometry.GrpObj.lieEquiv`,
`AlgebraicGeometry.GrpObj.infPointsMap`, and
`AlgebraicGeometry.Scheme.dualNumbersOver`. The common import is
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Functoriality`; public imports
provide the other three declarations. No new Lean module is needed.

For arbitrary `S : Scheme.{u}` and `G : Over S` with `[GrpObj G]`,
`dualNumbersOver S` is exactly `Over.mk S.dualNumbersProj`; `infPoints G`
is exactly the kernel of precomposition with the zero section. `lieEquiv G`
is `Equiv.ofBijective` of `toLie G`, whose documented formula takes the epsilon
coefficient through the universal property of the relative differential sheaf.
`infPointsMap f`, for `[IsMonHom f]`, is the actual group homomorphism given by
composition with `f`. Every hypothesis and clause of this new definition node
is therefore supplied by the recorded existing declarations. In particular no
smoothness or field restriction was introduced. The definitions apply to empty
bases, nonreduced bases, arbitrary characteristic and the trivial group.

Before adding this node, searched all DAG records for all four full names and
searched the blueprint with `blueprint_refs.py search 'infinitesimal points'`
(zero matches). Existing candidates are theorem nodes or use these definitions;
none records ownership of these four definitions. LeanSearch and LeanFinder
returned eight hits each, concerning algebra extensions, abstract Lie algebras
or manifold groups, not this scheme interface. Mathlib grep over
`AlgebraicGeometry` found zero hits for the four names. Project-source grep
located the exact existing definitions above; Sheaf grep located consumers in
`CharZeroDifferentiationHom` and `AbelDifferentialBoundary`. The unmodified
wrapper search records and project/DAG search outputs are included in the new
node's `mathlib_searches`. This is an existing-definition record, not a private
copy of a definition or a postponed theorem.

## Returned-delivery repair

H2 on immutable head `f9bf51eebeb2`: replaced the added, unused
`lem-ag-lie-equivalence-multiplication` statement dependency with the new
definition node `def-sfb-group-scheme-infinitesimal-points`, owning all four
interfaces requested in the return. Retained
`lem-sfb-relative-split-torus-matrix-sheaf`: the maintainer accepted the uniquely
normalized coordinate choice. No item statement, proof, proof dependency or
Lean declaration changed. Compared the retained sandbox against current main:
only `lean` and the authorized added `stmt_deps` differ. All other current-main
node fields are retained.

Second reading of the repair reopened the four upstream docstrings, signatures
and definition bodies. The new node describes their exact kernel, coefficient
map, composition map and over-base dual-number object, without relying on
`lieEquiv_mul`. The previously reviewed Lean source remains byte-identical,
SHA-256 `cfbcac0d0452991cf75385e2ba3325f16eec8d06bca818077528ca491cf96909`.
The maintainer's return independently accepted the mathematical statement
clause by clause, including arbitrary base changes and the stated edge cases.

The first repair dry run required the primary declaration to be declared directly
in its recorded module, so the new node uses `infPointsMap` as primary and
retains all four names in `lean.declarations`. The recorded module remains
`...Lie.Functoriality`, as the return requests.
