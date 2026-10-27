## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativePerfectFibreCriterion` states
`AlgebraicGeometry.AlgebraicSpace.relativePerfect_iff_locally_boundedBelow_fibres`,
with `sorry` as its entire proof. Three data-only helpers implement exactly the
residue-field map, fibre and inclusion introduced in the item. No other theorem
is introduced and no mathematical claim is proved.

Read the complete assigned node, each original statement dependency and its
recorded declaration/docstring, the existing space pseudo-coherence, derived
module, tensor-pullback, morphism-property and relative-perfection interfaces,
Stacks `spaces-more-morphisms.tex`, lemma-bounded-on-fibres (Tag 0GFK), and the
current blueprint direct-images proof. The Stacks statement agrees with the
node; there is no mathematical correction, disputed statement or changed proof.
The withdrawn CompactObject example was read together with its current node,
which redirects to `WeilConjectures.CategoryTheory.CompactObject`.

### Hypotheses and clauses

- Size convention: `universe u w wF`; `Scheme.{u}`, space small ringed models
  with section universe `u`, and arbitrary independent derived localization
  universes `w` and `wF`. Every variable and universe is explicitly bound;
  `autoImplicit` is disabled. The two `HasDerivedCategory` binders implement
  the stipulated existence/size convention, and require no equality of site
  and derived morphism universes.
- Scheme S and space X over it: `S : Over B`, `X : AlgebraicSpace B`,
  `f : X ⟶ schemeSpace S`. `B` is only an auxiliary common ambient scheme
  for the existing fppf-sheaf representation. It adds no restriction: take
  `B = S` and `S = Over.mk (𝟙 B)` for the literal source formulation.
  The generalized over-B version retains exactly the same map X → S.left.
- Flat and locally finitely presented f: `hf : MapIsFlat f` and
  `hfp : MapIsLocallyOfFinitePresentation f`. These are the existing
  predicates testing compatible étale scheme charts, not a vacuous identity
  morphism condition or a representability assumption on f.
- `K ∈ D_QCoh(O_X)`: `K : X.DerivedModules` and
  `hqc : X.derivedQCohProperty K`. The existing predicate tests
  quasi-coherence of every cohomology sheaf in the original module topos.
- Pseudo-coherence: `hpc : X.IsPseudoCoherent K`, the already landed
  covering-sieve definition with bounded-above finite-free local models.
- Each point s: `s : S.left`, ranging over every underlying scheme point,
  not only closed or geometric points. `residueFieldSpaceMap S s` is the
  represented map induced by Mathlib's `S.left.fromSpecResidueField s`,
  with the given composite to B.
- `X_s`: `residueFibre S f s` abbreviates
  `enlargedFibreProduct f (residueFieldSpaceMap S s)`. This is the actual
  fppf sheaf fibre product, bundled by the existing algebraic-space proof.
- `i_s`: `residueFibreInclusion S f s` abbreviates the existing actual
  first projection `enlargedFibreProductFst`. The helpers never choose an
  arbitrary map, replacement fibre, or data from an existence-only theorem.
- `Li_s^* K`: `(derivedTensorPullback (residueFibreInclusion S f s)).obj K`,
  using the canonical total left derived ordinary tensor pullback; its
  interface is computed on K-flat resolutions. All fibre derived categories
  are explicitly available in the independent universe `wF`.
- Condition (i), lower bound for K: the first parenthesized `∀ V, ∃ T`
  chooses a covering sieve on each small étale model object. On each member
  U there exists `c : ℤ` such that for all `n < c` the restriction of
  `H^n(K)` by `SheafOfModules.overFunctor` is `IsZero`. This is exactly
  local cohomological boundedness below, as already expressed inline in
  `pseudoCoherent_rhom_quasiCoherent`; it does not require global bounds.
- Condition (i), each derived fibre: the conjunct beginning `∀ s : S.left`
  repeats that same local cohomology-vanishing formula for the actual
  derived pullback on X_s. Every s and every covering member has its own c.
- Condition (ii): `IsPerfectRelativeToScheme S f K` uses the existing
  affine étale chart criterion, namely quasi-coherent cohomology,
  pseudo-coherence on charts, and `Scheme.HasFiniteTorDimensionOver`.
  Its definition chooses a K-flat representative over the inverse-image
  structure sheaf and `a b : ℤ` with `a ≤ b`, and tests vanishing in every
  degree outside [a,b] against EVERY module sheaf over that ring in degree
  zero. Bounds vary by affine chart, exactly the node's local requirement.
  Under the explicit hqc and hpc assumptions, its other conjuncts are
  already assumed; thus this is precisely (ii), not absolute perfection,
  a fixed global interval, or a test only against quasi-coherent modules.
- The displayed `↔` is between the whole conjunction (i) and condition
  (ii). Relative perfection is not an additional assumption or conclusion.
  Perfect complexes mentioned as background in the node impose no extra
  hypothesis; the strict-perfect coefficient module is imported unchanged.

### Dependency declarations used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  structure sheaves and modules.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is exactly
  the general `SheafOfModules` category inherited by the space model.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  the existing `SheafOfModules.IsQuasicoherent` specialization used by
  `derivedQCohProperty`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`: the existing
  strict-perfect package and local-perfectness predicates; unchanged background.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, and the already fixed small module model.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`:
  `AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect`:
  `IsPerfectRelativeToScheme`, using upstream
  `WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver`:
  `Scheme.HasFiniteTorDimensionOver`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `derivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.fromSpecResidueField`.

The item gains the seven already landed definition-owner nodes corresponding
exactly to the seven added space notions above. No new node and no dependency
module is supplied. All original dependencies and all proof steps are preserved.
The theorem docstring carries all six proof steps and their dependency ids.

### Proof-only imports

Recorded, available proof dependencies are imported non-publicly. Four proof
nodes currently have no usable declaration in the read tree:
`lem-sfb-etale-pseudocoherence-descent`,
`lem-sfb-space-ring-sheaf-tor-amplitude-stalk-test`,
`lem-sfb-ring-relative-perfect-fibre-criterion`, and
`lem-sfb-etale-relative-tor-comparison`. Their absence affects only the future
proof, not formation of this statement, and their proof-plan citations remain.

The proof-only import
`Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion` was tried and
omitted after the compiler reported that its public import
`Sheaf.AlgebraicGeometry.FiniteTorDimensionOver` duplicates
`AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver` from the upstream
`WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver` already used by
relative perfection. The upstream definition is retained, following the explicit
launcher instruction to repair duplicate imports by preferring upstream.
The affine Tor criterion remains in proof_deps and the proof docstring;
no live library source or dependency record was edited for this collision.

### Searches and edge cases

Searches used the prescribed msearch wrapper (recorded in searches.jsonl):
LeanFinder on the full relative-perfect fibre criterion returned ordinary
flatness/smoothness and affine-limit results, no match; Loogle on
`DerivedCategory.IsGE, AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent`
returned no hits (the project-specific name is unknown to its Mathlib index);
Mathlib grep on
`LocallyBoundedBelow|locallyBoundedBelow|relativePerfect|RelativePerfect|bounded_on_fibres`
returned no hits. LeanSearch on the criterion returned eight hits about formal
smoothness, quasi-finite fibres and finite-presentation/quasi-coherence; none
states the relative-perfect bounded-fibre criterion.
Direct rg searches of both `lean/WeilConjectures` and `lean/Sheaf` found the
existing pseudo-coherence, relative-perfection and derived-pullback definitions
used here, and the inline covering-sieve lower-bound formula in
`AlgebraicSpacePseudoCoherentRHomQuasiCoherent.lean`, but no theorem giving this
criterion. The required grep of the item id in `lean/WeilConjectures` gave no
hits. No project/Mathlib declaration uses any of the four delivered names.

Checked the zero complex (all local tests vanish, any interval such as [0,0]
works), empty X and empty residue fibres (zero cohomology and vacuous site
conditions), empty S (no s-tests), arbitrary/nonclosed s, negative lower
bounds and bounds varying between different charts and fibres. No finite-type,
Noetherian, quasi-compactness, separation, nonemptiness, fixed global lower
bound or perfectness over O_X has been added. Flatness over a field does not
force the object to be perfect on a singular X; the right side correctly tests
relative Tor dimension over that field instead.

### Validation

`scompile.py Q04 lem-sfb-space-relative-perfect-fibre-criterion` compiled the
sandbox file and its exact library module separately and cleanly (8.0 s and
2.3 s in the successful run), under the default 60 s per-file limit. No warning,
auto-implicit, auxiliary proof, or sorry-containing definition remains.

## Second reading by Q04

Independent second reading by the maintainer review (the delivered section was
the author's own self-check). Read against the node, Stacks
spaces-more-morphisms.tex lemma-bounded-on-fibres (Tag 0GFK, l. 12759) and the
live records and modules of every statement dependency.

Node list → Lean → verdict:
- Scheme S, space X over it, f : X → S: `S : Over B`, `X : AlgebraicSpace B`,
  `f : X ⟶ schemeSpace S` (def-trf-scheme-algebraic-space). The ambient B is the
  form required by `IsPerfectRelativeToScheme`; B = S.left recovers the node. OK.
- f flat, locally finitely presented on étale scheme charts: `MapIsFlat f`,
  `MapIsLocallyOfFinitePresentation f` = `MapIsLocally (@Flat/@LocallyOfFinitePresentation)`
  over all compatible étale chart pairs (def-sfb-space-morphism-properties). OK.
- K ∈ D_QCoh, pseudo-coherent: `K : X.DerivedModules`, `hqc : X.derivedQCohProperty K`,
  `hpc : X.IsPseudoCoherent K`. OK; nothing stronger.
- s ∈ S arbitrary point; X_s, i_s: `s : S.left`; `residueFieldSpaceMap` is the
  represented map of `S.left.fromSpecResidueField s`; `residueFibre` /
  `residueFibreInclusion` are abbrevs of `enlargedFibreProduct` /
  `enlargedFibreProductFst` (def-sfb-space-sheaf-fibre-product). They are canonical, not chosen. OK.
- Li_s^*K: `(derivedTensorPullback (residueFibreInclusion S f s)).obj K`
  (def-sfb-space-derived-tensor-pullback, K-flat). OK.
- (i) local lower bounds: for every small-model object V there is a covering sieve
  with, on each member U, some c such that the restriction of H^n(K) to U vanishes
  for every n < c. The fibre clause is the same, for every s. Each bound is
  local, with no uniformity across U or s. OK.
- (ii) / S-perfection: `IsPerfectRelativeToScheme S f K` = D_QCoh ∧ on every
  affine chart, pseudo-coherent ∧ `HasFiniteTorDimensionOver` (all modules over the
  inverse-image ring, one interval per chart). Under hqc and hpc this is exactly (ii),
  and it is Stacks' "S-perfect". The ↔ has the whole conjunction (i) on the left. OK.

Universes: u for the site; independent w for X and wF for all fibres. These are only
existence binders and impose no equality. autoImplicit is off, and every variable is bound.
Edge cases: empty X, S or fibre (vacuous sieve tests, zero object); K = 0; non-closed s;
negative bounds. All are covered, with no Noetherian, quasi-compactness or
uniform-bound assumption.
H4: no space-fibre or relative-perfect fibre-criterion declaration in
side-live lean/Sheaf or lean/WeilConjectures (grep fromSpecResidueField/schemeSpace defs,
residueFibre, FibreCriterion). The helper names do not clash.
Records: the stmt_deps additions are 7 landed definition nodes only. The original deps
are kept, the lean.statement is verbatim in the file, and the proof is `sorry`. Docstrings
carry the source place, the blueprint id and the six proof steps. The proof-only imports
are private.
No mismatch found; only this section was replaced.
