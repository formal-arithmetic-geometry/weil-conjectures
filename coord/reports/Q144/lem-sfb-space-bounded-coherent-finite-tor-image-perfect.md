## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceBoundedCoherentFiniteTorImagePerfect` states
`AlgebraicGeometry.AlgebraicSpace.isPerfect_derivedDirectImage_of_bounded_coherent_finiteTor`
with the sole proof `sorry`. The item statement, proof plan, and proof dependencies
are unchanged. Its statement dependencies gain the existing shared definitions used
in the signature and one new relative Tor definition node. No dependency record is repaired.

I read the node, every original statement dependency and its recorded declaration,
the available proof dependency records, and Stacks `spaces-perfect.tex` at
`lemma-perfect-direct-image` (08IS). The three hypotheses and conclusion agree with
that source. I also read `lemma-closed-proper-over-base` and
`definition-proper-over-base` (0CZC) in that file, and
`definition-tor-amplitude` (08FZ), `lemma-tor-amplitude` (08G1), and
`lemma-tor-amplitude-stalk` (0DJJ) in `sites-cohomology.tex`.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A scheme S and algebraic spaces over S | `{S : Scheme.{u}} {X Y : AlgebraicSpace S}` and `(f : X ⟶ Y)` |
| Small etale structure sheaves and module derived categories | `X.SmallModules`, `Y.SmallModules`, `X.DerivedModules`, and the existing equivalence `smallModuleEquivalence`; these use the small affine etale model of the original module topos |
| Size convention | Explicit universes `u w` and independent `[HasDerivedCategory.{w} X.SmallModules]`, `[HasDerivedCategory.{w} Y.SmallModules]`; the sites/coefficients use their recorded original universe |
| Y quasi-compact | `_hYqc : CompactSpace (Point Y.obj.obj)` |
| Y quasi-separated | `_hYqs : IsAbsolutelyQuasiSeparated Y`, the recorded absolute affine-test criterion; no assumption on S is added |
| Y locally Noetherian on etale scheme charts | `_hYln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T)` |
| f locally of finite type | `_hft : MapIsLocally (@LocallyOfFiniteType) f` |
| f quasi-separated | `_hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)` |
| H an unbounded derived object | `H : X.DerivedModules` |
| Quasi-coherent cohomology | `_hqc : X.derivedQCohProperty H`, using the original `SheafOfModules.IsQuasicoherent` after transport back from the small model |
| Coherent: finitely generated on Noetherian affine etale charts | `_hcoherent` tests `Module.Finite (Γ(T, ⊤))` on the sections of the Zariski chart restriction of each transported homology sheaf. The charts are locally Noetherian because f is locally of finite type over the locally Noetherian Y, so this is precisely the stated coherent condition |
| Vanishing outside one finite integer interval | `_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ n, n < a ∨ b < n → IsZero (...)` |
| Closed geometric-stalk support of every H^n | `_hsupport` gives a representable closed immersion `i : Z ⟶ X` with `Set.range (mapPoint i.hom.hom) = moduleSupport (...)`, using the existing geometric-germ support |
| Reduced induced structure on that closed support | The same `_hsupport` requires `∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)`; a reduced closed immersion with that image is the reduced induced closed subspace |
| Support proper over Y | `MapIsProper (i ≫ f)` in `_hsupport`; the shared predicate is exactly separated, finite type and universally closed |
| Scalar restriction of H along f^{-1}O_Y → O_X has finite Tor dimension, with a global interval and all module tests | `_hTor : HasFiniteTorDimensionOver f H`, defined in the new node below by the equivalent uniform geometric-stalk/bounded-flat criterion. The ring map is the existing `SingleComplex.stalkMap f s x`, and the stalk complex is restricted using `ModuleCat.restrictScalars` |
| Canonical Rf_* computed by K-injectives | `(derivedDirectImage f).obj H`, conjugating the recorded compatible-chart direct image by the small-model module equivalences before taking the existing unbounded right derived functor |
| Perfect conclusion | `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w} Y.smallStructureSheaf (...)`, the existing local bounded finite-free-retract predicate |

The source paragraph's conventions about finite presentation, relative module flatness,
and annihilator scheme-theoretic support introduce no further hypotheses on this H or f.
In particular, support in hypothesis (2) is the reduced closed geometric support, not
an annihilator condition on a chosen term of a complex. The theorem has no hypothesis
that f is proper, quasi-compact, flat or finitely presented. Derived tensor/pullback
occur in the meaning of finite Tor dimension and in the proof plan, rather than as
extra data supplied to the theorem. Bounded flat stalk representatives are K-flat,
so they compute the prescribed derived tensors against arbitrary base stalk modules.

Dependency declarations used (full names lie in `AlgebraicGeometry.AlgebraicSpace`
unless another namespace is shown):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `IsRepresentableWith`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`,
  `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the recorded `QCoh`
  specialization and slice instances; `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`. No replacement predicate is defined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `ModuleDirectImageModel`, `moduleDirectImage_isRightAdjoint`; these are retained
  by the canonical derived direct image.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureSheaf`, `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `derivedDirectImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsProper` (and its three defining conditions); `ProperCurveModuli`:
  `MapIsQuasiCompact`, `mapPoint`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`; its underlying
  `IsLocallyStrictPerfectComplexOfUniverses` uses the shared degreewise finite-free
  splitting package from `StrictPerfectPackageOnSite`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.stalkRing`, `SingleComplex.stalkMap`, `SingleComplex.stalk`, with
  their actual section-colimit and germ normalization; these supply the new definition.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`:
  `ModuleCat.restrictScalars`; `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.

The available proof-only dependencies are imported without `public`:
`WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
(`SheafOfModules.grothendieckAbelian_with_localized_generator`) and
`WeilConjectures.CategoryTheory.TruncationHypercohomology`
(`CategoryTheory.exists_truncationHypercohomology`). The module-functor proof dependency
is already a public dependency through the derived calculus. The other five proof
nodes have no Lean record in the read base, so no module is available to import:
`lem-sfb-space-proper-support-bounded-coherent-image`,
`lem-sfb-space-noetherian-pseudocoherent-criterion`,
`lem-sfb-space-proper-support-derived-projection-formula`,
`lem-sfb-space-quasicoherent-tor-amplitude-test`,
`lem-sfb-ringed-site-perfect-criterion`. They are retained in the proof plan and docstring;
the statement does not need their assertions as inputs.

Mathematical edge cases checked:

- H=0 and the empty source: cohomology/support vanish, the empty reduced closed
  subspace supplies each support, and the direct image is perfect. The new Tor
  predicate permits the zero representative and, on an empty source, has no
  geometric point tests. Neither case is excluded by an inhabitedness hypothesis.
- Empty target and the zero ring are not excluded.
- A non-quasi-compact disjoint union mapping to a point, with H supported on one
  proper component, is allowed. No compactness of X or f is present. The a,b in
  the relative Tor predicate precede all geometric points, so arbitrary varying
  local Tor bounds do not accidentally satisfy the global hypothesis.
- a=b is allowed; a flat module in one degree has that amplitude. No strict inequality
  or nonzero module condition is hidden in the predicate.
- Over k[epsilon]/(epsilon^2), the residue field under the identity does not have
  finite Tor dimension: its infinite flat resolution cannot be replaced by a
  bounded flat complex. Thus `_hTor` is substantive and does not follow from
  bounded coherent cohomology.
- Reducible/nonreduced cohomology supports are handled by taking their reduced
  induced closed structure. The hypothesis is not replaced by properness of f.
- The ambient derived localization universe w remains arbitrary; standard
  localizations of ordinary stalk modules only occur internally in the definition.
  Geometric points use Type u, the existing section universe, so the point tests
  do not become vacuous through a smaller unrelated universe.

Searches before writing:

1. `msearch.py leanfinder` on "A bounded coherent complex with proper cohomology
   supports and finite Tor dimension over a Noetherian algebraic space has perfect
   derived direct image": eight abstract derived t-structure results, no space theorem.
2. `msearch.py loogle` on `"AlgebraicGeometry", "perfect"`: two smooth-locus
   results over perfect fields; no match.
3. `msearch.py grep` on `AlgebraicSpace|properSupport.*perfect|finiteTorDimension`:
   zero Mathlib hits.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` on the item id and
   `bounded_coherent.*perfect|perfect.*finiteTor`: only ring/scheme perfectness and
   unrelated uses; no theorem with this algebraic-space statement. The upstream
   scheme theorem in `BoundedCoherentFiniteTorDirectImagePerfect` is proper/scheme
   specialized, and cannot be used to state this generality as an existing match.
5. `tools/lean_names_upstream.py show` for this item found no attached declaration.
6. Searches for the added relative Tor notion are recorded in the new node, including
   the raw `msearch.py` outputs. LeanSearch returns ordinary scheme stalkwise flatness;
   LeanFinder returns scheme flat/smooth morphism facts; Mathlib grep returns no match.
   `rg` in the project finds the scheme-only `Scheme.HasFiniteTorDimensionOver`
   and relative-perfect predicates with extra pseudo-coherence and varying local
   bounds. DAG grep and `tools/blueprint_refs.py search` confirm no definition node
   for the uniform general algebraic-space predicate.

Validation: both modules compile individually through `scompile.py`, in dependency
order, against the published live build. Both sandbox and library-name checks pass
without warnings. The initial incorrect Mathlib Noetherian import path was repaired
before the clean check. The theorem proof is `sorry`; the new definition contains
no `sorry` and no arbitrary-map or arbitrary-object choice. No statement dispute
or source correction is needed.

## New nodes

`def-sfb-space-finite-tor-dimension-over`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTorDimensionOver`, defines
`AlgebraicGeometry.AlgebraicSpace.HasFiniteTorDimensionOver`. This is the global
relative Tor hypothesis of Stacks 08IS(3), expressed using 0DJJ and 08G1: after
restriction along the canonical geometric stalk ring map, one interval [a,b]
contains a flat representative at every geometric point. Enough geometric points
make these tests equivalent to the original all-module-sheaf tests over f^{-1}O_Y;
0DJJ gives the same interval in both directions, and 08G1 turns each interval
condition into the existence of a bounded flat representative. The representative
K of H is global, the interval is uniform, and the stalk complexes P may depend
on the point. Standard localizations are confined to this internal ordinary-module
test and impose no equality involving w. The predicates for scheme targets and
relative-perfect objects do not define this notion: the former has a scheme
base, while the latter adds pseudo-coherence and permits varying local intervals.
The searches and source places above establish why a new definition node is required.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
