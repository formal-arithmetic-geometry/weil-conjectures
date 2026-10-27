## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothReducedDensePullback` states
`AlgebraicGeometry.smooth_reduced_dense_pullback`. Its sole theorem has proof
`sorry`; there are no new definitions, helper theorems, dependency repairs or
statement corrections. The original natural-language statement and dependencies
are unchanged. No statement dispute was found.

The source places read were ILO Expose VIII 2.2.7--2.2.9, printed pp.90--91
(PDF pp.96--97), Stacks descent.tex `lemma-reduced-local-smooth` (034E),
morphisms.tex `lemma-fppf-open` (01UA), and algebra.tex `lemma-flat-going-down`
(00HS). I also read the current blueprint's `lem-trf-local-term-locality`
statement and proof under `literature/blueprint/latest/`. ILO 2.2.2 explains
maximal domination as taking component generic points to component generic
points. The theorem supplies the smooth-pullback geometric inputs used below
the normalized-blowup calculus, rather than asserting the normalization theorem.

Hypotheses and conclusions, matched individually to the node:

- Schemes S and T and their morphism: `{S T : Scheme.{u}} (h : T ⟶ S)`.
  The arbitrary explicit universe is the standard scheme universe; there is no
  finiteness, field, nonemptiness, separatedness or surjectivity restriction.
- Reduced, locally Noetherian base: `[IsReduced S] [IsLocallyNoetherian S]`.
- Smoothness of h: `[Smooth h]`, the dependency's recorded Mathlib class.
- Reduced and locally Noetherian source: the first two conjuncts
  `IsReduced T ∧ IsLocallyNoetherian T`.
- Every component generic point: quantify `C : Set T` with
  `C ∈ irreducibleComponents T`, then `ξ : T` with `IsGenericPoint ξ C`.
  The conclusion `∃ D : Set S, D ∈ irreducibleComponents S ∧
  IsGenericPoint (h ξ) D` says exactly that its image is a generic point of
  a component of S. There is no chosen component or chosen generic point.
- Every dense open of S: `∀ (U : S.Opens), Dense (U : Set S) → ...`.
  The open condition is carried by `S.Opens`; density is a separate hypothesis.
- Density in T: `Dense (h ⁻¹' (U : Set S))`.
- Density in EACH component: for every `C ∈ irreducibleComponents T`,
  `Dense ((Subtype.val : C → T) ⁻¹' (h ⁻¹' (U : Set S)))`.
  This is density in the subspace C, equivalently density of
  `C ∩ h⁻¹(U)` in C; it does not assert density of that intersection in T.
- A quasi-coherent ideal J: `J : S.IdealSheafData`, the existing affine-local
  encoding used by the extended-ideal dependency. The module sheaf of this
  ideal is the existing `J.toModules`, not an arbitrary sheaf with a map.
- Quasi-coherence and finite type are retained explicitly as
  `Scheme.Modules.IsQuasiCoherentFiniteType J.toModules`, the recorded
  dependency's conjunction of the existing sheaf predicates.
- Nowhere dense zero set: `IsNowhereDense (J.support : Set S)`.
  `IdealSheafData.support` is the closed ZERO set V(J), as its definition and
  `coe_support_eq_eq_iInter_zeroLocus` show; it is not the module's nonzero-stalk
  support. Its ideal convention gives support(top) = empty, support(bot) = S.
- The conclusion is `IsNowhereDense ((J.comap h).support : Set T)`.
  `comap` is literally the kernel of the first projection from the pullback
  of `J.subschemeι`, precisely the node's definition of extended ideal.
- The empty-scheme and omitted-components sentence is respected by the absence
  of any extra hypothesis. All universal component/point clauses become vacuous
  for empty T; density and nowhere density still have their usual empty-space
  meanings.

Statement dependency declarations used (their signatures and documentation
were read in their source modules):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, with
  section-wise reducedness and the stalk equivalence below it.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`, defined by Noetherian affine sections.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  defined by smooth ring maps on affine charts.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, closure of the singleton equal
  to the indicated set.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, maximal irreducible
  subsets; the dependency is a Mathlib leaf, so no Lean-record repair is needed.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap` (and `support_comap` for the
  recorded proof). Its original module is imported publicly.
- The existing module realization of ideals is
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.
- The standard topology notions `Dense` and `IsNowhereDense` are reused;
  the latter is supplied publicly by `Mathlib.Topology.GDelta.Basic`.

The already-stated proof dependencies are imported without `public`, including
`Smooth.geometricallyReduced` from the upstream geometrically reduced module,
`exists_open_finite_irreducibleComponents` from its recorded Sheaf module,
and the Mathlib modules for finite presentation, finite type, flat openness,
geometrically reduced pullback, closed immersions, and affine fibre products.
The docstring carries all seven DAG proof steps: finite-type ascent;
reducedness via geometric fibres and identity pullback; generalization lifting
and component maximality; openness and density; local finiteness and density
on individual components; the affine tensor/quotient computation for V(J);
and dense complements. No postponed helper assertion was introduced.

Edge cases checked mathematically before drafting: T empty; S empty (then a
map forces T empty); a smooth open immersion omitting entire base components;
an identity map on a reducible scheme; U = top; J = top (empty zero set);
J = bot (fails nowhere-density for nonempty S, allowed for empty S);
nonseparated and non-quasi-compact schemes; arbitrary characteristic.
In particular the density-on-components clause uses the subspace topology,
and the proof isolates the base component using local finiteness before
claiming that its generic point belongs to an arbitrary dense open.

Searches actually run with `msearch.py Q57 lem-trf-smooth-reduced-dense-pullback`:

- LeanSearch: "Smooth morphism over a reduced locally Noetherian scheme
  preserves generic points of irreducible components and pulls dense opens
  back to dense opens". Eight hits: smoothness definitions, local finite
  presentation, and `genericPoint_eq_of_isOpenImmersion`; no full match.
- LeanFinder: "Smooth morphism over a reduced locally Noetherian scheme has
  reduced source preserves generic points and pulls back dense open subsets
  densely in each irreducible component". Eight hits: smoothness, dominance,
  reducedness for open immersions and generic points of open immersions;
  none states this conjunction.
- Loogle: `AlgebraicGeometry.Smooth, Dense`. Successful search, zero hits.
- Mathlib grep: `smooth.*[Dd]ense|[Dd]ense.*smooth|[Ss]mooth.*[Rr]educed`,
  subdirectory `AlgebraicGeometry`. Five hits, concerning smooth group schemes
  and density of the smooth locus over a perfect field; no full match.
- Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for smooth/reduced/dense and generic/smooth
  combinations, then `smooth_reduced_dense_pullback`,
  `smooth.*dense.*pullback`, `dense.*preimage.*[Ss]mooth`: related partial
  results and docstring citations only. `GenericFibreCoverDensity` has a
  reduced-source theorem over an integral base, not this statement.
- `grep -rn 'lem-trf-smooth-reduced-dense-pullback' lean/WeilConjectures`
  found no recorded upstream declaration. Source rg of IdealSheaf modules
  found the existing `toModules`, `support` and `comap` interfaces used above.

A final rereading of the original JSON against the theorem checked every
binder, each of the four groups of conclusions, the subspace density type,
and the ideal support convention. It found no mismatch requiring a change.
The only node field changed is `lean`; its statement is copied verbatim
from the theorem signature. All variables and universes are explicitly bound,
with `autoImplicit false`; every Lean line is at most 100 characters.

Validation: the prescribed `scompile.py` compiled the single delivered file
cleanly on the server in both sandbox and library mode (2.0 s and 2.6 s),
with no errors or unexpected warnings. `deliver2.py --no-push` then printed
`OK (dry run)` after both the server preflight and per-file compilation passed.
The final local consistency check confirmed that only `lean` changed in the
node, the recorded signature occurs verbatim in the file, and no Lean line
exceeds 100 characters.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
