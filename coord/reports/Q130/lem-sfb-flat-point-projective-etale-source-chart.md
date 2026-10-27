## Worker report

The module `Sheaf.AlgebraicGeometry.FlatPointProjectiveEtaleSourceChart` states
`AlgebraicGeometry.exists_projective_affine_etale_source_chart`, with its whole proof
`sorry`. It adds no definition. The existing node is unchanged except for `lean`.
I read Stacks `flat.tex`, Tag 05ID, `proposition-finite-presentation-flat-at-point`,
including the proof at lines 3286–3340. It gives exactly the two pointed elementary
etale neighbourhoods, affine source and base, and projectivity of pulled-back sections.
The module docstring reproduces the eight accepted DAG proof steps and their citations.

Hypothesis and conclusion correspondence:

- Schemes and named morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`.
- The O_X-module: `(F : X.Modules)`; quasi-coherence and finite presentation are
  `[F.IsQuasicoherent] [F.IsFinitePresentation]`, using the recorded Mathlib notions.
- Marked point and its image: `(x : X)`, with `s` written directly as `f x`.
- Flatness at that point only: `hflat` is `Module.Flat (S.presheaf.stalk (f x))`
  of the actual module stalk `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F`,
  restricted along `(f.stalkMap x).hom` by `ModuleCat.restrictScalars`.
  This is the stalk formulation explicitly included in def-pc-scheme-module-flat-over;
  the global `F.IsFlatOver f` would be stronger and is not assumed.
- Affine schemes and chosen points: existential `Y S' : Scheme.{u}`, `y : Y`, `s' : S'`,
  and `IsAffine Y ∧ IsAffine S'`.
- Three arrows: existential `g : Y ⟶ X`, `q : Y ⟶ S'`, `e : S' ⟶ S`.
- Commuting square: `g ≫ f = q ≫ e`.
- Marked points: `g y = x ∧ q y = s'`. Commutativity then implies `e s' = f x`,
  so the base neighbourhood is pointed over `(S,s)` without a redundant conjunct.
- Elementary etale source neighbourhood: `Etale g ∧ IsIso (g.residueFieldMap y)`.
  The source of the actual field map is κ(g y), identified with κ(x) by `g y = x`.
- Elementary etale base neighbourhood: `Etale e ∧ IsIso (e.residueFieldMap s')`.
  Its source is κ(e s'), identified with κ(s) by commutativity and the point equations.
  These concern the induced maps, not merely an abstract isomorphism of fields.
- Pulled-back module: `(Scheme.Modules.tensorPullback g).obj F`, the recorded tensor
  construction, imported through `TensorPullbackSectionAdjunction`.
- Projective sections over the new base: the final `@Module.Projective` uses the
  existing natural Γ(Y,O_Y)-module `Γ((tensorPullback g).obj F, ⊤)` and restricts it
  along `q.appTop.hom` with `Module.compHom`. The base ring is precisely `Γ(S', ⊤)`.
  No `Module.Finite`, `Module.FinitePresentation`, free basis, or finite rank over
  this ring is assumed or asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`;
  affine schemes use `IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, whose docstring explicitly records the equivalent
  stalkwise formulation used here at the single marked point.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: its public Mathlib
  `SheafOfModules.IsQuasicoherent`; the conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` is unnecessary because the node separately
  assumes quasi-coherence and finite presentation, rather than finite type.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` (the finite-presentation clause of the
  dependency whose main recorded module is `Generators`).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly exposes the
  actual `Scheme.Modules.tensorPullback` construction in
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; its full definition and docstring
  were read. No pullback functor is redefined or chosen.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, used directly to encode the prescribed module stalk.

All currently recorded proof-dependency modules are imported non-publicly unless already
publicly needed by the signature. For Mathlib leaves the recorded match's file is imported.
`lem-trf-complete-algebra-devissage-etale-existence` currently has no Lean record, no
Mathlib match, and no closed upstream declaration, so there is no proof module to import;
it remains named explicitly in the proof docstring. It is not needed to type this statement.

Edge cases checked against the signature and source: the empty source has no `x`, so
there is no omitted pointed case; an empty base cannot receive the marked point. The
zero sheaf is allowed and produces the zero projective module. Nonclosed points and
arbitrary residue fields are allowed; no algebraic-closedness, rational-point,
Noetherian, finite-type-over-field, separatedness, global flatness, or cartesian-square
hypothesis is introduced. Schemes and their module stalks use the same arbitrary `u`,
with no unrelated smaller test-object universe. Infinite rank over the base remains
allowed (e.g. O on affine one-space over a field already has infinite-dimensional
sections over the base). No statement correction, disputed statement, new node, or
dependency repair is needed.

Searches actually run:

- `msearch.py ... leanfinder`: “A finitely presented quasi coherent sheaf flat at a point
  has projective affine sections after elementary etale neighborhoods of source and
  base”. Eight hits: flat morphism APIs, universal openness, and
  `Module.Flat.projective_of_finitePresentation`; none gives the statement. The latter
  requires finite presentation over the base ring, which is absent here.
- `msearch.py ... loogle`: `Module.Projective, AlgebraicGeometry.Etale`: zero hits.
- `msearch.py ... grep`: `projective.*[Ee]tale|[Ee]tale.*[Pp]rojective` in
  `AlgebraicGeometry`: zero Mathlib hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `flat-point-projective|flatPoint.*rojective|projective.*[Ee]tale|etale.*[Pp]rojective`:
  no exact theorem; `FlatAlgebraEtaleProjectiveNeighborhood` is the structure-sheaf
  special case, and `HenselianFlatPointFreeAffineNeighbourhood` has a henselian base
  and a different conclusion. Numerous etale cohomology/projective-line hits are
  unrelated. The exact new name was also checked in both trees and
  `dag/lean_names_upstream.json`, with no match.
- `grep -rn` for this node id in `lean/WeilConjectures`: no match.
- Source searches located the existing module stalk, tensor pullback, scalar
  restriction, finite presentation, projectivity, and induced residue-field map APIs;
  their declarations and docstrings were opened before writing the signature.

Validation: server compilation and delivery preflight are run using the prescribed
`scompile.py` and `deliver2.py` wrappers; no local or global build is run.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
