## Worker report

The module `Sheaf.AlgebraicGeometry.SheafExtStalkLocalization` states
`AlgebraicGeometry.nonempty_moduleSheafExt_stalk_linearEquiv`, with a `sorry` proof.
No definitions are added and the node statement is unchanged.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`.
- Quasi-compactness: `[CompactSpace X]`, as recorded by
  def-weil-pbc-quasi-compact-scheme; no separation condition is imposed.
- Locally Noetherian: `[IsLocallyNoetherian X]`, as recorded by pqf-def-locnoeth.
- F and G are O_X-modules: both have type
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
- Coherence of each: `hF` and `hG` use `RingedSpace.IsCoherent` from pqf-def-coherent.
- Every point: `(x : X)` without any condition on x.
- Every nonnegative integer degree: `(q : ℕ)` and `(q : ℤ)` in sheaf Ext.
  This parametrizes exactly the integers q >= 0 without omitting q = 0.
- The left side is `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
  (moduleSheafExt X (q : ℤ) F G)`, the stalk of the recorded sheaf Ext of F[0],G[0].
- The right side is `Abelian.Ext` of the two objects obtained from the same stalk functor,
  in degree q. Its ambient module category is over `X.presheaf.stalk x`, the local ring.
- The isomorphism is `Nonempty (... ≃ₗ[X.presheaf.stalk x] ...)`, an isomorphism of
  modules, hence also of Ext groups. No arbitrary carrier equivalence is substituted.
- `[HasDerivedCategory.{w} ...]` supplies the size infrastructure required by sheaf Ext;
  it imposes no geometric condition. Module-category `HasExt` is supplied by Mathlib,
  with no extra finiteness, regularity or derived-category hypothesis at the stalk.

Dependency declarations read and used:
`Mathlib.Topology.Defs.Filter`: `CompactSpace`;
`Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
`Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`;
`Sheaf.AlgebraicGeometry.SheafExt`: `AlgebraicGeometry.moduleSheafExt` (and its functor);
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: `CategoryTheory.Abelian.Ext`.
The shared stalk functor is
`AlgebraicGeometry.RingedSpace.moduleStalkFunctor` from
`Sheaf.Algebra.Homology.ModuleStalkFunctor` (def-pc-module-stalk-functor).
`Mathlib.Algebra.Category.ModuleCat.Ext.Basic` supplies the module-category HasExt
instance and the Ext scalar action from `Ext.Linear`.

Edge cases checked mathematically before writing: the empty scheme has no points so the
point-indexed claim is vacuous; zero F or zero G gives zero groups on both sides; q = 0
is localization of internal Hom; F = O_X gives G_x in degree zero and zero in positive
degrees. A one-point scheme gives the usual ring Ext comparison. No field,
characteristic, regularity or dimension restriction is introduced.

Searches (2026-10-11, msearch.py, recorded in searches.jsonl):
LeanFinder query `stalk of sheaf Ext for coherent modules is Ext over the local ring`:
eight hits on sheaf cohomology, tilde stalk localization and local cohomology, none the
statement. Loogle `Abelian.Ext, stalk`: no hits, unknown identifier `Abelian.Ext`.
LeanSearch `stalk sheaf Ext coherent localization`: unavailable, Internal Server Error.
Mathlib grep `stalk.*Ext|Ext.*stalk|SheafExt`: 25 hits, only stalk-map extensionality and
unrelated presheaf extension names. `rg` of the same localization patterns and the node
id in WeilConjectures gives unrelated Fourier-transform/dual-number hits, no theorem.
`rg` in lean/Sheaf gives stalk definitions and the citer CoherentExtVanishing docstring,
no statement of stalk Ext localization. The proposed full declaration name is absent
from Mathlib/source/project and dag/lean_names_upstream.json.

Sources read online because the local Stacks TeX checkout is absent:
[0FZ3](https://stacks.math.columbia.edu/tag/0FZ3), proof (1), explicitly gives this
stalk comparison; [0GM8](https://stacks.math.columbia.edu/tag/0GM8), case (2), supplies
pseudo-coherent/bounded-below derived Hom localization;
[08E8](https://stacks.math.columbia.edu/tag/08E8) supplies pseudo-coherence of F[0];
[0A64](https://stacks.math.columbia.edu/tag/0A64) identifies ring derived Hom cohomology
with shifted derived-category morphisms. The module docstring carries all three proof
steps and their DAG nodes. No statement dispute or statement correction is needed.

Validation: the previous missing `SheafExt.olean` artifact cleared after the server's
2026-10-11T15:54:50Z global build. A fresh `scompile.py M1
lem-sc-ext-stalk-localization` run compiled the unchanged theorem cleanly (exit 0,
no warnings). The delivery dry run is checked below before handoff.

## Second reading by M1

I read the node statement and the module independently. The introduced objects and their
rendering are: a scheme `X : Scheme.{u}`; quasi-compactness `[CompactSpace X]`; local
Noetherianity `[IsLocallyNoetherian X]`; coherent `O_X`-modules `F G :
SheafOfModules (moduleRings X.toRingedSpace)` with `RingedSpace.IsCoherent` hypotheses
`hF hG`; a point `x : X`; and a nonnegative integer `q : Nat`. The module has exactly
these binders and no separation, field, characteristic, dimension, or finiteness
hypothesis beyond the node.

The conclusion is rendered clause by clause as follows. The sheaf Ext stalk is
`(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (moduleSheafExt X (q : Int) F G)`.
The local coefficient ring is `X.presheaf.stalk x`, and the two local modules are the
stalk functor applied to `F` and `G`. The right side is `Abelian.Ext` of those modules in
degree `q`, and the displayed result is `Nonempty (... ≃ₗ[X.presheaf.stalk x] ...)`,
exactly the node's module isomorphism. `[HasDerivedCategory.{w} ...]` supplies only the
size infrastructure required by `moduleSheafExt`. The cast `(q : Int)` and the Nat
degree of `Abelian.Ext` together express precisely every integer degree `q >= 0`,
including zero.

Edge cases remain covered: an empty scheme makes the point quantifier vacuous; zero
modules and a one-point scheme are included; `q = 0` is included; no characteristic or
universe case is excluded. I searched Mathlib, the source repository, and `lean/Sheaf`
for sheaf-Ext stalk localization (LeanSearch, LeanFinder/Loogle, and `rg`) and found no
existing declaration. The dependency declarations used by the module are the recorded
`moduleSheafExt`, coherent-module predicate, module stalk functor, `CompactSpace`,
`IsLocallyNoetherian`, and Mathlib's `Abelian.Ext`; their signatures match the node. No
mismatch was found, so no source, statement, dependency, or module change was necessary.
