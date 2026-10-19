## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteTypeFlatEtaleNeighborhood.lean` states
`AlgebraicGeometry.exists_finite_type_flat_etale_neighborhood`.  It is a statement-only
module: the proof is `sorry`.  The theorem has the exact source hypotheses and conclusion.
The local flatness condition is rendered directly as `Module.Flat` on the stalk module,
with the scalar action induced by `f.stalkMap`; this is the stalk formulation of
`def-pc-scheme-module-flat-over`.  The conclusion uses the categorical pullback of schemes,
the recorded `Scheme.Modules.tensorPullback`, and restriction to an open subscheme.

The hypotheses and conclusion clauses are rendered as follows.

* `f : X ⟶ S` is a morphism of schemes, with the typeclass
  `[LocallyOfFinitePresentation f]` (the locally finite-presentation hypothesis).
* `F : X.Modules` and `hF : Scheme.Modules.IsQuasiCoherentFiniteType F` render the
  quasi-coherent finite-type module hypothesis, using the recorded dependency module.
* `x : X` is the chosen point.
* `hflat : moduleFlatAt f F x` uses the landed stalk-flatness predicate
  `AlgebraicGeometry.moduleFlatAt` (module `Sheaf.TraceFormula.FlatAssociatedEquidimensional`,
  also used by `lem-trf-flat-fibre-free-neighbourhood`): the stalk module
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F`, with scalars through
  `(f.stalkMap x).hom`, is `Module.Flat (S.presheaf.stalk (f x))`.  This is the pointwise
  form of `def-pc-scheme-module-flat-over` (Stacks 01U4 (1) iff (2)); no new definition.
* `S'`, `s'`, and `e : S' ⟶ S` are existentially introduced.  `Etale e`, `e s' = f x`,
  and `IsIso (e.residueFieldMap s')` render the elementary étale neighbourhood and its
  residue-field isomorphism.
* Write `e₀ := Scheme.fromSpecStalk S' s' ≫ e : Spec 𝒪_{S',s'} ⟶ S`.
  `V : (CategoryTheory.Limits.pullback f e₀).Opens` is the open subscheme of
  `X ×_S Spec 𝒪_{S',s'}`, and `x' : V` is its marked point.  The equations
  `(pullback.fst f e₀) (V.ι x') = x` and `(V.ι ≫ pullback.snd f e₀) x' = IsLocalRing.closedPoint (S'.presheaf.stalk s')` say that
  the marked point lies over both `x` and the chosen base point `s'`.
* `SheafOfModules.IsFinitePresentation ((Scheme.Modules.restrictFunctor V.ι).obj
  ((Scheme.Modules.tensorPullback (pullback.fst f e₀)).obj F))` is finite presentation of
  the pulled-back module on `V`.
* `∀ y : ↥(pullback f e₀), pullback.fst f e₀ y = x → y = V.ι x'` states the required
  uniqueness of the point over `x`.
* The final clause is `Scheme.Modules.IsFlatOver` (the recorded declaration of
  `def-pc-scheme-module-flat-over`) of the restricted pulled-back module over
  `V.ι ≫ pullback.snd f (Scheme.fromSpecStalk S' s' ≫ e)`, i.e. flatness over
  `\mathcal O_{S',s'}` on all of `V`; the module is quasi-coherent, so the affine-local
  definition agrees with the stalkwise one.

The dependency declarations used are:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`.
* `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
* `def-weil-pbc-module-finite-type-presentation`: Mathlib's
  `SheafOfModules.IsFiniteType`/`SheafOfModules.IsFinitePresentation` declarations.
* `def-pc-scheme-module-flat-over`: `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`; its stalk formulation is expanded directly
  in this theorem as required by the node statement.
* `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
* `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
* `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, together with
  `pullback.fst` and `pullback.snd`.
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (the open `V` supplies this structure).
* `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (the
  recorded module, which publicly re-exports `WeilConjectures.AlgebraicGeometry.TensorPullback`),
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.

I checked edge cases in the statement before writing it: the finite generating list may be
empty (the zero module case), the fibre-support dimension may be zero, `V` may be any open
containing the marked point, and the pullback point uniqueness is stated for all points over
`x`, including the zero-dimensional and empty-support situations.  No nonemptiness or
positive-rank assumption was added.

Searches made:

* `msearch.py ... leanfinder "finite type quasi coherent module flat at a point finitely
  presented after elementary etale neighborhood"`: returned only Mathlib finite-presentation,
  étale, and localization declarations; no neighbourhood theorem (no match).
* `msearch.py ... loogle "AlgebraicGeometry.Etale, SheafOfModules.IsFinitePresentation,
  Module.Flat"`: 0 hits.
* `msearch.py ... grep "elementary.*etale|etale.*neighborhood|moduleFlatAt|FinitePresentation"
  Mathlib/AlgebraicGeometry`: 0 hits.
* Repository `rg` searches for `elementary.*etale`, `EtaleNeighborhood`, and the target id found
  no existing declaration of this theorem or an elementary-étale-neighbourhood definition.
  The recorded dependency declarations and Mathlib declarations listed above were then read
  at their source signatures.

The file was compiled with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q95 lem-trf-finite-type-flat-etale-neighborhood lean/Sheaf/AlgebraicGeometry/FiniteTypeFlatEtaleNeighborhood.lean`

The sandbox and library compilations completed with no errors or warnings.

## Second reading by Q95

I reread the node statement and the Lean signature against Tag 05I5.  The morphism, locally
finite-presentation instance, quasi-coherent finite-type module, point, and stalk-flatness
hypotheses all occur without additions.  The existential base scheme, marked point, étale
map, point equation, and residue-field isomorphism render the elementary étale neighbourhood.
The pullback is `CategoryTheory.Limits.pullback f e₀`; `V` is an open of that pullback and
`x'` is explicitly over `x` and `s'`.  The signature includes the marked-point second-projection equation, finite presentation,
the stalkwise flatness of the restricted tensor pullback, and separately states uniqueness
of every pullback point over `x`.  The zero-module/zero-dimensional cases remain admissible.
The second reading found no statement correction, no missing hypothesis, and no extra
conclusion; only the spelling was made explicit through the recorded declarations.

## Maintainer review correction (NT reviewer, 2026-10-18)

The Lean statement and node record were found correct and are unchanged.  Corrections:
the report above now names the delivered path `lean/Sheaf/AlgebraicGeometry/...` and the
actual spelling of the flatness hypothesis (`moduleFlatAt`) and of the flatness conclusion
(`Scheme.Modules.IsFlatOver`); the module now imports the recorded module of
`def-pc-module-pullback` (`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`) and the
stated proof dependency `Sheaf.TraceFormula.ElementaryDevissageFinitePresentation`
(lem-trf-elementary-devissage-finite-presentation), which was missing from the plan imports.
The fixed file compiles cleanly per file (`tools/nt_compile.py`, no message).
