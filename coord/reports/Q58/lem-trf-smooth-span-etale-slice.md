## Worker report

The delivery states `AlgebraicGeometry.Smooth.exists_pointed_span_etale_slice` in
`Sheaf.AlgebraicGeometry.SmoothSpanEtaleSlice`, with proof `sorry`. It also repairs the
module interface of the existing proof dependency `lem-trf-smooth-point-etale-immersion`.
No natural-language node statement or dependency list changes. No new notion is defined.
Sources read: Stacks `more-morphisms.tex`, Tag 0GDX
`lemma-relative-map-approximation-pre`, especially its final paragraph, and Tag 057G
`lemma-slice-smooth`, including its proof. The latter explicitly gives an immersion and
singleton designated fibre. The former restricts the span to its scheme-theoretic
inverse image. The additional projection and point clauses in this node spell out that
restriction by the existing fibre-product universal property.

Hypothesis matching (all schemes and all points are in the explicitly bound universe `u`):

| Node hypothesis or notation | Lean rendering |
| --- | --- |
| Schemes and morphisms `X → S`, `Y → T`, `S' → S`, `S' → T` | `{X Y S T S' H : Scheme.{u}}`, `f`, `g`, `q`, `lam` |
| `q` smooth | `[Smooth q]` |
| Chosen `s'`, `s = q(s')`, `t = λ'(s')` | `(s' : S')`; the expressions `q s'`, `lam s'` are used directly |
| The specified map `κ(s) → κ(s')` is an isomorphism | `hs : IsIso (q.residueFieldMap s')` |
| `X' = X ×[S] S'`, `Y' = Y ×[T] S'` | `pullback f q`, `pullback g lam` |
| The two morphisms from `H'` | `a : H ⟶ pullback f q`, `c : H ⟶ pullback g lam` |
| Both are étale | `[Etale a]`, `[Etale c]` |
| Both are morphisms over `S'` | `r : H ⟶ S'`, `ha : a ≫ pullback.snd f q = r`, `hc : c ≫ pullback.snd g lam = r` |
| Point `h'` over `s'` | `(h : H)`, `hh : r h = s'` |
| `x' = a'(h')`, `y' = c'(h')`, and image `x` | `a h`, `c h`, `(pullback.fst f q) (a h)` |
| `κ(x) → κ(x')` is an isomorphism | `hx : IsIso ((pullback.fst f q).residueFieldMap (a h))` |
| `κ(x') → κ(h')` and `κ(y') → κ(h')` are isomorphisms | `haκ : IsIso (a.residueFieldMap h)`, `hcκ : IsIso (c.residueFieldMap h)` |

Conclusion matching:

| Node clause | Lean rendering |
| --- | --- |
| Open neighbourhood `O` of `s'` | `O : S'.Opens`, `s' ∈ O`; its open subscheme is `O.toScheme` and its canonical inclusion is `O.ι` |
| Closed immersion `i : V → O` | `V : Scheme.{u}`, `i : V ⟶ O.toScheme`, `IsClosedImmersion i` |
| Regard `i` also as a morphism into `S'` | `j : V ⟶ S'` together with `j = i ≫ O.ι` |
| `v` maps to `s'` | `v : V`, `j v = s'` |
| Structure morphism `V → S` | `qV : V ⟶ S`, `qV = j ≫ q` |
| This morphism is étale | `Etale qV` |
| `κ(s) → κ(v)` is an isomorphism | `IsIso (qV.residueFieldMap v)`; its domain is identified with `κ(q s')` by `qV = j ≫ q` and `j v = s'` |
| Its underlying fibre over `s` is `{v}` | `qV ⁻¹' {q s'} = {v}` |
| `τ = λ' i : V → T` | `τ : V ⟶ T`, `τ = j ≫ lam` |
| `W = H' ×[S'] V` | The chosen Mathlib object `pullback r j`, used directly throughout |
| The fibre of `W → H'` at `h'` is canonically `Spec κ(h')` | `IsIso ((pullback.fst r j).fiberToSpecResidueField h)`: this is the canonical projection itself, not an unspecified isomorphism |
| There is a unique point `w` over `h'` | `w : ↥(pullback r j : Scheme.{u})` and `(pullback.fst r j) ⁻¹' {h} = {w}` |
| `κ(h') → κ(w)` is an isomorphism | `IsIso ((pullback.fst r j).residueFieldMap w)` |
| Canonical maps `X ×[S] V → X'`, `Y ×[T] V → Y'` | `kX`, `kY`; each is uniquely specified by its two projection equations |
| Induced maps from `W` to those two restrictions | `aV`, `cV`; each is uniquely specified by its two projection equations |
| `W ≅ H' ×[X'] (X ×[S] V)` | `eX : pullback r j ≅ pullback a kX` |
| `W ≅ H' ×[Y'] (Y ×[T] V)` | `eY : pullback r j ≅ pullback c kY` |
| These identifications preserve projections | The two equations for `eX.hom` identify its projections with `pullback.fst r j` and `aV`; the two for `eY.hom` identify them with `pullback.fst r j` and `cV` |
| The three induced maps are étale | `Etale aV`, `Etale cV`, `Etale (aV ≫ pullback.fst f qV)` |
| They commute over `V` | `aV ≫ pullback.snd f qV = pullback.snd r j`, and the corresponding equation for `cV` |
| They commute over `S` | `(aV ≫ pullback.fst f qV) ≫ f = pullback.snd r j ≫ qV`; the other stated projection equations also give the structural triangles |
| `w` maps to `x` and `v` | `(aV ≫ pullback.fst f qV) w = (pullback.fst f q) (a h)` and `(pullback.snd r j) w = v` |
| `τ(v) = t` | `τ v = lam s'` |
| `κ(x) → κ(w)` is an isomorphism | `IsIso ((aV ≫ pullback.fst f qV).residueFieldMap w)` |

The existentially named composites and restriction maps do not introduce arbitrary maps:
`j`, `qV`, and `τ` have explicit defining equalities. The two projections determine each
of `kX`, `kY`, `aV`, `cV` uniquely by the universal property of the chosen pullback.
The two projections likewise determine each comparison isomorphism. Thus this is an
existential formulation of the specified canonical constructions. No arbitrary coefficient
map, choice from `Nonempty`, hidden `let`, or extra geometric assumption occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; proof input
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` and the open-immersion
  residue-map isomorphism instance.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and their universal property.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  `Etale.etale_isStableUnderBaseChange`, `Etale.etale_comp`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Restrict` supplies `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, including its pullback instances.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField` and the underlying fibre interpretation.
- `Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion`:
  `AlgebraicGeometry.Smooth.exists_etale_immersion_slice`, repaired in this delivery.
- `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`:
  `Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`.
- Plain proof imports retain the recorded permanence tools from Mathlib modules
  `Morphisms.Proper`, `Finite`, `FinitePresentation`, `QuasiCompact`, `QuasiSeparated`,
  `Separated`, `FiniteType`, and `Immersion`. Statement dependencies are public imports;
  proof dependencies are private imports unless their module is already public for
  a statement notion. No import cycle is introduced.

Searches, all performed through `msearch.py` where indicated:

- LeanFinder: “A pointed etale span over a smooth morphism restricts to a closed etale
  slice with singleton fibre and unchanged residue fields”. Eight hits: standard étale
  presentations, étale localization and standard smooth charts; no pointed span theorem.
- Loogle: `AlgebraicGeometry.Smooth, CategoryTheory.Limits.pullback`. Three hits:
  `instSmoothFstScheme`, `instSmoothSndScheme`, and smooth normalization pullback;
  none gives the statement.
- Mathlib grep: `etale.*slice|smooth.*span|exists_etale_immersion_slice` in
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: “smooth scheme morphism rational point closed etale slice base change
  pointed etale span”. Eight hits about smooth definitions, smoothness base change,
  and étale base change; no full slice-and-span result.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for smooth spans, étale
  slices, `exists_etale_immersion_slice`, the item id, and the proposed declaration.
  The general smooth-point immersion theorem is the existing proof dependency;
  upstream `Morphisms/Slicing.lean` provides a weaker morphism slice. Neither has
  the full pointed span and canonical comparison conclusions. The proposed name
  has no hit in Mathlib, upstream, `lean/Sheaf`, or `dag/lean_names_upstream.json`.
- Read the actual server source with `scompile.py --source
  Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion` after the compiler reported
  the legacy-module incompatibility; it confirms the same unimportable header.

Edge cases checked before writing and again against the finished statement:

- Empty schemes are not excluded by an extra assumption. Existing input points force
  `H` and `S'`, and hence their indicated images, to be nonempty; if an input point
  cannot exist, the universally quantified theorem has no such instance.
- If `q` is the identity, the slice can be an open neighbourhood with its identity
  closed immersion. The fibre and comparison clauses reduce to the expected ones.
- For a smooth affine-space projection at a rational point, a coordinate slice has
  the singleton fibre and all stated pullbacks. Positive relative dimension is allowed.
- Disconnected or multi-sheeted `H` is allowed. The singleton condition concerns only
  the fibre over the fixed `h`, rather than the whole fibre of `W → V`.
- Nonreduced `H` and nonreduced bases are allowed: the relevant fibre is a nonempty
  closed subscheme of the spectrum of the field `κ(h)`, hence has zero defining ideal.
- There is no characteristic restriction and no finite-type, Noetherian, separated,
  or affine hypothesis beyond smoothness and the étale legs already in the node.
- The residue isomorphisms are those of the given scheme maps, not abstract field
  isomorphisms. All schemes use `Scheme.{u}` uniformly, with no additional size relation.

Validation: both delivered modules compile separately with `scompile.py` on the server,
in dependency order, with no errors or non-sorry warnings. The repaired dependency
compiled in 8.5 seconds and the item in 18.3 seconds (the same sources also passed
compilation under their actual module names). Both node copies differ from the read
repository only in `lean`; their signatures are extracted verbatim from the files.

There is no `STATEMENT-DISPUTED` finding or natural-language statement correction.
Only the dependency module-format fault described below was found.

## Dependency modules

`lem-trf-smooth-point-etale-immersion`: its recorded
`Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion` source has no `module` command.
The compiler rejects its import from the required module-mode item with:
“cannot import non-`module` Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion from `module`”.
The same owning module is repaired in the sandbox, with `module`, public statement
imports, private proof imports, exposed public declarations, and `autoImplicit false`.
Its mathematical statement and declaration name are preserved. The old `letI` canonical
residue algebra is passed explicitly to `Module.Finite` (through `Algebra.toModule`)
and `Algebra.IsSeparable`, so no hypothesis changes. The expanded docstring gives the
current four-step proof: finite local fibre dimension, dimension-zero open slice,
positive-dimensional hypersurface slice with closedness and residue verification,
and composition of the inductive immersion. Every theorem proof remains `sorry`.
Only this dependency node's `lean` field changes, with an explanatory `note`.

For this dependency, `IsClosed {f.asFiber x}` is exactly closedness in the scheme fibre;
`Module.Finite` and `Algebra.IsSeparable` use `(f.residueFieldMap x).hom.toAlgebra`;
the result binds `Z`, `i`, `z`, asserts `IsImmersion i`, `i z = x`, `Etale (i ≫ f)`,
and makes the range of the fibre inclusion exactly `{z}`. The algebra instances are
specified, not quantified over. Identity morphisms and dimension-zero smooth maps are
included, arbitrary characteristic and nonreduced bases remain allowed, and empty-source
cases require a point and therefore have no instance. Its statement notions are the
recorded Mathlib `Scheme`, `Smooth`, `Scheme.Hom.fiber`, `residueFieldMap`, `Algebra`,
`Algebra.IsSeparable`, `Etale`, `IsImmersion` (the closed/open factorization). The already
stated hypersurface proof input is retained as a plain import from
`Sheaf.TraceFormula.SmoothSeparableHypersurfaceSlice`; the dimension-bound and
zero-dimensional-singleton-open proof nodes have no recorded module and so add no import.

## Second reading by Q58

No second worker was started, as instructed by the dispatcher brief. The worker delivers
directly; the maintainer's independent review is the independent reading. An in-thread
reread compared each hypothesis and clause against the node and source, using the tables
above. It found the legacy dependency module incompatibility, which is repaired here.
It also checked that all existential maps have their canonical projection characterizations,
that the fibre isomorphism concerns the canonical structural map, and that the point
singleton is taken over `h`, not over `v`. The natural-language statements are unchanged.
