## Worker report

The module `Sheaf.AlgebraicGeometry.AffineProjectiveCompactification` states
`AlgebraicGeometry.exists_affine_projective_compactification`, with proof `sorry`.
It includes the parenthetical construction in the node: a closed immersion into affine
space, composition with a standard projective chart, and the scheme-theoretic image of
that composite as the compactification. No definitions, dependency modules, new nodes,
or statement corrections are needed. The node copy changes only `lean`.

### Hypotheses and conclusions

| Node text | Lean rendering |
| --- | --- |
| A field K | `(K : Type u) [Field K]` |
| An affine scheme X | `(X : Scheme.{u}) [IsAffine X]` |
| Over K | `[X.Over (Spec (.of K))]`, with structure map `X ↘ Spec (.of K)` |
| Finite type | `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and `[QuasiCompact (X ↘ Spec (.of K))]`, the recorded conjunction defining finite type |
| Choose finite-dimensional affine and projective spaces | Existential `(n : Type u) (_ : Finite n) (i : n)`. The number of affine coordinates is the cardinality of `{k : n // k ≠ i}`; there is one further homogeneous coordinate i |
| Closed immersion into affine space over K | Existential `e : X ⟶ 𝔸({k : n // k ≠ i}; Spec (.of K))`, `IsClosedImmersion e`, and its composition with the affine-space projection equals `X ↘ Spec (.of K)` |
| Standard open immersion from affine space into projective space | `(ProjectiveSpace.standardOpenIso n (Spec (.of K)) i).inv ≫ (ProjectiveSpace.standardOpen n (Spec (.of K)) i).ι` |
| Composite immersion into projective space | Existential `j : X ⟶ ℙ(n; Spec (.of K))` with the displayed equality `j = e ≫ ...`. This specifies the composite rather than allowing an unrelated morphism |
| Take the scheme-theoretic closure, Xbar | `j.image`, the existing `Scheme.Hom.image` construction, with its canonical inclusion `j.imageι` |
| Open immersion X to Xbar | `IsOpenImmersion j.toImage`, using the canonical `Scheme.Hom.toImage` |
| Dense | `DenseRange j.toImage`, explicitly topological density |
| Xbar projective over K | `IsHProjective (j.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K))` |
| Equal Krull dimensions | `topologicalKrullDim j.image = topologicalKrullDim X` |

The structure map on the closure is its inclusion followed by the projective-space
projection. The canonical identity `j.toImage ≫ j.imageι = j`, the defining equality for
j, and the equation for e show that the open immersion is over K. These identities do
not add another independent hypothesis. Choosing a distinguished coordinate in an arbitrary
finite homogeneous-coordinate type is equivalent to writing P^N and its chart A^N: reindex
the finite type by Fin (N+1), sending i to 0. It excludes no value N, including N = 0.

### Dependency declarations read and used

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`
  (and the source signature of `Spec.map` was read).
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`,
  `AlgebraicGeometry.Scheme.Over`, its structure morphism, and `Scheme.Hom.IsOver`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-nagata-relative-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace`.
- `def-nagata-scheme-theoretic-closure`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `AlgebraicGeometry.Scheme.Hom.image`; the existing `imageι` and `toImage` in that module
  provide the inclusion and canonical factorization.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`. This source is absent from the older local checkout;
  its complete current server source was read using `scompile.py --source`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension` records
  `topologicalKrullDimAt` and `topologicalKrullDim`; both source definitions were read.
  The global dimension in this statement is Mathlib's `topologicalKrullDim`, with values
  in `WithBot ℕ∞`, preserving the dimension of the empty scheme.

The existing chart construction is
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`,
`AlgebraicGeometry.ProjectiveSpace.standardOpenIso` and `standardOpen`.
Its full signature and docstring identify precisely the affine chart of projective space.
This is a helper for the projective spaces already appearing in `def-kun-projective`,
not a new notion or a private definition.

Proof dependencies with recorded modules are imported without `public`:
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion`
(`exists_isImmersion_projectiveSpace`),
`WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`
(`ProperClosedModel`, `nonempty_properClosedModel`),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (`QuasiCompact.of_comp`), and
`Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
(`IsSchemeTheoreticallyDominant`). Properness is available through the public projectivity
dependency (`Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`). The recorded
closed-model interface is used as a proof input, not as a replacement definition of
the closure. Its signature was read, and it packages a suitable closed model rather
than asserting a theorem for every prescribed immersion. The proof can use the
scheme-theoretic-image API directly for the chosen chart immersion.
`lem-kun-dimension-extension` currently has no recorded Lean module; it is a proof
dependency, not needed to type this statement, and its future proof import is omitted.

### Source and edge cases

Read the blueprint node's original Markdown on the project server after finding that
the untracked literature checkout is absent locally (the public raw GitHub URL returns
404). Its statement agrees verbatim with the DAG. Its proof explicitly chooses a
polynomial presentation and the standard chart, takes scheme-theoretic closure, and
uses the generic points for the dimension equality. Also read Stacks
[01RG](https://stacks.math.columbia.edu/tag/01RG) for the closure open immersion and density,
and [0A21](https://stacks.math.columbia.edu/tag/0A21), parts (3) and (8), for the dense-open
dimension argument component by component.

- Empty X: allowed, with empty scheme-theoretic image, dense empty-to-empty immersion,
  and dimension bottom on both sides; the finite coordinate type may still be nonempty.
- No affine generators (N = 0): one homogeneous coordinate and an empty affine-coordinate
  subtype give A^0 and P^0. The theorem does not require a positive dimension.
- Nonreduced X: no reducedness is assumed; `j.image` is the scheme-theoretic image,
  retaining the scheme structure, rather than a topological closure or reduced subscheme.
- Reducible X and components of different dimensions: no integrality, connectedness,
  irreducibility, or equidimensionality hypothesis is added. A dense open contains all
  generic points, so the supremum of their transcendence degrees is unchanged.
- Arbitrary characteristic and non-algebraically-closed fields: only `Field K` is used.
- Universe: K, X, and finite coordinate types live in the common arbitrary universe u,
  as in the dependency projective-space API; no test-scheme or field-extension
  quantification is restricted to a smaller universe.

There is no `STATEMENT-DISPUTED` issue or statement correction.

### Searches and validation

Executed the prescribed `msearch.py` searches, with their logs in the sandbox:

- LeanFinder: "Every affine scheme of finite type over a field admits a dense open
  immersion into a projective scheme of equal Krull dimension". Eight hits concern Proj
  properness/finite type, its projection, the dominant global-spectrum map, and
  `Proj.fromOfGlobalSections`; none is this compactification theorem.
- Loogle: `"projective", "immersion"`. Zero hits.
- Mathlib grep: `projectiveClosure|projectiveCompactification|compactification|exists.*[Pp]rojective`
  in AlgebraicGeometry. Zero hits.
- LeanSearch: "Every finite type affine scheme over a field has a projective closure
  with the same dimension". Service unavailable (Internal Server Error); no absence
  conclusion drawn from this service.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for compactification and
  projective-existence patterns: curve-specific compactification results and general
  Chow models exist, but do not state this arbitrary-dimensional affine result with
  its dimension equality and specified chart/closure construction.
- Focused `rg` for `compactification-affine|AffineCompactification|affine_compactification|`
  `projective_compactification|exists_projective.*[Dd]ense` finds only the upstream
  integral-curve projective closure and the side dimension-at-most-one completion.
- The upstream blueprint-id search and `dag/lean_names_upstream.json` search found no
  existing declaration of `lem-kun-compactification-affine`. The new declaration name
  does not occur in the upstream or side sources.

`scompile.py Q30 lem-kun-compactification-affine` compiled the delivered module cleanly
as a separate file through the required local side-project overlay, with no errors or
warnings. Only the named theorem is postponed, with the node's complete proof route
in its docstring. The delivery dry run is the final mechanical check; an independent
second reader will provide the second-reading section and deliver.

## Second reading by Q30

I reread the node `lem-kun-compactification-affine`, its source place
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-compactification-affine.md`,
and the declaration in `Sheaf.AlgebraicGeometry.AffineProjectiveCompactification`.
The item-by-item match is:

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Field `K` | `(K : Type u) [Field K]`; exactly the stated arbitrary field, with no characteristic or algebraic-closure assumption. Pass. |
| Affine finite-type `K`-scheme `X` | `(X : Scheme.{u}) [IsAffine X] [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]`; this is the recorded finite-type convention and adds no hypothesis. Pass. |
| Finite homogeneous coordinates and distinguished chart | `∃ (n : Type u) (_ : Finite n) (i : n)`; the arbitrary finite index type with `i` represents `P^N` and its `A^N` standard chart, including `N = 0`. Pass. |
| Closed affine embedding | `e : X ⟶ 𝔸({k : n // k ≠ i}; Spec (.of K))` with `IsClosedImmersion e` and `e ≫ ... ↘ Spec (.of K) = X ↘ Spec (.of K)`; this is precisely a closed immersion over `K`. Pass. |
| Standard chart and composite | `j : X ⟶ ℙ(n; Spec (.of K))` together with `j = e ≫ (standardOpenIso ...).inv ≫ (standardOpen ...).ι`; the map is forced to be the displayed composite, rather than an unrelated projective map. Pass. |
| Scheme-theoretic closure | The target is `j.image`, with the canonical inclusion `j.imageι` and factorization `j.toImage`; this is Mathlib's scheme-theoretic image construction. Pass. |
| Open dense immersion | `IsOpenImmersion j.toImage ∧ DenseRange j.toImage`; these are exactly the open and topologically dense assertions. The over-`K` compatibility follows from the displayed equations and `j.toImage_imageι`; no extra independent clause is required by the node. Pass. |
| Projective closure over `K` | `IsHProjective (j.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K))`; this is the recorded finite-projective-space convention for `j.image` over `Spec K`. Pass. |
| Dimension equality | `topologicalKrullDim j.image = topologicalKrullDim X`; same order and same global Krull-dimension notion as the node. Pass. |

I checked the edge cases explicitly. The empty scheme is permitted (the existential can
choose a one-coordinate projective space, and both dimensions are the bottom value);
the coordinate type may have one element, so dimension zero is included; reducible and
nonreduced schemes are not excluded; arbitrary characteristic and non-algebraically
closed fields remain allowed; and all scheme, field, and coordinate universes are the
same arbitrary `u`, with no hidden smallness restriction. There is no index-set or
zero-object hypothesis in this statement.

For the dependency audit I opened the declarations for `Scheme`, `Spec`, `Over`,
`LocallyOfFiniteType`/`QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`,
`AffineSpace`, `Scheme.Hom.image`/`imageι`/`toImage`, `IsHProjective`, and
`topologicalKrullDim`. Their signatures are the notions used above; no private copy or
specialized replacement occurs. I also checked the projective chart declarations
`ProjectiveSpace.standardOpenIso` and `standardOpen`. Searches with `rg` in the source
checkout and side `lean/Sheaf`, the upstream-name index, Mathlib, and the prescribed
LeanFinder/Loogle/LeanSearch queries found no existing declaration of this theorem or
an equivalent arbitrary-dimensional affine projective compactification. The unavailable
LeanSearch service and rejected `IsHProjective` Loogle query were recorded as unavailable,
not treated as positive matches.

No mismatch was found, so no Lean or node statement was changed. The only mechanical
repair made by this reading was adding this section. The required separate compilation
of `lean/Sheaf/AlgebraicGeometry/AffineProjectiveCompactification.lean` via `scompile.py`
completed with no errors or warnings.
