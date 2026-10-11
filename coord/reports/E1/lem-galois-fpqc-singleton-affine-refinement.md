## Worker report

Module `Sheaf.AlgebraicGeometry.FpqcSingletonAffineRefinement` states
`AlgebraicGeometry.Scheme.exists_fpqc_singleton_affine_refinement`; its proof is `sorry`.
Source: Stacks Project, Topologies, Definition 022B and Lemma 022E. The requested
`literature/stacks-project/topologies.tex` is absent in this checkout; I read the local
copy at `/home/ubuntu/c1-stacks-review/topologies.tex`, lines 2888-2895 and 3151-3164.

Statement correspondence:

- Scheme objects and morphism `f : X ⟶ S`: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Affine base: `[IsAffine S]`.
- Singleton fpqc hypothesis: `hf : Presieve.singleton f ∈ fpqcPrecoverage S`.
- Finite number `m ≥ 0`: `∃ (n : ℕ)`; `Fin n` indexes the opens, including `n = 0`.
- Affine open subschemes of `X`: `U : Fin n → X.Opens` and
  `∀ j, IsAffineOpen (U j)`; their schemes are `(U j).toScheme`.
- Their coproduct: `let X' := ∐ (fun j : Fin n ↦ (U j).toScheme)`.
- Map induced by the open inclusions: `h : X' ⟶ X` and
  `∀ j, Sigma.ι (fun k ↦ (U k).toScheme) j ≫ h = (U j).ι`.
- Composite map and its relation to `f`: `g : X' ⟶ S` and `g = h ≫ f`.
  This equation is also the assertion that `h` is over `S`.
- Affineness, flatness, and surjectivity: `IsAffine X' ∧ Flat g ∧ Surjective g`.
- Singleton fpqc conclusion: `Presieve.singleton g ∈ fpqcPrecoverage S`.

Dependencies used: `def-pc-scheme` via `Mathlib.AlgebraicGeometry.Scheme`'s
`AlgebraicGeometry.Scheme`; `def-weil-pbc-fpqc-covering` via
`Mathlib.AlgebraicGeometry.Sites.Fpqc`, `AlgebraicGeometry.Scheme.fpqcPrecoverage`;
`def-weil-flat-morphism` via `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`AlgebraicGeometry.Flat`; `def-weil-surjective-morphism` via
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`;
`lem-weil-pbc-scheme-coproduct-family` via `Mathlib.AlgebraicGeometry.Limits`,
`AlgebraicGeometry.instHasColimitsOfShapeDiscreteSchemeOfSmall`, `sigmaOpenCover`,
`disjoint_opensRange_sigmaι`, and `CategoryTheory.Limits.Sigma.ι`.
The opens and their inclusions are `Scheme.Opens.toScheme` and `Scheme.Opens.ι`.

Edge cases: `n = 0` is admitted for empty `S`; empty `X` and the zero ring are not
excluded by the universe or type choices. An identity cover of affine `S` admits
`n = 1` and `U 0 = ⊤`; a flat surjection between affines likewise admits `U 0 = ⊤`.

Searches:

- `msearch leanfinder` query "finite affine open refinement of singleton fpqc
  covering of affine scheme with coproduct flat surjective": eight related hits,
  including `Scheme.affineCover` and `OpenCover.affineRefinement`; no exact match.
- `msearch loogle` query "AlgebraicGeometry.QuasiCompactCover.exists_hom,
  AlgebraicGeometry.Scheme.fpqcPrecoverage": zero hits.
- `msearch grep` query `fpqc|affine.*refin|QuasiCompactCover` in
  `Mathlib/AlgebraicGeometry`: related cover definitions and refinements; no exact match.
- `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for fpqc and affine
  refinement found `Scheme.exists_finite_affine_flat_of_mem_fpqcTopology` in
  `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`: it starts from a
  covering sieve and supplies finite affine schemes in that sieve, without the
  asserted opens inside the particular source `X`, their coproduct, or `h`.
- `grep -rn` for the node ID in `WeilConjectures` and `rg` for fpqc refinement in
  `lean/Sheaf`: no match.

The source proof is reflected in the declaration docstring: take affine opens from
the fpqc condition over the whole base; form their finite coproduct and induced map;
check surjectivity and flatness; then verify the singleton fpqc condition.

## Second reading by E1

I read the node and Stacks Project, Topologies, Definition 022B and Lemma 022E
against the module. Definition 022B assumes a scheme as base, flat component
maps, and a finite affine-open image cover over each affine open of the base.
Lemma 022E adds precisely the hypothesis that the base is affine.

- Objects: the node's affine scheme `S` is `{S : Scheme.{u}} [IsAffine S]`;
  its source scheme and arrow are `{X : Scheme.{u}} (f : X ⟶ S)`.
  Verdict: exact, with no Noetherian, field, characteristic, or finiteness
  hypothesis on either scheme.
- Covering hypothesis: the one-member fpqc family is
  `hf : Presieve.singleton f ∈ fpqcPrecoverage S`. The dependency node records
  Mathlib's `Scheme.fpqcPrecoverage`; `QuasiCompactCover` is tagged 022B and
  expresses the finite affine-open image condition. Verdict: exact.
- Finite family: `∃ (n : ℕ) (U : Fin n → X.Opens)` renders the integer `m ≥ 0`
  and the indexed opens of `X`; `∀ j, IsAffineOpen (U j)` renders their
  affineness, and `(U j).toScheme` is the actual open subscheme. Verdict: exact.
- Coproduct and inclusions: `let X' := ∐ (fun j : Fin n ↦ (U j).toScheme)`
  renders `X'`; `h : X' ⟶ X` and
  `∀ j, Sigma.ι (fun k ↦ (U k).toScheme) j ≫ h = (U j).ι` make `h` the map
  induced by all open inclusions. The dependency's coproduct instance and
  `Sigma.ι` are the same scheme coproduct, including the empty index.
  Verdict: exact.
- Map over the base: `g : X' ⟶ S` and `g = h ≫ f` render the composite and
  assert that `h` is over `S`. Verdict: exact.
- Conclusions: `IsAffine X' ∧ Flat g ∧ Surjective g ∧
  Presieve.singleton g ∈ fpqcPrecoverage S` renders every remaining clause,
  using the dependency nodes' Mathlib notions of affine scheme, stalkwise
  flatness, topological surjectivity, and fpqc covering. Verdict: exact.

Edge cases: `Fin 0` allows the empty family for empty `S`; `n = 1` covers the
identity on affine `S`. No nonempty-scheme, nonzero-ring, positive-index,
characteristic, or extra universe binder was inserted. `Scheme.{u}` and
`Fin n` use the same scheme universe as the coproduct dependency.

Independent searches: `msearch.py ... leanfinder` with "fpqc cover affine
scheme finite affine open refinement source map" returned related affine
cover declarations but no exact theorem. `msearch.py ... loogle` with
`AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact`
found the finite affine-open witness for a quasi-compact cover, without this
coproduct package. `msearch.py ... grep` with
`singleton.*fpqc|fpqc.*affine|affine.*refinement` found the singleton fpqc
membership lemma and open-cover refinement, but no exact statement. An `rg`
search of `WeilConjectures`, Mathlib's algebraic geometry files, and this
project's `lean/Sheaf` found the existing theorem about a finite affine
family in an fpqc sieve; it does not require those schemes to be opens of
this particular `X`, nor supply the map `h` and the asserted coproduct.

No mismatch was found; the module and node signature needed no change.
The file compiled without errors or warnings.
