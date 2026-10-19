## Worker report

The module `Sheaf.AlgebraicGeometry.SchematicDensityGenericFibreOpen` states
`AlgebraicGeometry.schematicDensityGenericFibreOpen` with `sorry` proof. It uses the canonical
Mathlib fibre `Scheme.Hom.fiber`, the canonical open-subscheme inclusion `U.ι`, and the
canonical pullback inclusion `pullback.snd U.ι (f.fiberι y)`. The componentwise injectivity
condition on `Scheme.Hom.app` renders the injective sheaf map
`𝒪_{X_y} → (j_y)_* 𝒪_{U_y}` from Tag 01RE.

The hypotheses render the node clause by clause:

- `f : X ⟶ Y` is the scheme morphism, with `[LocallyOfFiniteType f]` and `[QuasiCompact f]`
  rendering finite type as recorded by `def-weil-finite-type-morphism`.
- `hY : IsIrreducible (Set.univ : Set Y)` renders irreducibility of `Y` using the
  `IsIrreducible` definition behind `def-weil-irreducible-components`.
- `η : Y` and `hη : IsGenericPoint η (Set.univ : Set Y)` render the generic point from
  `def-sc-generic-point`.
- `U : X.Opens` renders an arbitrary open subscheme of `X` and `U.ι` its canonical open
  immersion.
- `f.fiber η` and `f.fiber y` render `X_η` and `X_y`; `pullback.snd U.ι (f.fiberι y)` is the
  canonical base-changed open immersion `j_y`. The hypothesis `hηdense` says that every
  component of its structure-sheaf map is injective on sections. The conclusion supplies an
  open `V`, proves `(V : Set Y).Nonempty`, and requires the same componentwise injectivity
  for every `y ∈ V` and every open of `f.fiber y`.

Dependency declarations used: `AlgebraicGeometry.Scheme` and `Scheme.Hom` from
`Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
`AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι` from `Mathlib.AlgebraicGeometry.Fiber`;
`AlgebraicGeometry.IsGenericPoint` from `Mathlib.Topology.Sober`; and
`AlgebraicGeometry.IsSchemeTheoreticallyDominant` was searched but is not needed because the
statement records the sheaf-map injectivity directly via `Scheme.Hom.app`.
The Mathlib leaf `irreducibleComponents` was checked for the irreducibility definition.

Edge cases checked before writing: `U = ⊥` makes the generic injectivity hypothesis impossible
unless the generic fibre is empty; `U = ⊤` gives the identity inclusion; `V` is explicitly
nonempty; an empty total scheme is allowed (the theorem can choose any nonempty open of an
irreducible base); and no Noetherian, reduced, quasi-separated, or separated hypotheses are
introduced. The construction uses pullback fibres, so residue fields and the fibre product are
not replaced by arbitrary choices.

Searches made: `msearch.py NP lem-trf-schematic-density-generic-fibre-open leanfinder` for
“finite type irreducible scheme open generically schematically dense spread to nearby fibres”
returned only dominance and generic-spreading declarations, with no exact theorem;
`msearch.py ... loogle "IsSchemeTheoreticallyDominant"` returned the Mathlib dominance class
and its kernel/app-injective lemmas, not this fibre-spreading result; `msearch.py ... grep`
for `generic.*[Dd]ense|[Ss]chemeTheoreticallyDominant.*fiber` found only
`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`; `rg` over WeilConjectures and
`lean/Sheaf` found no matching theorem. The recorded Mathlib declarations and their full
signatures/docstrings were read in `Fiber.lean`, `FiniteType.lean`, `Topology/Sober.lean`,
`Topology/Irreducible.lean`, and `Morphisms/SchemeTheoreticallyDominant.lean`.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
