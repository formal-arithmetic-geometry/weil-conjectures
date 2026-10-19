## Worker report

The module `Sheaf.Paper.AffineLineSupportGeometry` states
`WeilConjectures.PurityFiniteSetting.affineLine_support_geometry`, with a single
`sorry` proof and no new definitions. The natural-language statement is unchanged.
The proof docstring records all five steps and their DAG citations.

Hypotheses and constructions, clause by clause:

- A field k: `(k : Type u) [Field k]`. This is any field, of any characteristic,
  with no finite-field or coefficient assumptions.
- A scheme Y of finite type over k: `(Y : Scheme.{u})`,
  `[Y.Over (Spec (.of k))]`, `[LocallyOfFiniteType (Y ↘ Spec (.of k))]` and
  `[QuasiCompact (Y ↘ Spec (.of k))]`. The two morphism properties are exactly
  finite type, as stipulated by def-weil-finite-type-morphism.
- X is the relative affine line, with projection p: the published `Line Y`
  is definitionally `AffineSpace (ULift.{u} (Fin 1)) Y`, and `lineProjection Y`
  is its canonical projection to Y. The singleton coordinate type has exactly
  one element, including at universe zero.
- The zero section s is the published `zeroSection Y`, defined using
  `AffineSpace.zeroSection`, which is `homOfVector (𝟙 Y) 0`. Its coordinate
  pullback is zero by `AffineSpace.zeroSection_appTop_coord`. Under the
  polynomial affine charts `AffineSpace.SpecIso`, this is the constants-preserving
  evaluation map t ↦ 0. It is a closed immersion by
  `AffineSpace.isClosedImmersion_zeroSection`.
- U with its open subscheme structure is the published `Punctured Y`, namely
  `((Line Y).basicOpen (coordinate Y)).toScheme`; j is `openImmersion Y`, the
  canonical inclusion of precisely that open. `AffineSpace.range_zeroSection`
  identifies the zero-section image with simultaneous coordinate vanishing.
  For the singleton coordinate type this identifies U with the exact complement
  X minus s(Y). This is a definition-level identification, not an arbitrary open
  immersion supplied as additional data. On the polynomial chart it is D(t),
  the spectrum of R[t] localized at t, equivalently the Laurent polynomial ring.
- X finite type over k: the first conclusion is
  `LocallyOfFiniteType (lineProjection Y ≫ Y ↘ Spec (.of k)) ∧`
  `QuasiCompact (lineProjection Y ≫ Y ↘ Spec (.of k))`.
- U finite type over k: the second conclusion is the same conjunction for
  `puncturedProjection Y ≫ Y ↘ Spec (.of k)`;
  `puncturedProjection Y` is definitionally `openImmersion Y ≫ lineProjection Y`.
- Y, X and U Noetherian: `IsNoetherian Y ∧ IsNoetherian (Line Y) ∧`
  `IsNoetherian (Punctured Y)`. The Mathlib class extends exactly
  `IsLocallyNoetherian` and `CompactSpace`, so includes global quasi-compactness.
- j quasi-compact: the final conclusion is `QuasiCompact (openImmersion Y)`.

Dependencies used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs; its full class signature
  and docstring were read.
- def-pc-scheme: `AlgebraicGeometry.Scheme` and its morphisms,
  Mathlib.AlgebraicGeometry.Scheme.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- def-sbc-affine-space: `AlgebraicGeometry.AffineSpace`,
  Mathlib.AlgebraicGeometry.AffineSpace, with its canonical projection,
  `coord`, `homOfVector`, and `SpecIso` as read in that module.
- def-weil-closed-immersion and def-weil-open-immersion:
  `AlgebraicGeometry.IsClosedImmersion` in
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and
  `AlgebraicGeometry.IsOpenImmersion` in Mathlib.AlgebraicGeometry.OpenImmersion.
  These are realized by the existing section and inclusion constructions.
- pqf-def-locnoeth: `AlgebraicGeometry.IsLocallyNoetherian` in
  Mathlib.AlgebraicGeometry.Noetherian; `IsNoetherian` packages its conjunction
  with compactness without a new definition.
- Added the already landed def-pur-affine-line-datum to stmt_deps, using
  `WeilConjectures.PurityFiniteSetting.Line`, `coordinate`, `Punctured`,
  `zeroSection`, `lineProjection`, `puncturedProjection`, and `openImmersion`
  in Sheaf.Paper.PurityAffineLineDatum. Read all of these definitions and their
  docstrings. These geometric declarations take arbitrary schemes and require
  none of the coefficient assumptions used elsewhere in that module. This
  addition reuses the exact parent datum instead of defining another punctured line.

Every proof dependency is a Mathlib leaf or an already used definition.
The imports provide the finite-type composition/base-change instances,
`LocallyOfFiniteType.isLocallyNoetherian`,
`QuasiCompact.compactSpace_of_compactSpace`, `Scheme.compactSpace_of_isAffine`,
`quasiSeparatedSpace_of_isAffine`, `locallyOfFiniteType_of_isOpenImmersion`,
`PrimeSpectrum.isTopologicalBasis_basic_opens`,
`PrimeSpectrum.localization_away_isOpenEmbedding`, and
`PrimeSpectrum.localization_away_comap_range`. Their signatures were inspected.
The latter two proof-only modules are imported without `public`.

Edge cases checked mathematically before writing: Y empty (both the line and its
open complement are empty, hence all conclusions hold); Y = Spec k (the rings
are k[t] and k[t,t⁻¹]); Y = Spec k[ε]/(ε²) (no reducedness assumption is used);
Y = projective line (no global affineness assumption); a nonseparated finite-type
Y (no separatedness is imposed); and positive characteristic. The coordinate
is a global section for arbitrary Y. There is no nonempty hypothesis or
finite-field specialization. All variables and the universe u are explicitly bound.

Searches performed:

- msearch.py leanfinder: “For a finite type scheme over a field its affine line
  and punctured affine line are Noetherian and the open inclusion is quasi compact”.
  Eight results, including IsNoetherian,
  instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion,
  quasiCompact_of_noetherianSpace_source, and IsAffineOpen.isCompact.
  These give components, not the complete conjunction about this datum.
- msearch.py loogle: `AlgebraicGeometry.AffineSpace, AlgebraicGeometry.IsNoetherian`:
  zero results.
- msearch.py grep: `zeroSection|Noetherian|instLocallyOfFinitePresentation`
  with subdirectory `AlgebraicGeometry/AffineSpace.lean`: zero results (the
  wrapper's subdirectory selector is not a file selector).
- msearch.py grep: `AffineSpace|instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion`
  under AlgebraicGeometry: ten results including the AffineSpace module and
  its basic definitions, no complete statement.
- rg in WeilConjectures and lean/Sheaf for affineLine, affine-line,
  AffineLine, zeroSection, and punctured: located the upstream zero-section
  construction, its closed-immersion and range theorems, and the published
  PurityAffineLineDatum definitions reused here.
- rg for the item id in WeilConjectures: no result.
- rg for `AffineLineSupportGeometry|affineLine_support_geometry` in
  dag/lean_names_upstream.json, lean/Sheaf and WeilConjectures: no result.

No new node, dependency repair, statement correction, or disputed statement.

Validation: scompile.py compiled the sandbox file and the actual module path
successfully, with no errors or warnings (34.3 s and 23.1 s, each below 60 s).

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
