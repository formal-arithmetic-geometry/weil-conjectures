## Worker report

The module `Sheaf.AlgebraicGeometry.DmOpenFiniteEtalePermanence` states
`CategoryTheory.dm_open_finite_etale_permanence`, with one `sorry` and no definitions.
The node's natural-language statement, proof and proof dependencies are unchanged.
Four already landed definition nodes are added to `stmt_deps` so that each reused
interface is explicit in the graph. There are no new nodes or dependency repairs.

Hypothesis and conclusion correspondence:

- A field k is `(k : Type u) [Field k]`; the base is `Spec (.of k)`.
- The stack X is a `BasedCategory.{v₁, w₁} (Over (Spec (.of k)))`, with
  `hX : IsDeligneMumfordModuliStack X`. This includes the CFG and stack hypotheses.
- Smoothness and finite type, including quasi-compactness, are
  `hft : HasSmoothFiniteTypeModuliAtlas X`. On a DM stack over a field this is
  equivalent to the smooth-atlas test in the node: an etale atlas is smooth;
  conversely, an etale atlas can be restricted to finitely many finite-type charts,
  and smoothness descends along its base change to a smooth atlas.
- Finite diagonal is `hdiag : HasFiniteModuliDiagonal X`. The recorded definition
  represents each two-scheme test and requires finiteness over their product, with
  BOTH projections identified. It does not confuse finiteness of a projection
  with finiteness of the diagonal.
- The open is `U : OpenModuliSubstack X`. Its full subcategory `U.category` uses
  the original projection. `property` and `pullback` give the full pullback-stable
  subcategory; `open_pullback` supplies an open subscheme after every scheme test,
  with the actual projection identified by a natural isomorphism over identities.
- The first four conjuncts assert that U is DM, smooth and finite type (including
  quasi-compactness), has finite diagonal, and has proper diagonal, respectively.
  They appear BEFORE the universal quantification over Y, so no decoration
  hypothesis is needed for the open conclusions.
- The decoration is any `Y : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))` and
  `p : BasedFunctor Y U.category`, with `IsFibredInGroupoids Y`. No stack condition
  is assumed for Y; it follows as part of the DM conclusion.
- For EVERY scheme `T : Over (Spec (.of k))` and map
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) U.category`, the hypothesis
  supplies E, `g : E ⟶ T` and an equivalence to `moduliTwoFiberProduct t p` with
  `IsFinite g.left ∧ Etale g.left`. `IsSchemeModuliBaseChange e g` requires that
  equivalence and its compatibility with the actual projection to T, by a natural
  isomorphism over identity base maps. This is a natural equivalence of categories
  fibred over T-schemes, not a bijection of isomorphism classes or an arbitrary map.
- The six decoration conjuncts assert Y DM, Y smooth finite type, Y finite diagonal,
  `IsRepresentableFiniteModuliMap p`, `IsEtaleModuliMap p`, and Y proper diagonal.
  The two map predicates together mean representable finite etale: each describes
  the actual scheme-test projection. A finite representation is a scheme, and
  its identification with an etale algebraic-space presentation transports etaleness.
- `HasProperModuliDiagonal` is precisely separatedness in this DM setting, as
  required by the node, and is asserted for both U and Y.
- There is no nonemptiness or surjectivity hypothesis on p. Scheme and field sizes
  use u throughout; the two CFG object/hom universe pairs are explicitly separate.

Dependency declarations read and reused (all names have their original namespaces):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` (the current
  name of the stale search-service `IsEtale` spelling).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `BasedCategory`/`BasedFunctor` conventions, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`, `discreteModuli`, `discreteModuliMap`,
  `IsDeligneMumfordModuliStack`, and the space-base-change atlas predicates.
- Added landed dependency `def-sfb-open-moduli-substack`, module
  `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack` and its `category`.
- Added landed dependency `def-sfb-finite-stack-scheme-tests`, module
  `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`: `HasFiniteModuliDiagonal`,
  `IsRepresentableFiniteModuliMap`.
- Added landed dependency `def-sfb-moduli-stack-properties`, module
  `Sheaf.AlgebraicGeometry.ModuliStackProperties`: `HasSmoothFiniteTypeModuliAtlas`,
  `HasProperModuliDiagonal`. The local source was absent, so the complete current
  server source was read with `scompile.py --source` before using it.
- Added landed dependency `def-sfb-moduli-chart-normalization`, module
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `IsSchemeModuliBaseChange`,
  `IsEtaleModuliMap`. No normalization condition is imposed on this theorem.

The stated proof dependencies have their modules imported: finite/proper, finite
composition, closed-immersion finite and smooth composition use the corresponding
Mathlib modules already public for the statement; the etale/smooth fibre theorem is
imported privately from `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`,
and the Noetherian scheme results from `Mathlib.AlgebraicGeometry.Noetherian`.
The three proof-only nodes `lem-sfb-finite-type-stack-affine-smooth-atlas`,
`lem-sfb-representable-fibred-category-stack`, and
`lem-sfb-representable-finite-stack-properties` currently have neither a Lean record
nor a Mathlib match; no speculative import or replacement axiom is introduced.
They are cited in the complete ten-step proof docstring and remain proof tasks.
They are not missing objects needed to TYPE the current statement.

Edge cases checked before writing: U may be the empty full subcategory, and the
empty atlas has all required properties. E and Y may be empty over a nonempty U;
there is no `Surjective g.left`. Disconnected opens, non-surjective finite etale
maps and characteristic p are unrestricted. No genus, level, connectedness,
reducedness or algebraically closed base-field condition is added. Nontrivial
stack automorphisms are retained in the categories and 2-fibre products.
The finite diagonal hypothesis ensures a separated stack, not trivial inertia.
No statement dispute or statement correction was necessary.

Searches made:

- `msearch.py leanfinder`: "Open substacks and finite etale covers of smooth finite
  type Deligne Mumford stacks have finite diagonal". Eight hits on scheme etale,
  diagonal and base-change lemmas; no stack permanence statement.
- `msearch.py loogle`: "IsDeligneMumfordModuliStack, IsFinite". No hits; the stack
  predicate is not a Mathlib identifier.
- `msearch.py leansearch`: "Representable finite etale morphism of categories
  fibred in groupoids after every scheme base change". Eight hits on scheme
  stability under base change and ordinary relative representability; no theorem
  about CFG open substacks or DM permanence.
- `msearch.py loogle`: the quoted phrase "finite etale". Zero hits.
- `msearch.py grep`, subdirectory AlgebraicGeometry:
  `FiniteEtale.*Moduli|RepresentableFiniteEtale|DeligneMumford|OpenSubstack`.
  Zero Mathlib hits.
- `rg` over project `lean/Sheaf` and upstream `lean/WeilConjectures` for stack,
  finite-diagonal, open-substack and atlas names found the four landed interfaces
  above. `rg` for `IsSchemeModuliBaseChange` and `IsEtaleModuliMap` found the chart
  normalization node's already usable interfaces, removing the need for a new node.
- `rg` over Mathlib, upstream and Sheaf for both the snake-case and camel-case
  proposed theorem names found no duplicate. Searching the blueprint ID upstream
  found none; its occurrences in `AbelianLevelCoarseModuli` are proof-docstring
  citations, not declarations of this result.
- `tools/blueprint_refs.py search 'finite etale'` found the existing finite-etale
  scheme material, not a duplicate of the present stack permanence statement;
  `ancestor` reports None, as already recorded for this node.

Validation: `scompile.py Q145 lem-sfb-dm-open-finite-etale-permanence <file>`
compiled sandbox and library module modes cleanly (10.6 s and 17.1 s), with no
errors or unexpected warnings. All universes and variables are explicitly bound,
`autoImplicit` is false, and the sole theorem body is `by sorry`.

## Second reading by Q145

A separate pass by the dispatched worker reread the original node, the final
signature and the reused predicate bodies. No second agent was started, as the
dispatcher forbids it; the maintainer supplies the independent delivery review.

The pass checked the field/base, DM and smooth finite-type hypotheses on X,
finite diagonal over the PRODUCT of tests, and the full pullback-stable open.
It checked that the U conclusions are independent of the later Y hypothesis.
It checked that Y is only assumed CFG, that every decoration test has simultaneous
finite and etale properties on the SAME g, and that the equivalence identifies
the first projection. The conclusion's finite and etale map predicates express
the same representable property, while proper diagonal appears for both outputs.
Every conjunct of the node is covered; empty and nonsurjective cases are retained.
No hypothesis or definition was strengthened. The only graph changes are the four
landed definition dependencies and the Lean attachment. No mismatch required repair.
