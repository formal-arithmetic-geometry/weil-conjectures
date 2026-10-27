## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSchemeCoherentDerivedImage` states
`AlgebraicGeometry.proper_scheme_coherent_derived_image`, with one `sorry` and no
new definitions. The statement is unchanged. No new or repaired dependency nodes
are needed. Source read: `literature/stacks-project/perfect.tex`, lines 2662–2682,
Tag 0D0B, lemma-direct-image-coherent-bdd-below. The source allows locally finite
type f with proper cohomology supports; this node explicitly specializes to proper f.
Closed cohomology supports are then proper over the base. The node's five proof
steps are included in the theorem docstring and all recorded proof modules are imported.

Hypothesis and conclusion correspondence:

- Schemes and their morphism: `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Noetherian S in the node's explicitly expanded sense: `[IsLocallyNoetherian S]`
  and `[CompactSpace S]`. CompactSpace imposes no separation condition.
- Proper f: `[IsProper f]`; Mathlib's universally closed condition supplies the
  quasi-compactness needed to turn locally finite type into finite type.
- Zariski structure-sheaf modules: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`
  and the corresponding S category. This is the carrier used by the recorded
  scheme derived-image interface, rather than a new module category.
- Unbounded derived categories: `(G : schemeDerivedCategory X)` and the supplied
  `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wS}` instances. Their localization
  morphism universes are independent; these are choices of localization, not
  boundedness, resolution, or cohomological assumptions.
- Coherent source cohomology: `hcoherent : ∀ j : ℤ, RingedSpace.IsCoherent ...`
  applied to `(DerivedCategory.homologyFunctor ... j).obj G`.
  The exact coherence predicate includes finite type and finite-type kernels of
  every map from finite free modules on every open. The conjunction
  IsQuasiCoherentFiniteType is not used as a substitute for coherence.
- Vanishing in all sufficiently negative degrees: `hbelow : ∃ a : ℤ, ∀ j : ℤ,
  j < a → IsZero (...)`. All degrees, including negative integers, are retained.
- Canonical Rf_*G: `((schemeDerivedDirectImage f).obj G)` in both conclusions.
  This is the recorded K-injective derived direct-image construction, with no
  arbitrary functor or replacement morphism.
- First conclusion: `∀ j : ℤ, RingedSpace.IsCoherent S.toRingedSpace ...` says
  every cohomology sheaf of Rf_*G is coherent.
- Second conclusion: `∃ a : ℤ, ∀ j : ℤ, j < a → IsZero ...` says the derived
  image is bounded below. It does not add an upper bound or require that the
  output bound be the input witness (the proof can in fact preserve that bound).

Dependency declarations read and used, with their full signatures/docstrings
inspected in the source files:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation of the same `SheafOfModules` used by the scheme API.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`. Cohomology is `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`, as the repaired dependency record says.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`. Its domain/codomain are the shared
  `schemeDerivedCategory` of `WeilConjectures.AlgebraicGeometry.DerivedCategory`.

Plain proof imports correspond to every other proof dependency:
`DerivedCategory.TStructure.t` (Mathlib.Algebra.Homology.DerivedCategory.TStructure),
`SheafOfModules.isGrothendieckAbelianOfUniverses`
(Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses),
`SheafOfModules.module_pullback_pushforward_adjunction`
(Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction),
`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`
(Mathlib.CategoryTheory.Adjunction.Limits),
`CategoryTheory.exists_truncationHypercohomology`
(WeilConjectures.CategoryTheory.TruncationHypercohomology),
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`
(WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex), and
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`
(WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum).

Edge cases checked mathematically before writing: G = 0; empty X or S;
f = identity; a complex with one nonzero coherent cohomology sheaf in any integer
degree (including negative degrees); a bounded below complex unbounded above;
and the boundary degrees n = a and n = a-1 in the filtration proof. In degree
n = a the filtration has one potentially nonzero graded term. Below a it is
zero. There is no characteristic restriction, nonemptiness, affineness, bounded
above hypothesis, or site change. The universal scheme universe u and independent
localization universes introduce no equality restriction on derived morphism sizes.

Searches performed through the prescribed msearch.py wrapper (raw tool outputs
are also recorded by that wrapper in the sandbox searches.jsonl):

- leanfinder: "Proper pushforward preserves bounded below derived complexes with
  coherent cohomology on a Noetherian scheme" — eight hits, including ordinary
  pushforward and DerivedCategory.IsGE, but no coherence preservation theorem.
- leansearch: "Proper derived pushforward preserves bounded below coherent
  cohomology" — eight hits about ordinary pushforward and its adjunction and
  additivity, none asserting the present result.
- loogle: `AlgebraicGeometry, coherent, schemeDerivedDirectImage` — unknown
  identifier AlgebraicGeometry, zero hits; repaired with the string-name query below.
- loogle: `"coherent", "pushforward"` — five hits about quasi-coherent ordinary
  pushforward, not coherent bounded below derived image.
- grep: `(coher.*(derived|pushforward|direct.image))|((derived|pushforward|direct.image).*coher)`
  — seven Mathlib hits, all ordinary quasi-coherent pushforward.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for proper/coherent derived images,
  bounded/IsGE and the item id: no existing declaration for this node. The exact-id
  hit in ProperSchemeCoherentExtFinite.lean is a proof reference, not a statement.
  Nearby DirectImageBoundedCoherent and NoetherianProperBoundedCoherentImage have
  an upper-bound hypothesis. They do not give the bounded-below result.

No STATEMENT-DISPUTED flag or statement correction is needed. All variables and
universes are explicit, with `set_option autoImplicit false`. The module compiles
through scompile.py in both sandbox and library modes (2.9 seconds each), with
no errors or disallowed warnings. The only postponed theorem is this node's theorem.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
