## Worker report

States `AlgebraicGeometry.exists_relative_complex_noetherian_cohomology_approximation`
in `Sheaf.AlgebraicGeometry.RelativeComplexNoetherianCohomologyApproximation`.
Its proof is `sorry`; the only other declaration is the concrete definition
`relativeApproximationScalarAdjoint`, applying the recorded normalized extension/restriction
Hom equivalence to derived sections of gamma followed by the normalized Leray comparison.
No existing node, statement, definition, or dependency record was changed except the item's
`lean` field. No new nodes or dependency modules are needed.

Clause-by-clause correspondence:

- A commutative ring is `A : CommRingCat.{u}`. The original structure morphism is
  `f : X ⟶ Spec A`, with `X : Scheme.{u}`.
- Separated finite type is `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  These are genuine hypotheses on f, not properties of an identity morphism.
- `E : schemeDerivedCategory X` is the given unbounded derived object.
  `hE : X.IsPseudoCoherentRelativeTo f E` uses the dependency's exact definition;
  its covers and embeddings can vary with the integer degree.
- Quasi-coherence is `schemeDerivedQCohProperty X E`, for all integer degrees.
  The upper bound is `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H^i(E))`, with H written
  using `DerivedCategory.homologyFunctor` on the shared module-sheaf category.
- Each integer n has its own existential choices: `∀ n : ℤ, ∃ A₀ : CommRingCat.{u}, ...`.
  The coefficient ring is required to satisfy `IsNoetherianRing A₀`.
- The ring map A₀ to A is encoded contravariantly by `g : Spec A ⟶ Spec A₀`;
  `affineBaseRingMap g` recovers it using the canonical GammaSpec identifications.
  Full faithfulness of Spec ensures this quantifies over exactly all ring maps.
- The model is `X₀ : Scheme.{u}` with `f₀ : X₀ ⟶ Spec A₀`, and the three conjuncts
  `IsSeparated f₀`, `LocallyOfFiniteType f₀`, `QuasiCompact f₀`.
- The morphisms are `u₀ : X ⟶ X₀` and `j : X ⟶ pullback f₀ g`, with
  `IsClosedImmersion j`, `j ≫ pullback.fst f₀ g = u₀`, and
  `j ≫ pullback.snd f₀ g = f`. These express the stated closed immersion over
  Spec A and its projection u. Pullback commutativity implies u is over Spec A₀.
- `E₀ : schemeDerivedCategory X₀` has `RingedSpace.IsCoherent` cohomology in
  every degree. Its cohomology vanishes when `i < a ∨ b < i` for some integer bounds
  a,b; thus precisely bounded coherent cohomology, with no perfectness assumption.
- `γ : E₀ ⟶ (schemeDerivedDirectImage u₀).obj E` is the required derived morphism.
- `c₀` and `c` expose the canonical comparison that is implicit in the words
  induced map on derived global sections. The equation `(c₀.hom.app M) x = x`
  fixes the actual identity on underlying sections. The displayed equation for every
  homotopy-category J specifies its right-derived lift by the universal derived unit,
  exactly as `exists_affineSectionsCompositionComparisons` does. These are
  characterizations of canonical comparison data, not arbitrary identifications.
- Alpha is `relativeApproximationScalarAdjoint f f₀ g u₀ E E₀ γ c`, with source
  `(affineDerivedExtension g).obj ((affineDerivedGlobalSections f₀).obj E₀)` and
  target `(affineDerivedGlobalSections f).obj E`. The former is derived extension,
  constructed with K-flat resolutions, along the actual recovered coefficient map.
  `affineDerivedGlobalSections` uses unbounded structure-module derived sections.
- The homology maps of this actual alpha satisfy `IsIso` for every `n < i` and
  `Epi` in degree n. In ModuleCat, Epi is equivalent to surjectivity; this avoids
  a second underlying-function convention.
- `(IsProper f → IsProper f₀)` expresses that the same existential data can be
  chosen proper in the proper case. No isomorphism with an ordinary base change,
  flatness of g, boundedness below of E, or independence of n is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- The convention node def-pc-morphism-conventions supplies no new declaration;
  use Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` directly.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`; their full docstrings fix the common
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)` carrier.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsPseudoCoherentRelativeTo` and `Scheme.IsMPseudoCoherentRelativeTo`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the exact coherence predicate
  `RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`, read in full;
  quasi-coherent finite type alone is not used as the definition of coherence.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, computed using K-injectives.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.homologyFunctor`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `MorphismProperty.kFlat`, the recorded two-sided quasi-isomorphism-preservation predicate.
  The existing derived-extension construction uses the K-flat machinery directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and scheme limits:
  `pullback`, its projections and condition, as recorded for def-pc-fibre-product.
- `WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`:
  `affineDerivedGlobalSections`, `affineGlobalSections`, `affineGlobalSectionsDerivedIso`,
  `affineBaseRingMap`, `affineDerivedExtension`, `affineDerivedExtensionAdjunction`.
  Their full definitions were read, including normalization to the concrete derived
  counit, and the K-flat construction. The matching form of the normalized sections
  comparison was read in `AffineSectionsCompositionComparisons`.

The theorem binds the shared sheaf localizations for all schemes and module
localizations for all rings in the fixed size universe. This matches the existing relative
pseudo-coherence and affine-extension APIs. `u` and `w` are explicit and `autoImplicit`
is false. All modules of recorded non-Mathlib proof dependencies are imported plainly;
statement imports are public. The two proof-only dependencies without a recorded module,
lem-sfb-relative-m-pseudocoherent-high-qcoh and
lem-sfb-prescribed-envelope-relative-sheaf-descente, cannot yet contribute imports.

Edge cases checked: E=0; X empty (including the zero base ring); positive, zero,
and negative n; complexes unbounded below; non-flat A₀-to-A; nonproper f; proper f;
no equality X=X₀_A and no descent equality for E. All remain in the statement.
The upper and lower bounds use strict inequalities so endpoints remain permitted.
Epi is required at n, rather than erroneously an isomorphism there. Canonical
comparison normalization rules out substituting an arbitrary automorphism of sections.

Searches performed:

- msearch.py leanfinder, query “Noetherian cohomological approximation of relative
  pseudo coherent complexes with scalar extension of derived global sections”:
  eight hits on ordinary t-structure representatives and related derived-category
  results; none gives Noetherian relative-complex approximation.
- msearch.py loogle, query `ModuleCat.extendScalars, ModuleCat.restrictScalars`:
  twelve hits giving the ordinary extension/restriction adjunction and its maps;
  these are already used by the project's K-flat derived extension, not a match
  for the approximation theorem.
- msearch.py grep, query `pseudo.?coher|cohomolog.*[Aa]pproxim`: zero Mathlib hits.
- rg of `noetherian.*[Aa]pprox|[Aa]pprox.*[Cc]ohom|[Rr]elative.*[Cc]omplex` in
  lean/WeilConjectures and lean/Sheaf found scheme/ring Noetherian approximations
  and unrelated derived-complex constructions, no exact theorem.
- rg of `derivedGlobalSections|DerivedGlobalSections|derived.*[Ss]calar|
  scalar.*[Aa]djoint|derived.*[Gg]lobal|extendScalars.*[Dd]erived` and subsequent
  narrower searches found the canonical affine APIs used above. No replacement
  derived sections, tensor, or coherence definition was introduced.
- rg of this item's id in lean/WeilConjectures found no existing declaration.
  rg of both new declaration names in the project and dag/lean_names_upstream.json
  found no collisions.

Source limitation inherited unchanged: the paragraph after Stacks Tag 0CSD states
Kiehl's general proper direct-image assertion, not this approximation lemma.
The node explicitly calls the approximation agent-formulated and the primary source
WANTED. Read perfect.tex at lemma-flat-proper-pseudo-coherent-direct-image-general
and more-morphisms.tex at definition-relative-pseudo-coherence and
lemma-relative-pseudo-coherence. The latter supports exactly the quasi-coherence
and upper-bound clauses. No counterexample was found to the approximation claim,
and this delivery neither upgrades its source status nor silently corrects its statement.

Validation: scompile.py compiled the module in sandbox and library module mode
with no errors or unexpected warnings (28.9 s and 10.0 s respectively).

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
