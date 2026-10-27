## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteDominantNormalAffineChartRings` states
`AlgebraicGeometry.finite_dominant_normal_affine_chart_rings`, with its sole proof `sorry`.
No new definition, dependency repair, or statement correction is needed.

Hypotheses and conclusions, matched to the node:

- The schemes are `{V B : Scheme.{u}}`; `q : V ⟶ B` is the given morphism.
  `[IsIntegral V]` supplies integrality of V. `hB : IsNormalScheme B` unfolds to
  `IsIntegral B ∧ ∀ b, IsDomain (B.presheaf.stalk b) ∧
  IsIntegrallyClosed (B.presheaf.stalk b)`, exactly integrality and the stipulated
  integrally closed local domains on B. Bundling these clauses adds no assumption.
- `[IsFinite q]`, `[IsDominant q]`, and `[IsLocallyNoetherian B]` render finite,
  dominant, and locally Noetherian, respectively.
- The first conjunct quantifies over every index type `I : Type v` and family
  `U : I → B.Opens`. These are open subsets, not abstract charts with arbitrary maps.
  `hU : ∀ i, IsAffineOpen (U i)` is affineness, `(⨆ i, U i) = ⊤` is the cover,
  `∀ i, Nonempty (U i)` excludes empty members, and
  `∀ i, IsNoetherianRing Γ(B, U i)` is precisely the Noetherian coordinate-ring assumption.
- For each member, `Nonempty (q ⁻¹ᵁ U i)` states nonemptiness of the inverse image.
  The notation already constructs an open subset of V by continuous inverse image.
  `∃ hW : IsAffineOpen (q ⁻¹ᵁ U i), ...` supplies its affineness.
- The canonical coordinate rings are `A_i = Γ(B, U i)` and
  `C_i = Γ(V, q ⁻¹ᵁ U i)`. For an affine open, Mathlib's `IsAffineOpen.isoSpec`
  identifies its open subscheme with the spectrum of this ring. Thus these are the
  rings of the stated charts, without choosing unrelated presentations.
- The ring map `φ_i` is `(q.app (U i)).hom`. The equation
  `hW.fromSpec ≫ q = Spec.map (q.app (U i)) ≫ (hU i).fromSpec`
  says that on these spectrum charts the restriction of q is induced by φ_i.
  Both `fromSpec` maps are the canonical open immersions with the chart images;
  their factorization equation expresses the restricted morphism, including its sheaf map.
- `Function.Injective (q.app (U i)).hom` is injectivity of this exact map.
  `IsDomain Γ(B, U i) ∧ IsIntegrallyClosed Γ(B, U i)` is the normal-domain claim;
  `IsDomain Γ(V, q ⁻¹ᵁ U i)` is the domain claim for C_i.
  `(q.app (U i)).hom.Finite` unfolds to `Module.Finite A_i C_i` for the
  algebra induced by this exact ring homomorphism, so it is module finiteness via φ_i.
- The final conjunct independently asserts existence of an index type, open family,
  covering equality, and affineness, nonemptiness, and Noetherian section ring for
  every member. It does not assume an already chosen cover exists. An index type
  in `Type u` suffices by choosing one affine neighborhood per point of B;
  the universal assertion uses the independent universe v and covers arbitrary index sets.

Dependency declarations read and used (no private replacements):

- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (including its affine inverse-image condition and finite_app).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (nonempty and domains of nonempty open section rings).
- `def-sbc-normal-dominant-galois`: `WeilConjectures.AlgebraicGeometry.NormalScheme`,
  `AlgebraicGeometry.IsNormalScheme`; dominance uses the same node's recorded
  `AlgebraicGeometry.IsDominant` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. Its affine-cover equivalence was read.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`; chart identifications and canonical embeddings
  use `IsAffineOpen`, `IsAffineOpen.isoSpec`, and `IsAffineOpen.fromSpec` in
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` with `IsDomain`, the recorded normal-domain conjunction.
- Proof-only dependencies are imported from `Mathlib.AlgebraicGeometry.AffineScheme`
  (the recorded `Scheme.localRingHom_comp_stalkIso`, `Spec.algebraMap_stalkIso_inv`,
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.isOpenImmersion_fromSpec`,
  `IsAffineOpen.fromSpec_primeIdealOf`, `IsAffineOpen.isLocalization_stalk`), together
  with its Scheme/OpenImmersion imports (`Scheme.Hom.germ_stalkMap` and the stalk-map
  isomorphism instance), and `Mathlib.RingTheory.LocalProperties.IntegrallyClosed`
  (`IsIntegrallyClosed.of_localization_maximal`). No dependency lacks its recorded interface.

Source read: local Stacks algebra.tex, lemma-normality-is-local (030B, (3) to (1));
morphisms.tex definition-integral (01WH, finite clause); schemes.tex lemma-spec-sheaves
(01HV, (6)); properties.tex definition-noetherian (01OV) and its affine-cover equivalence.
The theorem docstring contains all four steps of the accepted node proof.

Edge cases checked mathematically:

- An integral scheme is nonempty; empty V or B is correctly excluded by the hypotheses.
- A cover indexed by the empty type cannot cover nonempty B; the first implication is
  vacuous in this case, while the final existence conjunct still supplies a valid cover.
- Empty affine charts are deliberately excluded: their section ring would be the zero
  ring and not a domain. No empty chart is introduced by the existence assertion.
- Dominance makes each nonempty open meet the image; without it a chart could have empty
  inverse image and the section map could fail injectivity (a closed point in an affine line).
- The identity on a normal locally Noetherian integral scheme gives identity section maps.
  Fields and the finite dominant map Spec Z[i] to Spec Z satisfy all clauses.
- No quasi-compactness or finite cardinality of the covering is imposed, so arbitrary
  locally Noetherian integral bases, including non-quasi-compact ones, remain covered.
- The chart index universe v is arbitrary; the existential index uses the point universe u.
  No field characteristic, separability, flatness, or normality of V is imposed.

Searches performed through the required msearch.py wrapper (logs in searches.jsonl):

- LeanFinder: "For a finite dominant morphism of integral schemes with normal locally
  noetherian target, affine inverse images have domain coordinate rings finite over normal
  domain coordinate rings with an injective ring map". Eight hits: IsFinite.finite_app,
  IsIntegralHom.hasAffineProperty, and normalization morphism results. These only give
  individual clauses or concern normalization, not this whole statement.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsDominant`. Zero hits.
- Mathlib grep in AlgebraicGeometry: `finite_app|app_injective|IsNormalScheme`.
  Fourteen hits, including finite_app and Scheme.Hom.app_injective; neither combines
  normal affine rings, nonempty affine inverse images, domains, and cover existence.
- LeanSearch: "Affine chart rings of finite dominant maps of integral schemes to a normal
  locally noetherian scheme are finite injective extensions of normal domains".
  Eight hits, all finite/integral morphism interfaces and local finite type facts;
  none says the entire node.
- Direct rg in lean/WeilConjectures and lean/Sheaf for
  `finite.*[dD]ominant|[dD]ominant.*finite|finiteDominantNormal|` followed by the item id
  finds nearby finite-dominant results but no affine-chart preparation theorem.
  The existing FiniteDominantNormalUniversallyOpen module is the parent theorem,
  whose proof discusses this preparation; it does not separately state the item.
- Direct rg for the item id and `finite_dominant_normal_affine_chart_rings` in both
  library trees and dag/lean_names_upstream.json returns no existing declaration.
- Read RingHom.Finite in Mathlib.RingTheory.Finiteness.Defs to confirm it means finite
  module via the given map, not finite type as an algebra.

Validation: the initial module compiled cleanly via scompile.py, with no errors or
unexpected warnings. The final import-visibility adjustment and delivery checks are
validated by the prescribed dry run. No STATEMENT-DISPUTED or node fault remains.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
