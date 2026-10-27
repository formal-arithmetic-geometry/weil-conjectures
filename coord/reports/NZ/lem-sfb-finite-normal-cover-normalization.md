## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteNormalCoverNormalization` states
`AlgebraicGeometry.finite_normal_cover_normalization`, with one whole-proof `sorry`.
It introduces no definitions, helper theorems, or new nodes. The original node's
statement and dependencies are unchanged. Source read: Stacks Morphisms Tag 035I,
`lemma-characterize-normalization` (including its proof), and Properties Tag 0358,
`lemma-normal-integral-sections` (including its proof). These give the normalization
universal property and the normal-domain argument used by the node's seven proof steps.
The declaration docstring carries all seven steps and their dependency names.

Hypotheses, in order:

- Integral schemes X and Z: `{X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]`.
  Integral schemes are nonempty, so the empty source and target are excluded exactly
  as in the node. One arbitrary universe u includes every pair of schemes, after
  taking a common ambient universe.
- Z locally Noetherian: `[IsLocallyNoetherian Z]`. There is no Noetherian hypothesis
  on X, and no global quasi-compactness condition on either scheme.
- Normality of Z, with domain local rings: `hZ : ∀ z : Z,
  IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)`.
- The finite surjective morphism: `(f : Z ⟶ X) [IsFinite f] [Surjective f]`.
- F and L are the actual generic stalks: `X.functionField` and `Z.functionField`.
  `[Algebra X.functionField Z.functionField]` supplies the field extension;
  `hL : X.fromSpecOfAlgebraFunctionField Z.functionField =
  Z.fromSpecFunctionField ≫ f` constrains its structural embedding to the induced
  generic stalk map. This is the datum described by “the induced field extension,”
  not an additional geometric restriction and not an arbitrary embedding. The
  existing canonical `dominantFunctionFieldAlgebra f` gives this algebra (surjectivity
  supplies dominance); the Spec–stalk adjunction identifies its generic-point equation
  with the canonical pullback. No independent choice of a generic point is made.
- The extension is finite: `[FiniteDimensional X.functionField Z.functionField]`.
  There is no separability hypothesis, nor étaleness of f or normality of X.

Conclusions, clause by clause:

- The canonical X-isomorphism is `∃ e : Z ≅ X.normalizationIn Z.functionField`, with
  `e.hom ≫ X.fromNormalizationIn Z.functionField = f`.
- Its restriction to the generic point is the identity on L:
  `Z.fromSpecFunctionField ≫ e.hom =
  (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization`.
  The right-hand side is the actual canonical map from Spec L into the normalization,
  so no arbitrary identification of its function field with L is substituted.
- Unique determination is stated for every morphism `v : Z ⟶ X.normalizationIn
  Z.functionField` over X with that same generic equation: `v = e.hom`.
  This includes, and is stronger in presentation than merely quantifying over
  isomorphisms, precisely the node's final proof step about an arbitrary u.
- Every nonempty affine open is quantified as `(V : X.Opens), IsAffineOpen V →
  ∀ (_ : Nonempty V), ...`. Its coordinate ring is A = `Γ(X, V)` and the inverse
  image's coordinate ring is B = `Γ(Z, f ⁻¹ᵁ V)`. `Nonempty (f ⁻¹ᵁ V)` and
  `IsAffineOpen (f ⁻¹ᵁ V)` explicitly assert the affine nonempty inverse image.
  This uses the canonical coordinate rings instead of arbitrary presentations
  Spec A and Spec B; the affine equivalence recovers any such presentation.
- `Function.Injective (f.app V)` is the injectivity of A → B.
- `Function.Injective (Z.germToFunctionField (f ⁻¹ᵁ V))` and
  `IsFractionRing Γ(Z, f ⁻¹ᵁ V) Z.functionField` state the germ embedding B ⊂ L
  and L = Frac B, using Mathlib's germ-induced B-algebra structure.
- The equality of B with the integral closure is literally the equality in L:
  `Set.range (Z.germToFunctionField (f ⁻¹ᵁ V)) =
  (@integralClosure Γ(X, V) Z.functionField _ _
  ((Z.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (f.app V).hom).toAlgebra : Set _)`.
  Thus the A-algebra structure in this closure is the given structural map A → B
  followed by the actual germ B → L. The subalgebra carrier equality is exactly
  equality of the two subrings inside L, not an abstract ring isomorphism.
- The final equality of maps on sections states that pullback by e, followed by the
  germ in L, equals the canonical generic evaluation of normalization sections.
  `e.hom.appLE` supplies its map from sections on the normalization inverse image
  of V to B. On the other side, `toNormalization.appLE ... ⊤ hgen` and
  `(Scheme.ΓSpecIso (.of Z.functionField)).hom` evaluate those sections in L.
  Thus e realizes the affine identification B = C as the identity in L on every V.
  Since these maps are restrictions of one global morphism, their restriction squares
  commute on all smaller opens, in particular principal opens and arbitrary overlaps.
  This expresses the node's agreement/gluing clause without assuming intersections
  of affine opens are affine. `hpre` and `hgen` are existential containment witnesses
  needed to type these canonical section maps; they impose no hypotheses on f or X.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (nonemptiness
  and domain coordinate rings), exposed through the function-field imports.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded integral-scheme
  clause reuses Mathlib `Scheme.functionField`, not `functionFieldOfComponents` for
  a general reducible scheme. Both the recorded module and its docstring were read.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.germToFunctionField`, its
  injectivity theorem, and `functionField_isFractionRing_of_isAffineOpen`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`; the field finiteness predicate is
  `FiniteDimensional`. These are exposed by the statement dependency modules.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, and `Scheme.Hom.appLE`;
  the chosen spectra are represented by the canonical rings of sections.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, and
  `Scheme.fromSpecOfAlgebraFunctionField`. Its relative-normalization construction
  supplies the canonical `toNormalization : Spec L ⟶ X.normalizationIn L`.
- `Sheaf.TraceFormula.LocalDimensionFormula`:
  `Scheme.Hom.dominantFunctionFieldAlgebra` (proof dependency, actual generic map).
- The remaining proof dependencies with recorded Mathlib matches are available via
  the normalizations/finite imports, `Mathlib.RingTheory.LocalProperties.IntegrallyClosed`,
  `Mathlib.RingTheory.Localization.Integral`, `Mathlib.AlgebraicGeometry.Modules.Tilde`,
  and `Mathlib.AlgebraicGeometry.Gluing`. They provide respectively the affine stalk
  localization and ring-equivalence transfers, maximal-localization normality,
  finite-algebra integrality, integral-closure localization, principal-open sections,
  and gluing. No proof-only import is public.

Edge cases checked mathematically: a field point with a finite extension, the identity
normal cover, the cusp k[t²,t³] ⊂ k[t] (a nonnormal target), the ramified map t = s²,
and a purely inseparable extension all have the asserted affine equality and the
specified generic map. The theorem does not require X separated: overlap compatibility
uses global section maps, not affineness of intersections. The affine V is required
nonempty; restrictions to D(0) are automatically the unique maps on empty schemes.
No algebraic closure, characteristic restriction, nontrivial extension degree, or
positive dimension has been imposed. The zero ring cannot be a nonempty affine
coordinate ring of an integral scheme.

Searches performed, 2026-10-24:

- msearch.py LeanFinder: “A finite surjective morphism of integral schemes from a
  normal source identifies the source with normalization in its function field.”
  Eight hits: relative normalization constructions and universal properties in
  Mathlib.AlgebraicGeometry.Normalization; no match for the full statement.
- msearch.py Loogle: `"AlgebraicGeometry", "normalization", "IsIntegral"`.
  Five relative-normalization instances, including
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`; these concern normalization
  of f in its entire source and omit the affine equality in k(Z), prescribed generic
  identity and morphism-level uniqueness.
- msearch.py grep: `normalizationIn|instIsIsoToNormalization|IsIntegrallyClosed` in
  AlgebraicGeometry/Normalization.lean: zero hits reported by that search service.
  Local source reading independently confirms relative normalization is available.
- msearch.py LeanSearch: “Affine rings of a finite dominant normal cover are integral
  closures in the function field.” Eight hits: `integralClosure`, function-field rings
  of integers and integral-closure instances; no geometric statement match.
- rg in lean/WeilConjectures and lean/Sheaf:
  `normalizationIn|finite_normal.*normalization|normal.*cover.*normalization`.
  Read `WeilConjectures.AlgebraicGeometry.NormalizationCoverIn` and the recorded
  normalization module in full relevant sections. `exists_iso_normalizationIn`
  identifies f.normalization, rather than Z, with X^L and only records the equation
  over X; it does not state this node's affine equalities or uniqueness. The finite
  étale component theorem is a special situation with additional hypotheses.
- grep of the item id in lean/WeilConjectures returned no matches. The upstream names
  index has no match for the new theorem's name. Local rg found no declaration of
  `finite_normal_cover_normalization` in either source root before writing it.

No statement correction, dependency-interface repair, or disputed statement is needed.
Validation: single-file compilation through the prescribed scompile.py, followed by
both deliver2.py dry run and delivery. Only the expected whole-proof sorry is present.

## Second reading by NZ

This is a self-audit, not an independent worker review: the dispatcher explicitly
forbids starting other agents and assigns independent review to the maintainer.
Re-read the unchanged node alongside the complete signature. The affine clauses,
unique global X-isomorphism and identity on L are all present. The generic compatibility
condition on the input algebra prevents an unrelated field embedding. The explicit
fraction-ring and germ-injectivity clauses were added on this reading so the phrase
“B ⊂ L = Frac B” is visible in the statement itself. The last section-map equation
ensures that the global isomorphism is the one induced by the affine identities;
functorial restriction gives principal and overlap compatibility. The use of actual
local rings, actual function fields, and the recorded normalization definitions
avoids replacement objects. No original-node field except lean was changed.
