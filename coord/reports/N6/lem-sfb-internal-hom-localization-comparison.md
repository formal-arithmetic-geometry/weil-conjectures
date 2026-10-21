## Worker report

Module: `Sheaf.Algebra.Homology.InternalHomLocalizationComparison`.
Main declaration: `CategoryTheory.internalHom_localization_comparison`.
This is stage 2: the single theorem has proof `sorry`. The five auxiliary
definitions contain actual constructions, with no postponed data or proof fields.
The node is unchanged except for its `lean` field. There are no new DAG nodes,
no dependency repairs, and no statement correction or disputed assertion.

Clause-by-clause reading of the node:

- A site small in the module universe: `{C : Type c} [Category.{v} C]`,
  `J : GrothendieckTopology C`; coefficients and module carriers live in
  `max c v r`. Thus the site is small relative to that universe, with no equality
  imposed on `c` and `v`. The sheafification and sheaf-composition instances
  express the standard sheaf infrastructure in this universe.
- A sheaf of commutative rings: `R : Sheaf J CommRingCat.{max c v r}`.
- Exact filtered colimits: the existing theorem
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  provides `IsGrothendieckAbelian.{max c v r} (scalarModules J R)` under the
  displayed site/sheafification hypotheses. Its `ab5OfSize` field is precisely
  exactness of filtered colimits in this module universe. This assumption of
  the prose is therefore already guaranteed in the small-site encoding; it is
  not replaced by an assumption about just one diagram, or silently assumed
  for an unrelated category. No redundant external exactness witness is needed.
- Ordinary unbounded derived categories: `DerivedCategory (scalarModules J R)`
  and the same category over `ringedLocalizationRingOfUniverses R s`.
  `scalarModules` transparently uses `ringedSiteModules`, hence Mathlib's
  `SheafOfModules`; it introduces no alternate sheaf category. The universal
  `HasDerivedCategory.{w}` instances choose localization sizes, as in the
  recorded scalar-Hom interface.
- Relative derived tensor and ambient internal Hom: the existing `M.closed`,
  its K-flat-normalized `M.model`, and
  `derivedInternalHomOfUniverses.{c, v, r, w} J R` are used throughout.
  `M.scalar a` is the existing universal derived change-of-rings pair, with
  prescribed ordinary sheafified tensor objects/maps and K-flat counit.
- Global section and localization: `s : (R.obj ⋙ forget CommRingCat).sections`,
  `S = ringedLocalizationRingOfUniverses R s`, and the actual coefficient map
  `ringedLocalizationRingUnitOfUniverses R s`. These are the recorded
  sheafification of sectionwise `Localization.Away` and its sheafified unit.
  No arbitrary ring, scalar map, or localization is supplied as a hypothesis.
  The telescope interpretation is the existing section-localization notion
  and scalar-localization complex-colimit theorem used in the proof plan.
- The object `K : DerivedCategory (scalarModules J R)` is arbitrary.
  `localizationHomComplex` is `coefficientHomResolution J R` followed by
  `(homComplexFunctor (R := R)).obj (op (DerivedCategory.Q.objPreimage K))`.
  The first argument is Q's actual representative of K. The second argument
  uses exactly the fixed functorial K-injective replacement defining the
  recorded derived internal Hom. Its identification is supplied by the
  existing `coefficientHomResolutionIso` and Q's preimage isomorphism.
- Every sequential diagram with one common termwise lower bound:
  `HasLocalizationHomContinuity` quantifies over every
  `D : ℕ ⥤ CochainComplex (scalarModules J R) ℤ`, with
  `∃ a : ℤ, ∀ n : ℕ, (D.obj n).IsStrictlyGE a`.
  The same integer bounds every term, not merely its cohomology.
- The evaluation-induced continuity map is
  `DerivedCategory.Q.map (colimit.post D (localizationHomComplex J R K))`,
  with universe parameters explicitly given in the source. Mathlib's
  `colimit.post` is exactly `colimit.desc` of the Hom images of the colimit
  coprojections. Hence its legs are the functorial, evaluation-induced maps.
  All colimits occur in complexes, before Q, so these are termwise sheaf
  colimits, not assumed colimits of the triangulated derived category.
  `IsIso` is imposed after Q, so the hypothesis asks for a derived
  isomorphism, not an isomorphism of complexes.
- `L` with cohomology vanishing in sufficiently negative degrees is
  `hL : ∃ n : ℤ, L.IsGE n`. Mathlib's `isGE_iff` identifies this with the
  cohomology-vanishing assertion. A strictly bounded-below representative of
  L is used only in the documented proof, not required of the given object.
- The canonical map over S is `localizationHomComparison`: apply the inverse
  strong scalar-tensor comparison to `F(H_R(K,L)) tensor_S F(K)`, follow by
  `F(evaluation)`, and apply `(M.closed S).transpose`. This is precisely the
  evaluation-transpose map of the node, with its indicated source and target.
  The first conjunct of the theorem asserts `IsIso` of this actual arrow.
- Evaluation-normalized scalar adjunction: `μ` and `α` have the existing
  types `ScalarHomTensorComparison M a` and `ScalarInternalHomAdjunction M μ`.
  These are presentations of the canonical operations; their existence is
  already the dependency `scalarInternalHomAdjunction_exists`. The theorem
  applies to every such normalized presentation. It does not postulate a
  new closed structure or a comparison with an arbitrary normalization.
- Restriction of the comparison is
  `localizationHomRestrictedComparison = U.map χ ≫ (α.iso a).hom.app (op K, F L)`.
  The second conjunct states that it is invertible. The third states exactly
  `eta_(H_R(K,L)) ≫ beta = H_R(K, eta_L)`. The fourth states that any arrow
  with these endpoints and this scalar-unit equation equals beta. This
  identifies beta with the sequential-continuity isomorphism: that
  isomorphism has this zeroth-leg equation, and localization's unit
  bijection makes the equation a unique characterization. In particular
  this asserts equality of the actual derived maps, not merely agreement
  on a collection of telescope legs. It does not replace the comparison by
  an arbitrary isomorphism or by a `Nonempty` choice.
- Naturality in both inputs: the final quantified square takes
  `f : K' ⟶ K` and `g : L ⟶ L'`, retaining continuity of K' and boundedness
  below of L'. The left arrow is `F.map (H_R.map (f.op,g))`; the right arrow
  is `H_S.map ((F.map f).op, F.map g)`. The equation is the naturality
  square of the actual comparison, contravariant in K and covariant in L.
  Naturality of its restriction then also follows from the dependency's
  natural `α.iso` and the functor U.
- There is no constructibility, completeness, perfectness, flatness of K,
  finite Tor amplitude, or field/characteristic assumption in any binder.

Dependency declarations read and used (including their full signatures and
source docstrings):

- `def-weil-size-convention`: metatheoretic convention, no object declaration;
  rendered by the explicit `c v r w` levels above.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`,
  retained through the scalar models' actual total tensor formula.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, used by `M.model` and
  the existing scalar model/comparison normalization.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`, with its actual
  K-injective-Hom localization and comparison declarations.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`,
  `CategoryTheory.ringedLocalizationRingOfUniverses` and
  `CategoryTheory.ringedLocalizationRingUnitOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteLocalization`,
  `CategoryTheory.ringedSiteSectionLocalization`, the slice telescope;
  its module is imported and the global scalar telescope is used in the
  proof plan through `scalarLocalization_complexColimit`.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `colimit.desc`, `colimit.post`, and `colimit.ι_post`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`;
  `M.scalar` retains the compatible universal derived scalar pair.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`, via `scalarRestriction` and
  `scalarDerivedRestriction` from the existing data module.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`,
  `CategoryTheory.scalarInternalHomAdjunction_exists`, together with its
  public `ScalarInternalHomData` declarations `ScalarHomModels`,
  `ScalarHomTensorComparison`, `ScalarInternalHomAdjunction`.
- The same dependency publicly supplies
  `Sheaf.Paper.CoefficientHomRepresentativeEvaluation` and its existing
  `WeilConjectures.coefficientHomResolution` and
  `WeilConjectures.coefficientHomResolutionIso`. These are reused verbatim.
- Proof imports: `Sheaf.CategoryTheory.ScalarLocalizationSheafExact`,
  `CategoryTheory.scalarLocalization_sheaf_exact`;
  `Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore`,
  `CategoryTheory.scalarLocalization_complexColimit`;
  ordinary/derived coefficient adjunction modules (publicly reached by the
  scalar-Hom interface); Mathlib's `CochainComplex.IsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`, and
  `CochainComplex.mappingCone.homotopyToZeroOfId` in their defining modules.

Edge cases checked before writing: K=0 and L=0 give zero internal Hom and
invertible zero-object comparisons. If s is a unit the coefficient map is an
isomorphism and the comparison is the identity under the canonical transports.
If s=0, or s is nilpotent, the localized ring is the zero sheaf, so both objects
over S vanish; no nonzero-section premise excludes this case. On the empty
site the same constructions and statements remain meaningful. For a one-object
site, R=Z, s=p, K=R and bounded-below L this gives ordinary p-localization of L.
No assumption bounds the Hom complex below; the continuity hypothesis bounds
only the input sequence. No termwise lower bound is imposed on the given L.
The coefficient universe can strictly exceed either site universe. ℕ is the
ordinary nonempty sequential index with its zero stage.

Searches, 2026-10-21 (all through the prescribed tools):

1. `msearch.py ... leanfinder "Derived internal Hom commutes with scalar
   localization if it preserves bounded below sequential colimits"`: eight
   results, all generic derived linearity/localization/Ext infrastructure;
   no statement matching the conditional scalar comparison.
2. `msearch.py ... loogle "colimitComparison"` and `... loogle "colimit.post"`:
   endpoint returned unknown identifiers. Direct reading of Mathlib's
   `Limits/HasLimits.lean` locates the actual `colimit.post` at line 843,
   which is reused in the module.
3. `msearch.py ... grep
   "(internalHom|derivedHom|rhom).*(localiz|invert)|(localiz|invert).*(internalHom|derivedHom|rhom)"`:
   six hits, monoidal category localization, OreLocalization and PicardGroup;
   none states the comparison here.
4. `rg -n` of internal-Hom/localization and sequential-continuity expressions
   in `lean/Sheaf` and `lean/WeilConjectures`, and the item id in
   `lean/WeilConjectures`: no existing declaration of this lemma.
   `EtaleInternalHomLocalization` concerns an open/closed localization
   triangle, and `IntegralConstructibleSequentialHom` concerns global Hom
   factorization; neither says this internal-Hom coefficient comparison.
   `ScalarInternalHomData` is exactly the usable generic scalar interface.

Read the local Bhatt--Scholze PDF, printed pp. 61--62, with `pdftotext`.
It states global Hom continuity and the constructible coefficient equivalence;
the node explicitly describes its stronger internal-sheaf continuity premise
as an agent conditional formulation. This delivery retains that premise and
that distinction; it makes no claim that global Hom continuity implies it.

## Second reading by N6

This is a fresh self-audit, not an independent second worker: the dispatcher
explicitly forbids starting another agent, and the maintainer performs the
independent delivery review. I reopened the source module and the node's full
statement after compilation. The boundedness hypothesis applies to L's
cohomology, whereas the continuity predicate restricts every input complex
termwise with a shared bound. The output concerns an S-linear morphism, and
its restricted counterpart uses the adjunction's specified isomorphism in
the correct direction. Checking the tensor order shows that evaluation is
on Hom(K,L) tensor K, so the inverse scalar-tensor comparison is the required
arrow before transposition. I also checked the naturality square's endpoints:
f runs from K' to K, so its opposite and F(f)'s opposite run toward the primed
Hom; g runs from L to L'. The scalar-unit equation has source H_R(K,L), and
its universal characterization applies because the target is canonically
isomorphic to U of an S-object. These endpoint checks found no statement
mismatch. During elaboration I made all helper universe arguments explicit,
reused Mathlib's `colimit.post` directly, removed an unnecessary alias for the
coefficient map, and corrected proof-only imports to the exact Mathlib
modules. No mathematical object, hypothesis, or node statement was changed.

Validation: the prescribed `scompile.py N6 ... InternalHomLocalizationComparison.lean`
completed both sandbox and library checks without errors or warnings (7.8 and
7.7 seconds respectively). The prescribed `deliver2.py --no-push` then printed OK for commit
`74aee069a43`: the server preflight and compilation both passed. Final delivery
uses the same module and node record, with this validation result added to the report.
