## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor` states
`AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_derived_scalar_compositor`.
Its only theorem has proof `sorry`. All other declarations are transparent aliases,
actual composites of existing canonical maps, structures, or fully written predicates.
No definition chooses data from an existence theorem. No node statement was corrected,
no dependency module was needed, and there are no disputed statements.

Hypotheses and conventions, clause by clause:

- `X : Scheme.{t}`, `I : Type w`, `[Finite I]`, `Y : I → Scheme.{t}` and
  `j : ∀ i, Y i ⟶ X` are exactly the scheme, arbitrary finite index set, components
  and inclusions. The two immersion instance families are the open and closed
  immersion hypotheses. `hdisjoint` uses disjoint ranges pairwise; `hcover` says
  every point is in one range. No component or index is assumed inhabited.
- `topology X` and `topology (Y i)` are the recorded small pro-etale sites, with
  object universe `t+1` and morphism universe `t`. Coefficients and module sections
  occupy `max u (t+1)`; localization uses `max (u+1) (t+2)`. This is the usual
  ambient universe containing the site and arbitrary coefficients, without an
  equality between the two site universes or between `t` and `u`. `w` is independent.
- `Mods` is the recorded `SuccessiveDerivedQuotient.Modules`, hence the existing
  ringed-site module category, not a private alternative. `rings` is exactly
  `clopenTensorRings`; `res` is exactly `ClopenLocalization.restriction`, forgetting
  commutativity on the coefficient sheaf only. Their underlying section restriction
  is the gluing node's `clopenModuleRestriction`. The universal ring binders in
  `Presentations`, `Comparison` and its laws quantify over every `R`, `S`, `T`.
- `resD` is `res.mapDerivedCategory`, the exact degreewise restriction of the
  localization node. The factors appearing in the equations are the canonical
  `mapDerivedCategoryFactors`, not arbitrarily chosen comparison maps.
- `Presentations` uses the existing `Presentation a`: ordinary objects and maps
  equal `changeOfRings a` and `changeOfRingsHom a`, with its universal left-derived
  pair. `ext` and `extD` only expose those existing fields. The theorem existentially
  provides presentations and their existing `Normalization`, imposing no extra
  hypothesis on any ring map. `computation` is the universal homotopy counit
  transported by `quotientCompQhIso` and `mapHomotopyCategoryFactors` to cochains.
- `Comparison.derived` is the asserted natural isomorphism
  `extD (p a) ⋙ resD j S ≅ resD j R ⋙ extD (q (rings.map a))`. Its morphisms are
  in the derived component-module category, hence linear over the target
  component ring. Natural isomorphism means naturality on all objects and morphisms.
- `Comparison.ordinary`, `Comparison.sections`, `Comparison.chain` and
  `Comparison.degree` specify the actual sheafified pure-tensor comparison and its
  degreewise chain lift. `sections` uses the existing `sectionTensor`, with the
  exact section restriction object `Over.map` on the component site. It sends
  the scalar-first tensor `s tensor p` to the same two restricted sections.
  This is the paper's `p tensor s` after its commutative scalar-order convention.
- `Comparison.representative` is the commuting square between `Q` of the chain
  comparison and the derived comparison through the canonical computations and
  restriction factors. The hypotheses are precisely `IsKFlatIndependentCoefficients P`
  and `∀ n, IsFlatOnSite (P.X n)`. `Comparison.computed` asserts that both
  computation maps are invertible, so this square identifies the derived comparison
  with the localized chain isomorphism, rather than an arbitrary derived isomorphism.
- `Comparison.extended` states K-flatness and flatness of every term of the scalar
  extension over `S`, and of its component restriction over `S_i`. No flatness of
  `a` occurs. The ordinary extension is applied termwise via `mapHomologicalComplex`.
- `Comparison.unique` says every natural transformation satisfying this same model
  equation is the supplied comparison, expressing independence of resolutions.
  Universal left-derived presentations are already determined up to their unique
  counit-compatible isomorphism. The theorem supplies all six law predicates for
  every component in its final conjunction.
- `Coherence.composition` is exactly the displayed derived compositor equation,
  with `n.derived` and `m.derived` the existing normalized global and component
  scalar compositors. `eqToHom` at its end only transports the equality
  `rings.map (a ≫ b) = rings.map a ≫ rings.map b` into the presentation family.
- `Coherence.ordinary_composition` records both ordinary paths; together with
  `composite_sections` it states that both send `t tensor (s tensor p)` to
  `(psi_i(s)*t) tensor p`, exactly the node's pure-tensor formula in scalar-first order.
  `degree` gives the same equality in each chain degree and `representative`
  gives its derived interpretation on a flat-term K-flat model.
- `Units.sections` is the multiplication formula `u tensor p ↦ u • p`.
  `Units.representative` normalizes its derived unit with the same canonical
  computation. `Coherence.identity` and `ordinary_identity` say that applying
  the comparison followed by the component unit equals restriction of the
  global unit. The identity functor-map transport is only `rings.map_id`.
- All coefficient maps are universally quantified. In particular the actual finite
  quotient transitions, completion projections, and their composites are instances
  of the same `a`, `b` and `a ≫ b`, including identity maps. The coefficient
  identifications and their transition compatibility are supplied by the imported
  gluing theorem `clopen_integral_coefficients`; no arbitrary replacement maps or
  discrete constant sheaf replacing the completed sheaf are introduced. Thus the
  final specialization clause needs no extra hypothesis or separate construction.
- Empty components, the empty partition, and zero ring sheaves are included by
  the same unrestricted quantifiers. Their zero-category descriptions are already
  the imported localization theorem's last three clauses. An empty partition forces
  `X` empty by `hcover`; the component laws are then vacuous, as they should be.

Dependency declarations read and used (publicly available through the imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`:
  `clopenModuleRestriction`, `clopenRingRestriction`, `clopenModuleRestriction_additive`,
  `clopen_ringed_module_gluing`, `clopen_integral_coefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization`:
  `ClopenLocalization.restriction`, `restrictionLimits`, `restrictionColimits`,
  `derivedRestriction`, `sheafify`, `locallyBijective`,
  `clopen_unbounded_derived_localization`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection`:
  `clopenTensorRings`, `clopenTensorModules`, `clopenTensorRestriction`,
  `clopen_total_tensor_kflat_detection`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` and its public
  `SuccessiveDerivedQuotientData`: `Modules`, `Presentation`, `Normalization`,
  `sectionTensor`, `successive_derived_quotient_normalization`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains the generic
  site constructions from `DerivedChangeOfRingsCochainModel` and
  `DerivedChangeOfRingsIndependentCoefficients`, including
  `derivedChangeRingIndependentCoefficients`, `changeOfRings`, `changeOfRingsHom`.
  The ordinary-ring presentation is not substituted for the ringed-site one.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `restrictScalars`, used
  by the existing `Normalization`'s extension/restriction adjunction fields.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the existing
  sheafified sectionwise tensor; `FlatOnSite`: `IsFlatOnSite`;
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `Q`, `Qh`, `quotientCompQhIso`;
  the exact-functor API supplies the canonical restriction factors.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: actual constant coefficient
  quotient maps, cone and completion map; publicly retains the completed coefficient
  sheaf and its finite quotient projections.
- Proof imports: `Sheaf.Paper.KFlatRingedToposPullback` (`isKFlat_ringedToposPullback`),
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
  (`site_derived_tensor_descent_independentCoefficients`), and
  `Mathlib.CategoryTheory.Localization.Predicate` (`lift`, `liftNatTrans`,
  `liftNatIso`, `natTrans_ext`). The remaining proof dependencies are public imports
  because their declarations also occur in the statement.

Sources opened: `literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-base-change` (06YY) and `lemma-derived-pullback-composition` (0D6D).
The latter uses one flat-term K-flat representative and preservation of that class,
exactly the model and compositor normalization expressed here. The node's complete
five-step proof is included in the theorem docstring, naming every proof dependency.

Edge cases checked before the final signature: nonflat quotient maps remain allowed;
identity maps use `map_id` rather than assuming strict functorial equality; composition
uses `map_comp` with its correct orientation; chain degrees range over all integers;
zero coefficients and empty sites are not excluded; every coefficient ring and every
finite index universe are quantified independently. There are no hidden auto-implicits.

Searches for an existing statement (the interrupted work's `searches.jsonl` is retained):

- msearch LeanFinder, “Restriction to a clopen component commutes with derived scalar
  extension and its composition isomorphism”: eight hits about ordinary restriction
  of scalars and scheme module restrictions; no derived pro-etale clopen assertion.
- msearch Loogle, `SheafOfModules, changeOfRings`: no hits, unknown identifier
  `changeOfRings` in the index; source search supplied its existing project interface.
- msearch grep, `clopen.*[Ss]calar|derived.*[Ss]calar.*[Cc]ompos`: no Mathlib hits.
  Repeated with `derived.*[Ss]calar.*[Cc]ompos|clopen.*[Ss]calar`: zero hits.
- msearch LeanSearch, “For a finite clopen scheme partition restriction commutes with
  unbounded derived extension of sheaves of scalar rings, preserving the canonical
  composition and unit comparisons”: eight ordinary scheme restriction results,
  no matching statement.
- `rg` of the same scalar/compositor patterns in `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: only the unrelated `SemilinearClopenUnitProjector`
  scalar arrows in `Sheaf`; no statement of this node. `grep -rn` of this item id
  in `lean/WeilConjectures` returned no matches. Existing definitions are reused.

Validation: `scompile.py NF lem-pur-clopen-derived-scalar-compositor <module>`
passed in sandbox form (24.0 seconds) and library form (19.0 seconds), with no errors
or non-sorry warnings. No global build was run. The earlier instance mismatch was
repaired by using Mathlib's abelian instance consistently; the structure elaboration
cost was repaired by separating data and law predicates, without splitting files
or changing the mathematical statement.

## Second reading by NF

Final rereading by the same dispatched worker; no independent agent was started,
as the dispatch brief prohibits it. Independent review is left to the maintainer
specified by this dispatch. This section records the worker's explicit second pass,
not a claim of an independent review.

Opened the final Lean file alongside the node and checked the mapping above.
The derived arrows have exactly the target coefficient linearity, naturality,
localization normalization and uniqueness; `extended` has both flat-term/K-flat
conclusions; the successive compositor equation has the correct source and target;
the local scalar order is reversed only to match the existing scalar-first tensor;
unit multiplication and all coefficient-map cases are retained. Checked in particular
that the component family of presentations has its implicit coefficient binders
preserved, and that equality transports run in the correct direction for composition
and identity. No mismatch with the node remains. Only the worker's draft elaboration
and formatting changed; the DAG statement and all dependency records are unchanged.
