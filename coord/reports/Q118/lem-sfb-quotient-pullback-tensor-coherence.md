## Worker report

Item: lem-sfb-quotient-pullback-tensor-coherence. The module states the coefficient-square
commutation, identifies the given normalized lambda with the ringed square comparison
through its ordinary balancing and derived computation-counit characterization, and states
the exact displayed tensor equation in the internal quotient-module derived category.
The sole theorem has proof `sorry`. The helper `quotientTensorPull` has real data: it is
exactly `CondensedRing.leftDerivedUpperStarTensor`, with `QuotientChange.L` unfolded once
in its definition to share the structural arguments. No separate tensor map is chosen.

Hypotheses and clauses, matched against the node:

- Prime ell and finite extension: `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
- The valuation ring and its chosen uniformizer are the existing
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`, used
  by `IntegralQuotient.integral`, `finite`, and `reduction`. All positive exponents are
  represented once, as `n + 1` with `n : ℕ`. In particular `n = 0` means exponent one,
  not a zero ring artificially inserted into the statement.
- R_T is `condensedRingObj (integral l E) T`, the pulled-back continuous integral
  condensed ring. Its identification with the positive finite-quotient limit is exactly
  the imported `sfb_integral_coefficient_limit`. S_T is
  `condensedRingObj (finite l E n) T`, and the vertical map is exactly
  `coefficientMap (reduction l E n) T`, not an arbitrary homomorphism.
- The ordinary unbounded internal derived categories are
  `DerivedCategory (QuotientChange.Modules ... T)`. `D` is the total left derived
  extension of the actual quotient, and `L` is the named existing total derived module
  pullback. Tensors and tensor morphisms use the existing uncompleted relative derived
  monoidal structure. Pushforward/adjunction data are imported through the recorded
  direct-image comparison; this lemma does not impose a pushforward hypothesis.
- The two `HasDerivedCategory` families specify the section categories' localization
  universes exactly as in `quotient_section_tensor_normalization`. They are structural
  localization data; no equality between the small site's object universe u+1 and
  morphism universe u is imposed. The internal derived categories retain their
  framework instances. These are not flatness or finiteness assumptions on inputs.
- The normalized scalar tensor isomorphisms b_T are the family `b` of the existing
  `QuotientSectionTensor.TensorIso` type, with `_hb` requiring exactly that dependency's
  `TensorNormalized` on every flat-term K-flat pair. Their existence and uniqueness
  are furnished by `quotient_section_tensor_normalization`.
- An arbitrary scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  `lam` has type `D_Y ⋙ L_S ≅ L_R ⋙ D_X`. `_hlam` is the exact existing
  `PullNormalized` used in `integral_quotient_direct_image_comparison`; it fixes lambda
  by the ordinary `CondensedRing.pullIso` and localization counits. There is no extra
  monoidality hypothesis on lambda.
- The first conjunct is precisely
  `f^*(q_Y) ≫ alpha_S = alpha_R ≫ q_X`, with `condensedPullbackHom` as alpha.
  Thus the actual two structural ring maps commute under the coefficient compositor.
- The second conjunct gives section scalar data `cX`, `cY`, with
  `ScalarSectionNormalized` fixing their actual quotient section models and universal
  counits. `PullSectionCondition ... lam barLam` identifies THIS lambda under the fixed
  internal/section and geometric comparisons. `SectionPullNormalized ... barLam`
  specifies the ringed-square composition comparison by its ordinary square and
  derived composite-counit equation. Unfolding it: its ordinary `e` is fixed through
  `CondensedRing.pullIso` and the ordinary scalar/geometric comparisons, and its derived
  equation evaluates that ordinary square on cochain models. This is the normalized
  characterization of c_B h c_A^-1 from Stacks 0D6D; an independently arbitrary
  isomorphism between the same endpoints would not satisfy this clause. No extra
  square-comparison construction or untracked existence axiom is introduced.
- The final conjunct quantifies over every `U V : DerivedCategory (Modules R Y)`.
  In Lean's left-to-right composition order the left side is
  `lam_(U tensor V) ≫ D_X(t_R) ≫ b_X`, and the right side is
  `L_S(b_Y) ≫ t_S ≫ (lam_U tensor lam_V)`. These are exactly the node's two routes.
  The common source is `L_S D_Y(U tensor V)` and common target is
  `D_X L_R U tensor D_X L_R V` in D_S(X). All component maps come from natural
  transformations; the equation therefore expresses the stated natural compatibility.
- Neither variable is exchanged: the final map is `lam.hom.app U ⊗ₘ lam.hom.app V`,
  in that order. No symmetry or homogeneous interchange is inserted. There are no
  boundedness, properness, completeness, constructibility or quotient-flatness binders.

Dependency declarations read and used (their recorded modules, publicly available through
QuotientSectionTensorNormalization unless separately imported):

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`; its imported CoefficientExtension gives the
  actual integers, uniformizer, ideal and finite quotient.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  `coefficientRing`, `condensedRingObj`, `condensedPullbackHom`, `coefficientPullbackIso`.
- Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit:
  `AlgebraicGeometry.ProEtale.sfb_integral_coefficient_limit`.
- Sheaf.Paper.CondensedModuleDerivedPushpull:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward` and the
  publicly imported derived adjunction.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom:
  `CondensedRing.derivedHom`, importing the exact relative `derivedTensor` used here.
- Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings:
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`, publicly retaining
  `SheafOfModules.DerivedChangeOfRingsCochainModel` used by the section scalar models.
- Sheaf.Paper.QuotientSectionTensorNormalization:
  `TensorIso`, `TensorNormalized`, `ScalarSectionData`, `ScalarSectionNormalized`,
  `PullSectionCondition`, `SectionPullNormalized`, `quotient_section_tensor_normalization`.
- Sheaf.Paper.IntegralQuotientDirectImageComparison:
  `IntegralQuotient.integral_quotient_direct_image_comparison`; its actual
  `QuotientChange.D`, `L`, `Modules`, `PullNormalized` are used unchanged.
- Sheaf.Paper.ModuleObjectProjectionMap:
  `CondensedRing.moduleObjectProjectionMap`; its public
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal exports
  `leftDerivedUpperStarTensor`, the actual t_R and t_S used here.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`, `MorphismProperty.kFlat`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `SheafOfModules.IsFlatOnSite`.
  These are the unchanged flat and K-flat predicates in the section normalization.
- Sheaf.Paper.IntegralQuotientCoefficients: `integral`, `finite`, `reduction`.
  Its existing node def-sfb-integral-quotient-coefficients is added to stmt_deps because
  these canonical maps occur explicitly in this statement (already a proof dependency).

The proof-only imports correspond to every already stated proof dependency, including
flat-term K-flat resolution/total tensor/pullback preservation, ringed tensor comparison,
ringed composition and two-isomorphism normalization, local section calculus, and
resolving-class two-variable descent. The theorem docstring carries the six proof steps
and the explicit generator calculation.

Edge cases checked before writing: f = identity gives the same normalized balancing
on both routes; zero inputs and empty schemes cause no exclusion; n = 0 is the nonflat
residue-field quotient (for E = Q_l, Z_l to F_l), not a case requiring ordinary extension
exactness; odd degrees preserve (i,j) and hence introduce no Koszul interchange sign;
both complexes may be unbounded in both directions and their tensors use direct-sum
totals. The target is quotient-linear, not merely an equality after forgetting scalars.
No statement fault or STATEMENT-DISPUTED claim was found.

Searches actually run:

- msearch.py leanfinder: "The normalized derived scalar extension pullback comparison
  for a quotient of sheaves of rings commutes with tensor products without flatness".
  Eight hits concerned ordinary SheafOfModules pullback, free generators and associativity;
  none states the specified unbounded quotient tensor equation.
- msearch.py loogle: `"NatTrans.IsMonoidal.tensor"`. Two hits were tensor and tensor_assoc;
  these assume an already monoidal natural transformation and do not establish the
  specified comparison's compatibility.
- msearch.py grep: `pullbackComp|IsMonoidal.tensor` under
  Algebra/Category/ModuleCat/Sheaf. Five hits were ordinary pullbackComp and its coherence.
- msearch.py leansearch: "Derived scalar extension and pullback comparison commutes with
  the normalized derived tensor comparison". Eight hits included ordinary tensor scalar
  extension, module adjunction and unrelated base-change facts; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for quotient/tensor, PullNormalized,
  SectionPullNormalized, and the prospective theorem name. Found the required existing
  interfaces, upstream coefficient-square naturality, and the downstream
  IntegralQuotientProjectionComparison proof discussion, but no theorem asserting this
  item's full conclusion. grep of the node id in lean/WeilConjectures found no match.
  The downstream file's tensor wrapper cannot be imported here: that projection
  comparison cites this node in its proof. The helper here only exposes the type of
  the same upstream map and does not define a new mathematical tensorator.
- Read blueprint main-20261015 integral proof paragraph (3) and Stacks
  sites-cohomology.tex, lemma-derived-pullback-composition (0D6D),
  lemma-pullback-tensor-product (07A4), including the K-flat representative proofs.

Validation: scompile.py passed cleanly on the server: sandbox 37.5 s and the actual
library module 32.1 s, with no warnings or errors. The first version timed out at 60 seconds;
its concrete comparison occurrences were replaced by a generic typed wrapper around
that exact existing comparison. The time limit was not changed.

## Second reading by Q118

Self-check with the node and Lean file open; no second agent was started, as the dispatch
explicitly prohibits it. The maintainer's independent delivery review remains required.
Checked every hypothesis and conjunct against the correspondence above, especially
lambda's orientation, the quotient coefficient action, n+1 indexing, and the ordered
homogeneous variables. The section identification uses the existing normalized
composition-counit characterization, not just a bare Nonempty natural isomorphism.
No natural-language statement correction and no dependency interface repair is made.
