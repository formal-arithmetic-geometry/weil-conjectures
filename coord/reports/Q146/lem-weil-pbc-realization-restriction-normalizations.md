## Worker report

The module `Sheaf.Paper.RealizationRestrictionNormalizations` states
`WeilConjectures.realization_restriction_normalizations` with one `sorry` and supplies six
fully constructed coordinate helpers for the same notion. There are no new nodes, no dependency
record repairs, and no statement correction. Every original statement and proof dependency has a
direct public import. The target node changes only its `lean` field.

Hypothesis and clause audit:

- Prime ell: explicit universe `u`, `{l : ℕ} [Fact l.Prime]`. Finite normed E/Q_ell:
  `{E : Type u} [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The actual ring of integers, positive quotient tower and specified uniformizer are those of
  `pbcIntegralDatum l E` and `pbcUniformizer l E`, as in both realization dependencies.
- Base field: `{k : Type u} [Field k]`, `[Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ l)]`. Thus the characteristic is positive prime and differs from ell.
- Schemes: `{T U : RealizationPullScheme l k}` is the dependency's existing bundle, with
  fields `over`, `finiteType`, `quasiCompact`, `separated`, `noetherian`, `dimension` and
  `invertible`. These express separated finite type over k, explicit Noetherianity, an existential
  finite natural bound on `topologicalKrullDim`, and ell invertible at every stalk. No empty scheme
  is excluded. `{f : T.scheme ⟶ U.scheme} [f.IsOver (Spec (.of k))]` is an arbitrary k-morphism;
  no properness, immersion or Cartesian-square assumption is added.
- Integral and rational categories are the existing `PbcBoundedConstructibleComplete` specialized
  to `pbcIntegralDatum`, and `PbcRationalCategory`/`pbcRationalization`. The former is the full
  integral subcategory used in all quantified N and M. The latter supplies context rather than a
  new condition in the three ambient equations; no Karoubi envelope is introduced.
- A_W is `pbcAdicCompletion W (pbcIntegralDatum l E)`; E_W is
  `rationalCoefficientSheaf l W E`. Normalized scalar data `sT`, `sU` are existing
  `RealizationScalarFunctorData`, so `realizationPullScalarMap l E sW` is precisely
  `sW.integralIso.hom ≫ sW.inclusion`. Its normalizations specify finite quotient reduction,
  continuous functions and pointwise inclusion. No arbitrary scalar map is a hypothesis.
- `a : RealizationCompletedPullArrow T U f sT sU` is the specified completed-pull datum from
  the dependency, including the actual completion unit and actual coefficient comparison. It
  already retains the coefficient-square equality, continuous precomposition normalization,
  inverse-image/localization module-unit and fraction normalizations and representative equations.
  These are the dependency's data, not added axioms about arbitrary functors.
- The coefficient isomorphism is `realizationRestrictionCoefficient a`, constructed by `asIso`
  of `completedCoefficientMap f (pbcIntegralDatum l E)` with `a.coefficient_isIso`. Its hom is
  exactly c_h. The E coefficient is `a.rationalCoefficient`; `a.rational_normalization` identifies
  its adjunct with precomposition. The actual square used by both b and d is
  `a.coefficient_square.symm`, with these two maps and the normalized scalar maps. This is the
  square asserted by `realizationCoefficientSquare`, transported to the specified normalized
  rational presentation; its commutativity is not assumed for an arbitrary coefficient choice.
- Ordinary pull P from the completed-pull dependency is `pbcActualDerivedPull`; its canonical
  adjunction is `pbcActualDerivedAdjunction`. The ring-sheaf theorem presents P by
  `proEtaleRingDerivedPullback`. These two are canonically identified by
  `realizationRestrictionOrdinaryPull a`, the actual `Adjunction.leftAdjointUniq` for their common
  direct image. This is real uniquely determined data, not a choice of a merely existent iso.
- b is `realizationRestrictionPull a`: precisely `proEtaleRingRestrictionDerivedPullback`
  followed by this canonical change of ordinary-pullback coordinates. Its direction is
  `P^E ⋙ r_T ≅ r_U ⋙ P`. d is `realizationRestrictionPush a`, exactly the published
  `proEtaleRingRestrictionDerivedDirectImage`, in direction `Q^E ⋙ r_U ≅ r_T ⋙ Q`.
  Both use the same completed isomorphism, same rational isomorphism and same square.
- Scalar extension, restriction and unit are `pbcDerivedExtend`, `pbcDerivedRestrict` and
  `(pbcDerivedScalarAdjunction ...).unit`. These are the ambient module-derived constructions.
  `sW.tensor_unit` and `sW.unit` specify their unit on modules and unbounded complexes.
- alpha^o is `realizationRestrictionAlpha a N`: F_T.map of the actual
  `pbcActualStrictCompletedPullUnit` followed by `a.alpha.hom.app N`. Thus gamma and alpha^comp
  are retained exactly, rather than replaced by an unnormalized natural isomorphism.
- The existing push theorem supplies a `RealizationLocalizedPushData` p for these scalar data.
  Existential `hA`, `hE` in the conclusion identify its coefficient isomorphisms with those of a.
  These equalities are conclusions, not extra assumptions on the morphism or coefficient maps.
  `realizationRestrictionBeta a p hA hE` is only equality transport of `p.beta`; its construction
  unfolds the existing irreducible scalar-map abbreviation and does not select a new beta.
  `p.beta_normalization` uniquely characterizes beta as the scalar-adjunction transpose in the
  node, so existence here refers to that specified map, not an arbitrary isomorphism.
- First displayed normalization is the first `∀ N` conjunct: j_T at P(N) followed by r_T of
  alpha^o equals P of j_U followed by `b.inv.app (F_U.obj N.obj)`.
- Second displayed normalization is the second `∀ M` conjunct: j_U at Q(M) followed by r_U of
  the transported specified beta equals Q of j_T followed by `d.inv.app (F_T.obj M.obj)`.
- Third displayed normalization is `∀ Z : DerivedCategory (proEtaleRingModules T.scheme
  (rationalCoefficientSheaf l T.scheme E))`: b inverse at Q^E(Z), then r_T of the canonical
  E-counit, equals P of d_Z followed by the canonical ambient A-counit at r_T(Z). There is no
  constructibility, integrality, completeness or bound assumption on Z or r_T(Z).
  All three equations occur in one conjunction, with the same a, p, b and d.
- Lean `≫` composes left to right; every displayed equation above reverses the node's
  right-to-left written composition accordingly. All equalities are of derived morphisms,
  not just homology maps or existence of unspecified object isomorphisms.

Dependency interfaces read and reused:

1. `Sheaf.Paper.IntegralUniformCoefficient`: `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete`
   (the Type (u+1) convenience specialization); the existing lifted Type u specialization
   `PbcBoundedConstructibleComplete` and `pbcIntegralDatum` is the same interface used by the
   recorded realization dependencies. No third integral category is defined.
2. `Sheaf.Paper.PbcRationalCategory`: `AlgebraicGeometry.Scheme.PbcRationalCategory`,
   `pbcRationalization`, `PbcRationalDerivedCategory` (raw scalar localization).
3. `Sheaf.Paper.RealizationScalarFunctor`: `WeilConjectures.RealizationScalarFunctorData`,
   `realization_scalar_functor`, the fields `integralIso`, `inclusion`, `tensor_unit`, `unit`.
4. `Sheaf.Paper.RealizationCompletedPull`: `WeilConjectures.realization_completed_pull` and
   its public `RealizationCompletedPullData` interfaces `RealizationPullScheme`,
   `RealizationCompletedPullArrow`, `realizationPullScalarMap`, `alpha_normalization`,
   `rational_normalization`, `coefficient_square` and `coefficient_isIso`.
5. `Sheaf.Paper.RealizationLocalizedPush`: `WeilConjectures.RealizationLocalizedPushData`,
   `realization_localized_push`, `integralPullback_normalization`, `beta_normalization`.
6. `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the reexported arbitrary-ring-sheaf
   `AlgebraicGeometry.Scheme.proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`,
   `proEtaleRingDerivedAdjunction`, and their ambient module categories.
7. `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
   `AlgebraicGeometry.Scheme.continuousCoefficientImmersionRestriction` (completion and
   sheaf-localization normalization, not a claim of sectionwise localization on all objects).
8. `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
   `AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedPullback`,
   `proEtaleRingRestrictionDerivedDirectImage`, `proEtaleRingSheafChangeAdjunction`.
9. `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`:
   `CategoryTheory.existsUnique_localizationInverseImage`, `localizationComparisonDerived_unit`
   and the specified-coefficient comparison clause.
10. `Sheaf.Paper.RealizationCoefficientSquare`: `WeilConjectures.realizationCoefficientSquare`.

Sources opened: the local Bhatt--Scholze PDF was extracted with pdftotext; Lemma 6.8.2
identifies integral continuous functions with the quotient limit and E with its sheaf localization,
and Remark 6.8.15 gives the ambient scalar/module adjunction context. The latest blueprint's
proper-base-change proof was read; this is the agent-extracted scalar-adjunction calculation
in the node, rather than a replacement proper-base-change route.

Edge cases checked before writing: identity f; empty T or U whenever a morphism exists; E=Q_ell;
zero integral objects and uniformizer-torsion objects; arbitrary unbounded Z with non-integral
restriction. None requires an extra instance or nonemptiness hypothesis. The finite-dimensional
bound includes zero-dimensional schemes; the empty scheme's dimension causes no exclusion.
No claim equates a selected resolution with its pullback. Universe u is arbitrary, with small
pro-etale object universe u+1 and morphism universe u retained by the dependency constructions.

Searches (2026-10-23):

- `msearch.py ... leanfinder "Restriction of continuous scalar derived pullback and pushforward
  comparisons preserves the scalar extension unit and the ambient adjunction counit"`: 8 hits,
  including `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`,
  `...homEquiv_symm_unitToPushforwardObjUnit`, `ModuleCat.ExtendRestrictScalarsAdj.unit` and
  open-immersion module restriction adjunctions. These are ordinary or specialized adjunction
  facts, not these three simultaneous actual continuous-derived comparison equations.
- `msearch.py ... loogle "SheafOfModules.pushforwardPushforwardAdj, Adjunction.homEquiv,
  proEtaleRingSheafChangeAdjunction"`: unknown identifier in the remote Mathlib search, 0 hits.
  Repeated with `SheafOfModules.pushforwardPushforwardAdj`: 3 hits, the ordinary sheaf
  adjunction and its unit/counit section formulas; no matching derived statement.
- `msearch.py ... grep "pushforwardPushforwardAdj|extendRestrictScalarsAdj_unit"
  Algebra/Category/ModuleCat`: 6 hits in ordinary module change-of-rings and sheaf pushforward.
- `rg -n` for `restriction_normalizations|restrictionNormalizations|lem-weil-pbc-realization-restriction-normalizations`
  over `lean/Sheaf`, `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no exact match.
  Broader `realizationRestriction|RestrictionNormalizations` also searched Mathlib, and finds only
  unrelated private realizationRestrictionUnit helpers. `grep -rn` of the item id in
  `lean/WeilConjectures`: no match. Existing upstream ChangeOfScalarsSquare concerns coefficient
  ring objects and their mates, not these module-derived equations. No new independent notion
  required a definition node.

Validation: the final module passed prescribed `scompile.py` sandbox and library compilation
cleanly (3.7 s and 3.3 s). Earlier probes diagnosed the canonical ordinary-pullback coordinate
identification; they are not delivered. All universes and variables are explicit, autoImplicit
is disabled, and the only postponed proof is the named main theorem with its complete four-step
natural-language proof in its docstring. No node fault or STATEMENT-DISPUTED issue found.

## Second reading by Q146

Under the dispatcher instruction to work alone, this is a separate worker self-check; the
maintainer supplies the independent review. Reopened the node and final module side by side.
Checked all field, scheme and morphism assumptions, the coefficient map directions, both units,
and every source and target of all three equations. The first draft used an Over morphism;
typeclass inference on its `.left` obscured the bundled Noetherian instances. The final statement
uses the definitionally same scheme morphism f and an explicit IsOver instance. Checked that
transporting beta unfolds only the existing scalar-map abbreviation, with no new comparison.
The main subtlety is that the completed-pull node's universal ordinary P and the ring-sheaf
node's termwise P are canonically isomorphic rather than definitionally identical; the delivered
helper inserts `Adjunction.leftAdjointUniq` using their common direct image and actual normalized
adjunctions. This also transports the ambient counit correctly. The final quantifier over Z
is unrestricted; no accidental integral-subcategory binder remains. No mathematical mismatch
or statement change was found. The six helpers all belong to the owning node and have real data.
