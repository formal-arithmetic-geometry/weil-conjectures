## Worker report

Item: `lem-sfb-normalized-open-refinement-coherence`. Module:
`Sheaf.Paper.NormalizedOpenRefinementCoherence`; namespace:
`AlgebraicGeometry.ProEtale.CondensedRing`. The statement, statement dependencies,
proof, and proof dependencies of the node are unchanged. No new nodes or dependency
repairs. There is no repair note for this item.

The module gives real data for `normalizedOpenRefinementUnitIso` and
`normalizedOpenRefinement`, and states five theorems, each with the complete proof
postponed by `sorry`. The auxiliary unit theorem is precisely the invertibility of
eta asserted in this node, and the unit isomorphism is `asIso` of that actual unit.
It does not choose a replacement adjunction or an arbitrary isomorphism. These helpers
belong to the same normalized arrow construction and are listed in `lean.declarations`.

Hypothesis and clause correspondence:

- Admissible commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  AddCommGrpCat.{u + 1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`, `(ℓ : ℕ)`,
  `[Fact ℓ.Prime]`, and `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`. The auxiliary
  open-unit lemma needs only the general commutative condensed ring specified by
  the generic open support localization result.
- Schemes and the size convention: `U Z Z' Z'' : Scheme.{u}`. Every complex input
  is in `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U)
  AddCommGrpCat.{u + 1}) (condensedRingObj Λ U))`. Thus the site retains object
  universe `u+1` and morphism universe `u`, as in the published framework, with
  coefficients in `AddCommGrpCat.{u+1}` and the ordinary derived category. There
  is no bounded, constructible, complete, localizing-subcategory or torsion input
  restriction.
- The coefficient object Lambda_T is exactly `condensedRingObj Λ T`, supplied by
  the recorded pullback-from-the-point declaration. All operations are on
  `CategoryTheory.Mod`, never a private module category.
- The three quasi-compact open immersions are the morphisms `j`, `j'`, `j''`
  with `[IsOpenImmersion ...]` and `[QuasiCompact ...]` for each. Single-arrow
  clauses use the first two, identity uses one, and composition uses all three.
  No finite-type, properness, density, Noetherian or base-field hypothesis occurs.
- `hj'=j` and `kj''=j'` are `w : j' ≫ h = j` and `w' : j'' ≫ k = j'`.
  The inverse-image conditions are `hw : h ⁻¹' Set.range j = Set.range j'`
  and `hw' : k ⁻¹' Set.range j' = Set.range j''`. For open immersions, equality
  of these underlying open subsets is equality of the open subschemes. The
  composition formula uses `k ≫ h` (Lean's order) and constructs its triangle
  equality by `Category.assoc`, `congrArg`, and transitivity. Its inverse-image
  equality is `(congrArg (fun S : Set Z' ↦ k ⁻¹' S) hw).trans hw'`, with no
  additional hypothesis. Identity uses the definitional inverse-image equality
  `rfl`, with no extra identity-condition binder.
- Exact extension by zero is `(openImmersionLowerShriek Λ j).mapDerivedCategory`;
  exact open restriction is `(upperStar Λ j).mapDerivedCategory`; total direct
  image is `(lowerStar Λ h).rightDerivedFunctor`. Their definitions retain the
  canonical alpha/eta scalar transport. The adjunction and its unit are exactly
  `derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j` and `.unit`.
- The open unit is invertible: `normalized_open_refinement_unit_isIso` states
  `IsIso` of this natural transformation. `normalizedOpenRefinementUnitIso`
  installs that named theorem and uses `asIso`; its forward morphism is the
  original unit, not an independently selected map. Its proof plan explains
  transport of the existing support-localization assertion to upperStar.
- `r_h` is precisely `identityOpenDerivedRestriction Λ j j' h w`, from the
  dependency. Its invertibility is the first conjunct of
  `identity_open_derived_restriction Λ ℓ hΛ j j' h w hw`.
- Definition of e: `normalizedOpenRefinement` applies the inverse Hom equivalence
  of the actual open derived adjunction to
  `unit_j'.app K ≫ inv (r_h.app (j'_! K))`. This is exactly the specified adjoint
  of r_h inverse after eta_j'. The only proof-dependent data is the inverse of
  a specified invertible map, uniquely determined by its inverse identities.
- The displayed normalization is the first conjunct of
  `normalized_open_refinement_coherence`: in Lean composition order,
  `unit_j(K) ≫ j^*(e_h,K) ≫ r_h(j'_!K) ≫ eta_j'(K)^{-1} = 𝟙 K`.
  Its second conjunct quantifies every arrow with the same source and target
  and says that this equation forces `a = normalizedOpenRefinement ... K`.
  This is existence (the defined map is normalized) and uniqueness, not just
  an implication about a hypothetical normalized map.
- Naturality is `normalized_open_refinement_naturality`, for every morphism
  `v : K ⟶ L` between arbitrary unbounded inputs. It states
  `e_h,K ≫ Rh_*(j'_! v) = j_! v ≫ e_h,L`.
- Identity is `normalized_open_refinement_id`: the arrow for `h = 𝟙 Z`, followed
  by `(moduleDerivedIdentity Λ Z).hom.app (j_! K)`, is `𝟙 (j_! K)`. Thus the
  canonical identity constraint is explicit.
- Transitivity is `normalized_open_refinement_comp`:
  `e_hk,K ≫ (moduleDerivedCompositor Λ k h).hom.app (j''_! K) =
  e_h,K ≫ Rh_*(e_k,K)`. This is precisely the node's compositor direction.
  Functor compositions are evaluated at objects, so no additional associator
  is needed in this equation of individual arrows.
- No invertibility of the refinement arrow is claimed. All five postponed
  theorems carry source, blueprint id, and the applicable steps of the node's
  seven-step natural-language proof in their docstrings.

Dependency declarations read and used (including transitive statement imports):

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and the
  commutative ring-object instance. The construction is the strong monoidal
  pullback from the point, not a constant coefficient replacement.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, with `ModObj`
  and action-compatible morphisms.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit
  and resolution comparison; the Grothendieck module-object specialization
  here is the existing ordinary `DerivedCategory` and `rightDerivedFunctor`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, supplied
  through the recorded `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` module
  (whose `LocallyOfFiniteType` is not an additional hypothesis here).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek`, its exactness instances, and
  `openImmersionLowerShriekUpperStarAdjunction`; and its derived counterpart
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction`. This is the recorded
  extension-by-zero construction transported to the unbounded derived category.
- `Sheaf.Paper.ModuleDerivedCompositorCoherence`: `moduleDerivedCompositor`,
  `moduleDerivedIdentity`, with their normalization and coherence theorems.
- `Sheaf.Paper.IdentityOpenDerivedRestriction`: `identityOpenDerivedRestriction`,
  `identity_open_derived_restriction` and its `_comp`, `_id` companions.
- Proof imports `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps`
  (`openSupportDerivedAdjunction`) and
  `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`
  (`condensedSupportDerivedLocalization`). The alpha transport
  `supportPullbackIsoUpperStar` connects their support restriction to the
  same module upperStar used in the statement. All recorded proof modules are
  imported directly or through `IdentityOpenDerivedRestriction`.

Source read: the current main-20261015 blueprint's
`det-sf-comp-coherence-cocycle.proof.md` (Refinement isomorphisms and Independence)
and `det-sf-comp-coherence-refinement.proof.md` (The restriction to X, (1), (3)).
Also read `coord/pefw-upstream-framework.md`. The source's isomorphism assertion
in (2), which needs properness and support arguments, is intentionally not a
clause of this node and is not stated here.

Edge cases checked before writing and again after compilation:

- Empty U: extension by zero of the unique zero object and the same Hom
  bijection make every equation meaningful; no nonempty assumption occurs.
- Zero coefficient ring: allowed as a finite discrete admissible coefficient;
  the zero module category causes no failure of units or inverses.
- Arbitrary unbounded K: no truncations or cohomological bounds appear.
- h or k identity: the derived identity comparison is retained explicitly;
  the composite inverse-image proof specializes without another assumption.
- j identity: the inverse-image condition forces j' onto all of Z', but this
  consequence is not imposed as an independent hypothesis.
- Arbitrary scheme universe u and site object/morphism universe distinction:
  no equality between independent universes is introduced.

Searches for an existing exact statement (2026-10-21):

1. `msearch.py ... leanfinder "The adjoint of the inverse common-open restriction
   is the unique normalized extension by zero refinement arrow, natural in
   unbounded complexes and transitive under composition"`: eight hits, all
   `ComplexShape.Embedding` Hom-equivalence/extension declarations. No match.
2. `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv, CategoryTheory.NatTrans"`:
   zero hits. No match.
3. `msearch.py ... grep "normalizedOpenRefinement|refinement.*[Cc]oher|homEquiv_naturality"
   CategoryTheory/Adjunction`: 25 generic adjunction naturality hits, e.g.
   `Adjunction.homEquiv_naturality_left` and `_right`. These supply formal
   primitives, not this module-object specialization with its specified r_h
   and compositor.
4. `rg` across `lean/WeilConjectures` and `lean/Sheaf` for
   `normalizedOpenRefinement|normalized_open_refinement|refinement.*[Cc]oher|lem-sfb-normalized-open-refinement-coherence`:
   unrelated etale, coefficient and compactification coherence hits; no exact
   pro-etale unbounded statement. `grep -rn` for this node id in
   `lean/WeilConjectures` returned no hit. The proposed new declaration names
   also have no hit in Mathlib or `dag/lean_names_upstream.json`.
5. Follow-up `rg 'refinement|Refinement'` in the upstream pro-etale ModuleObject
   tree found `boundedConstructibleOpenImmersionLowerShriekRefinement` and
   related compactification independence isomorphisms. Read its signature and
   definition in `BaseChangeTheorems/LowerShriek/CompactificationIndependence.lean`:
   it uses bounded constructible categories, finite-extension coefficients,
   and a different pullback/extension-by-zero comparison. It does not provide
   this general unbounded normalized arrow or these laws, so it is not an
   `existing: true` match.

Validation: `scompile.py O3 lem-sfb-normalized-open-refinement-coherence <module>`
passed both its sandbox check (5.4 seconds) and library-module check (5.3 seconds)
on the server, with no errors or warnings. Every variable and universe is
explicit; `autoImplicit` is false. No local build or repository write was run.
No statement fault or disputed statement was found.

## Second reading by O3

A second self-check reopened the sandbox node and the complete Lean file, matching
the clauses above. The dispatcher explicitly forbids starting another agent, so
this section does not claim an independent worker review; the maintainer performs
the independent review on delivery. Checked the source/target of the transpose,
the order eta then r_h inverse, the order of all four normalization factors, and
the forward direction of `moduleDerivedCompositor Λ k h`. Naturality quantifies
all morphisms and identity is normalized through the existing derived identity.
Removed preliminary redundant identity and composite inverse-image proof binders:
the final statement constructs those proofs, so it adds no hollow hypotheses.
The three open immersions remain quasi-compact in the composition clause; all
complexes remain unbounded. All definitions have real data, all five theorem
proofs are exactly `sorry`, and the seven declarations are listed in the node.
