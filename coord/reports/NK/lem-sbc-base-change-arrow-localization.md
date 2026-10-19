## Worker report

Item: lem-sbc-base-change-arrow-localization. The module
`Sheaf.AlgebraicGeometry.BaseChangeArrowLocalization` states
`AlgebraicGeometry.Etale.BaseChangeLocalization.baseChangeArrow_localization`.
Its proof is the sole `sorry`. Every helper definition has actual data.
The node's statement, proof and proof dependencies are unchanged. The statement
 dependencies gain the already landed `sbc-def-base-change-map`, to reuse its
set-valued arrow and its adjunction. No independent notion or new node is introduced.
The constructions of the canonical comparisons belong to this node, under the
missing-helper authorization of the stage-2 brief.

Hypotheses and clauses, with `BaseChangeLocalization.` suppressed below:

- Arbitrary schemes X,Y,S,T and f:X→S, g:T→S, h:Y→X, e:Y→T are the explicitly
  declared scheme and morphism variables. `sq : ChosenCartesianSquare h e f g`
  is exactly the recorded base-change square, with chosen Cartesian identification
  and its projection equations. No properness or smoothness assumption is made.
- The objects U,B and arrows a:U→X, b:B→S have `[Etale a]`, `[Etale b]`.
  The morphism f_U is `fU : U ⟶ B`; the factorization hypothesis is exactly
  `fac : a ≫ f = fU ≫ b`. There is no étaleness assumption on fU.
- T_B is `pullback b g`, g_B is `pullback.fst b g`, c is `pullback.snd b g`.
  Y_U is `pullback a h`, h_U is `pullback.fst a h`, d is `pullback.snd a h`.
  Thus the order of both factors agrees with the natural statement.
- `localArrow sq a b fU fac` is e_U. Its two components are h_U followed by fU,
  and d followed by e. It is defined by `pullback.lift`, using the factorization,
  global square commutativity and the pullback equation. In particular
  `pullback.lift_snd` gives e_U followed by c = d followed by e.
- `localSquare` constructs the chosen Cartesian local square, rather than taking
  it as an additional assumption. It converts sq's specified identification into
  the corresponding limit, pastes with Y_U's pullback square, then cancels T_B's
  pullback square. Its iso is the unique projection-preserving pullback iso.
- The actual sites are `Scheme.smallEtaleTopology`. Scheme objects have universe
  u, site objects u+1 and morphisms u. The coefficient categories are precisely
  `Type (u + 1)` and `AddCommGrpCat.{u + 1}`. No site-universe equality is imposed.
- Every r_Z is the existing `Etale.localizationRestriction A j inferInstance`.
  Its value on V→Z is the original sheaf's value on V→Z→the ambient scheme.
  In particular F_B is precisely `(localizationRestriction A c _).obj F`.
- In the set case, inverse image and its adjunction are the already recorded
  `Scheme.etaleSetPullback` and the landed `Etale.setUpperLowerAdjunction`.
  In the abelian case they are `Etale.upperStar AddCommGrpCat` and
  `Etale.upperStarLowerStarAdjunction AddCommGrpCat`. Both use the canonical
  sheafified presheaf inverse image. Direct image is always `Etale.lowerStar`.
- The global/local beta for sets is the EXISTING `Etale.setBaseChangeArrow`;
  for abelian groups it is `(Etale.baseChangeMap _ q.toCommSq.flip).app F`.
  The flip gives exactly f^{-1}g_* → h_*e^{-1}. The set arrow is the inverse
  mate of the direct-image comparison: transposing twice gives precisely the
  theta-and-counit transpose under h^{-1} ⊣ h_* in this node. Neither arrow
  is supplied as an unconstrained hypothesis or redefined in the delivery.
- `pullComp` takes the adjoint of the existing `Etale.lowerStarComp`, with the
  actual adjunctions. `squareIso` composes these comparisons along the common
  diagonal. `restrictionIso` is the canonical `leftAdjointUniq` between inverse
  image and restriction, sharing the same direct image. This is the unit-normalized
  comparison of the recorded set and abelian restriction lemmas, rather than a
  choice from their existence assertions. The generic helpers share the formulas
  between the two coefficient categories; the theorem fixes all their parameters.
- `inverseRestrictionSquare` is r_U f^{-1} ≅ f_U^{-1} r_B, built by replacing
  restriction with inverse image along a, composing along fa=bf_U, then replacing
  inverse image along b with restriction. `directRestrictionSquare` is restriction
  of direct image ≅ direct image of restriction. It inverts only the canonical
  site-level `MorphismProperty.Over.pullbackMapComparison` of a Cartesian square,
  then uses `Functor.sheafPushforwardContinuousIso`. Its section maps are exactly
  restriction along the projection-preserving isomorphism of fibre products.
- `leftComparison` is C_L: inverse-image/restriction composition followed by
  the slice comparison for g at B, whiskered by f_U^{-1}.
  `rightComparison` is C_R: the slice comparison for h at U followed by the
  inverse-image/restriction square for ed=ce_U, whiskered by h_U*. Both are actual
  natural isomorphisms built by whiskering and composing the specified comparisons.
- `Compatible`'s first conjunct is, for EVERY F, `r_U.map (beta F) ≫ C_R.app F =
  C_L.app F ≫ beta_local F_B`, exactly C_R ◦ r_U(beta_F) = beta_local ◦ C_L.
  Its second conjunct quantifies over EVERY sheaf morphism φ:F→G and writes the
  naturality square for this common composite, with its stated source/target
  functors. Thus naturality is explicitly included, not asserted just in prose.
  The theorem's two conjuncts instantiate this predicate for sets and abelian
  groups separately. No preservation or invertibility of beta is assumed.

Dependencies read and reused (module → declarations):

- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso` and its public dependency
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` →
  `ChosenCartesianSquare`, its commutativity, chosen iso and projection equations;
  `ChosenCartesianSquare.baseChangeInverseImageIso` supplies the abelian comparison
  convention. The shared formulas use its adjunction construction also for sets.
- `Mathlib.AlgebraicGeometry.Sites.Etale` → `Scheme.smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` → `Etale` and `Scheme.Etale`;
  `Mathlib.CategoryTheory.Sites.Sheaf` → `Sheaf`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` → `pullback`,
  its projections, lift and projection equations.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` → `Etale.lowerStar`,
  `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`, `Etale.lowerStarComp`,
  `Etale.upperStarComp`. `WeilConjectures.SixFunctors.BaseChange.Square` →
  `Etale.baseChangeMap`, with exactly its canonical square comparison and transpose.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` →
  `etaleSetInverseImageCompositionUnits`; its source was read with
  `scompile.py --source`, including the canonical adjoint construction.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction` →
  `etaleSetInverseImageRestriction`; current source read with `scompile.py --source`.
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` →
  `Etale.localizationRestriction`, `Etale.localizationRestrictionLowerStarAdjunction`,
  `Etale.upperStarIsoLocalizationRestriction`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver` → `Scheme.Etale.overEquiv`
  and `overSheafEquiv`; `Sheaf.Paper.SliceSiteLocalization` → `slice_site_localization`;
  `Sheaf.CategoryTheory.SiteMorphismComposition` → `siteMorphism_composition`.
  These are imported as part of the proof plan; their explicit schemes specialization
  is constructed by the canonical comparisons just described.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets` →
  `Etale.setUpperLowerAdjunction`, `Etale.setBaseChangeArrow`, from the added landed
  dependency sbc-def-base-change-map. Read its full signatures, formulas and docstrings.
- `Mathlib.CategoryTheory.Sites.Sheafification` → `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`, imported for the last proof step.
- `def-weil-size-convention` is metatheoretic, with no declaration to import; its
  size convention is expressed by the explicit universes above.

The two sectionwise exchange proof dependencies currently have no recorded Lean
module, so no nonexistent proof import was added: lem-sbc-sets-underived-exchange-sectionwise
and lem-weil-pbc-underived-exchange-sectionwise. Their natural-language representative
arguments are cited in the main theorem docstring, including kappa ell_loc = ell_glob
and the universal property of sheafification. They are proof prerequisites only;
no undeclared notion from them occurs in the statement.

Edge cases checked before writing: identity localizations a=id, b=id recover the
original square with the canonical pullback identifications; empty U and empty B
are allowed without a nonemptiness or cover hypothesis; fU can be arbitrary,
including an isomorphism; the sheaf F can be empty (sets) or zero (abelian groups).
The factorization need not be Cartesian. No comparison is formed by assuming the
base-change arrow invertible. The map kappa in the proof is not claimed to be an
isomorphism. Different choices of the original Cartesian identification are
allowed by the original square's exact data, with all its projection equations.
No false statement, omitted object, or disputed clause was found.

Searches for existing statements and constructions:

- msearch leanfinder, query `underived base change natural transformation commutes
  with restriction to etale neighborhoods`: eight hits about etale morphisms and
  differentials, none about the arrow compatibility.
- msearch loogle, query `CategoryTheory.Adjunction, CategoryTheory.NatTrans`: zero hits.
- msearch grep, query `baseChange.*[Ll]ocal|[Ll]ocal.*[Bb]aseChange`, Mathlib/CategoryTheory:
  two unrelated morphism-property stability hits, no arrow-localization theorem.
- msearch leansearch, query `canonical sheaf base change morphism compatible with
  etale localization`: eight hits about differentials/affine geometry, no match.
- rg over Mathlib Sites and the source/project modules for baseChange/restriction,
  square comparisons and pullback-map comparisons found `lowerStarComp`,
  `pullbackMapComparison`, `sheafPushforwardContinuousIso` and the canonical
  adjunction comparisons used here. The broad source/project search found no
  arrow-localization identity. The exact node-id search of WeilConjectures had
  no hits. A targeted set-exchange search found the landed setBaseChangeArrow;
  it is imported and reused, replacing the initial planned helper.
- A read-only DAG reachability check found no path from the newly added landed
  dependency sbc-def-base-change-map back to this item (328 nodes visited).

Validation: scompile.py compiled the delivered file cleanly in both its sandbox
and library module paths, with no errors and no warnings (55.7 s and 31.3 s,
respectively, each below 60 s). The final theorem is intentionally postponed.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
