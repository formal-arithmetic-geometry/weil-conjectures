## Worker report

Item: `lem-sfb-module-direct-image-open-pasting` (Q58, stage 2).
Module: `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting`.
Main declaration:
`AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting.moduleDirectImageOpenPasting`.
The only postponed proof is this theorem, with the node's eleven-step proof in its
source docstring. All ten helpers are actual definitions spelling out this same
node's comparisons, coordinates, and clauses; none chooses data from a postponed
existence theorem. The node changes only in `lean`.

Sources read: the current blueprint `sk-thm-sf-comp-composition.proof.md`, especially
Composition isomorphism and Canonicity and associativity; Stacks `proetale.tex`,
`section-morphism` (09A5); `sites.tex`, `section-localize` (00XZ);
`sites-modules.tex`, `lemma-adjoint-push-pull-modules` (03D3),
`definition-pushforward` (03D6), and `section-localize` (03DH).
The coherence equations are the node's explicit agent formulation of this calculation.

Hypotheses and objects:

- An arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is the unbundled presentation of the dependency's
  `Profinite.CondensedRing = Mon (...)`; no topological presentation is required.
- Schemes all have type `Scheme.{u}`. Their sites are the existing `Scheme.ProEt`
  with `ProEt.topology`; coefficients have universe `u + 1`, the published
  framework's common site/coefficient size convention. No equality of site object
  and morphism universes is imposed.
- `condensedRingObj Λ X` is precisely the recorded `p_X^* Λ` construction;
  `Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)` is the recorded
  category of internal module objects. There is no replacement module category.
- `lowerStar`, `upperStar`, and `upperStarLowerStarAdjunction` are the recorded
  module operations and their specified adjunction. `lowerStarComp` is their
  specified compositor. Every occurrence of the node's `c` is its `.inv`.
- The coefficient maps are `condensedPullbackHom Λ f`. Their isomorphism assumption
  is already supplied by `ProEtale.isIso_condensedPullbackHom` for this pulled-back
  coefficient system. `inverseImageActionIso` explicitly identifies `upperStar`
  with sheaf inverse image followed by `Mod.comap (inv (condensedPullbackHom Λ f))`.
  Its body is the existing `Mod.extendScalarsIsoComapInv`, whiskered by the actual
  sheaf pullback on modules. Thus both open actions in (a) use alpha inverse.
- `j`, its pulled-back open `i`, and successive opens `v`, `k` have their ordinary
  `IsOpenImmersion` instances. `IsPullback i fU f j` specifies exactly the fibre
  product and its projections, without properness, quasi-compactness, a base
  field, or any finite/discrete coefficient assumption.
- The exact open extension by zero and its specified adjunction are reexported
  from the dependency module. They are background operations here, rather than
  extra arbitrary adjunctions or extra hypotheses on the statement.

Clause-by-clause rendering:

- Natural module isomorphisms: `Comparisons Λ` is a family of natural isomorphisms
  `lowerStar Λ f ⋙ upperStar Λ j ≅ upperStar Λ i ⋙ lowerStar Λ fU` on cartesian
  squares. The theorem asserts existence of one family satisfying all clauses
  simultaneously. Its components are morphisms of the actual module-object
  category, so their linearity concerns the specified actions.
- Clause (a): `coprojection Λ j M E` uses the specified module-adjunction unit,
  then restricts along the distinguished graph object supplied by the existing
  site `mapPullbackAdj`. `Sectionwise` asserts bijectivity of these canonical
  open-slice coordinate maps for every open, module, and object. Its second
  conjunct states the exact equation for beta on each section through these
  coordinates. `sectionArrow` is `pullback.map` with identity on the test scheme
  and `i` on the other factor; its two projections specify the canonical
  identification of the fibre products. This arrow is an isomorphism because
  the square is cartesian. In particular the equation fixes beta completely,
  rather than merely asserting some isomorphism of its endpoints.
- The other lift in (a): the first conjunct of `Composition` identifies the
  underlying map of `lowerStarComp.inv` with restriction along
  `(MorphismProperty.Over.pullbackComp f g).inv.app V`. This is exactly the
  sectionwise map of the recorded abelian-sheaf compositor.
- Clause (b): the second conjunct of `Composition` expands both inverse
  compositor paths. `Functor.associator.inv` supplies the common bracketing and
  `lowerStarCongr (Category.assoc f g h).inv` transports the composite scheme map.
  In ordinary composition notation these are the node's two displayed paths.
- Clause (c): `SuccessiveOpens` states the equation for the outer square
  `sqW.paste_horiz sq`. The right path first applies `upperStarComp v j`, then
  beta for the first and second open (whiskered as appropriate), then
  `upperStarComp k i` inverse at the pulled-back opens. All three functor
  associators appear explicitly.
- Clause (d): `MixedPasting` compares the outer square `sqF.paste_vert sqG`
  with the two inner squares. The left path first expands `c_{g,f}`, applies
  beta for `g`, then beta for `f`; the right path applies beta for the composite
  and expands `c_{gU,fU}`. The final functors are literally identical.
- Canonical fibre-product identifications: the square presentation allows any
  representative equipped with its actual projections and `IsPullback` proof.
  Taking `P = pullback f j` and the canonical projections gives the node's chosen
  fibre product. Conversely every such square is uniquely isomorphic to that
  chosen pullback preserving both projections. `sectionArrow` fixes the maps
  under this identification, so no extra arbitrary comparison or hypothesis
  has been introduced.
- Identity cases: `Units` gives beta for the identity open and for the identity
  scheme morphism using `upperStarId` and `lowerStarId`, and gives both
  composition-unit laws using the canonical functor unitors and `lowerStarCongr`.
- Complexes: `Degreewise` quantifies over every `CochainComplex (...) ℤ` and
  every pair of integer degrees, expressing naturality of beta and `c` at
  `K.d n m`. This makes their components cochain maps. Their inverses are
  cochain maps by invertibility. The other equations already quantify over
  every module, so applying them to `K.X n` gives every required degreewise
  equality. No derived-category operation or resolution is asserted.

Dependency declarations read and used:

| Dependency | Recorded module and declarations used |
| --- | --- |
| `sk-def-sfb-condensed-ring` | `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, unbundled as its underlying sheaf and the two ring-object classes. |
| `def-weil-pbc-proetale-site` | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`. |
| `sk-def-sfb-pulled-back-coefficients` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`, `condensedRingObj`, and commutativity preservation. |
| `sk-def-sfb-module-pushforward-pullback` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `CondensedRing.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`, `upperStarComp`. |
| `sk-def-sfb-module-lower-shriek` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`: `openImmersionLowerShriek`, its exactness and `openImmersionLowerShriekUpperStarAdjunction`, reexported as the background operation. |
| `def-sfb-finite-lower-star-comp` | `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`: `ProEtale.lowerStarComp`; section formula in the transitively imported `.UpperLowerStar.Iso`. |
| `lem-sfb-proetale-open-restriction-counit` | `Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`: `Scheme.ProEtaleOpenRestriction.objectComposition`; the main `proEtaleOpenRestrictionCounit`, `Sectionwise`, and `sectionArrow` are the proof input and normalization template. |
| `def-weil-abstract-derived-category` | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the existing `CochainComplex`, with objects `X` and differentials `d`; the recorded `DerivedCategory` is deliberately not invoked in the conclusion. |
| `sk-def-sfb-module-objects` | `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `Mod.Hom`, underlying `X` and `hom`. |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, projections, `pullback.map`; `IsPullback` and its pasting laws express the canonical identification of representatives. |
| `def-sfb-module-upper-star-comp` | `Mathlib.CategoryTheory.Adjunction.CompositionIso`: `Adjunction.leftAdjointCompIso`. The existing `CondensedRing.upperStarComp` body is precisely the same `conjugateIsoEquiv` expression with the recorded adjunctions and compositor; it is used directly rather than copied. |

The existing `ModuleObject.UpperLowerStar.Coherence` additionally supplies
`lowerStarCongr`, `lowerStarId`, `upperStarId` and the ordinary composition
coherence laws. These are existing canonical normalizations of the same operations.
The remaining stated proof dependencies are imported (possibly transitively):
`Sheaf.CategoryTheory.SheafTensorStructure`, the module-object definitions above,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`, the general operations
reexported by `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, and Mathlib's
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`.
The coefficient eta-composition and eta-identity inputs are already the declarations
`ProEtale.condensedPushforwardHom_comp` and `ProEtale.condensedPushforwardHom_id` in
`ModuleObject.Basic`; the latter node has no `lean` attachment yet, but its exact
upstream theorem exists. `lem-sfb-section-ring-lax-pushforward-coherence` has no
recorded Lean declaration to import; it is a proof-only prerequisite and supplies
no missing notion in this statement. Its proof-plan citation is retained verbatim
in intent. No dependency module repair or new definition node is needed.

Edge cases checked before writing and on rereading:

- Identity `f`, identity `j`, and either identity factor of `c`: explicitly covered
  by `Units`, with the correct left/right functor unitors.
- Empty opens, empty schemes, and empty successive opens: the same cartesian
  squares and graph coprojections exist, with no nonemptiness binder or division.
- Zero module and zero complex: all maps remain additive module morphisms and the
  same equations apply; there is no nonzero-ring or nonzero-module assumption.
- Every integer degree, including degree zero and differentials with zero target:
  `Degreewise` has no boundedness or degree-sign restriction.
- Arbitrary morphisms `f`, `g`, `h` and arbitrary commutative condensed rings:
  neither finite type, properness, a characteristic, a discrete topology, nor a
  finite cardinality condition enters a binder.

Searches actually made:

1. `msearch.py ... leanfinder "Direct image module objects proetale open restriction base change composition pasting associativity"`:
   eight hits, including scheme-Zariski `Modules.restrictFunctorComp` and
   `Modules.pseudofunctor_associativity_assoc`, but no general condensed
   pro-etale module comparison with both open-pasting laws.
2. `msearch.py ... loogle "SheafOfModules.pushforward_assoc"`: one hit, the
   ordinary module-sheaf direct-image associativity theorem. It supplies only
   part of this node, not the normalized open-slice comparison and its pasting.
3. `msearch.py ... grep "pushforward_assoc|pushforwardComp|restrictFunctorComp"`:
   25 hits in Zariski modules and generic sheaves/presheaves of modules; none
   states the whole node. Existing component constructions are reused above.
4. `msearch.py ... leansearch "proetale sheaves of modules open restriction direct image composition coherence"`:
   eight hits, including `SheafOfModules.pushforwardComp`, `pushforward_assoc`,
   `pullbackComp`, and Zariski restrictions. Again no exact match.
5. `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the proposed namespace/theorem name found
   no collision. `grep -rn` for the node ID in `lean/WeilConjectures` found no
   declaration. The closest upstream `ModuleObject.UpperLowerStar.Coherence`
   gives composition and identity coherence only. The module-object base-change
   files give bounded-constructible derived comparisons with field/coefficient
   assumptions; they cannot state this arbitrary underived theorem.

No statement dispute, source correction, or item-statement change was needed.

Validation: the final file compiled cleanly through the prescribed `scompile.py`
wrapper, both as sandbox and at its library module path (28.0 s and 20.9 s).
The prescribed `deliver2.py --no-push` dry run also passed server preflight and
per-file compilation (dry-run commit `492d6361827`, no push).
All universes and variables are explicit (`autoImplicit false`); lines are at
most 100 characters; there is exactly one `sorry`, the main theorem's whole proof.

## Second reading by Q58

This is a separate rereading by the same worker; the dispatch brief prohibits
starting another agent and assigns independent review to the maintainer.
I reopened the node and final source and checked the following specific points.

`Comparisons` has the correct direction `j^* f_* → fU_* i^*`. The chosen `c` is
`lowerStarComp.inv`, not the opposite direction. Its section formula therefore
uses `pullbackComp.inv`, and both `.hom` projections in the Lean expression are
needed to reach the map of section groups. The two occurrences of `coprojection`
in `Sectionwise` use respectively `j` on `f_* M` and `i` on `M`; the intervening
arrow is identity on the test scheme and `i` on the pulled-back scheme.
`inverseImageActionIso` visibly uses alpha inverse and introduces no new ring map.

For (b), I checked that the common source is the pushforward for `f ≫ (g ≫ h)`
and the target is `(f_* ⋙ g_*) ⋙ h_*`; the right path begins with the inverse
geometric congruence and the left path ends with the inverse functor associator.
For (c), the outer open maps are `v ≫ j` and `k ≫ i`; the first upper-star
compositor points forward, the last points backward. For (d), the two inner
squares paste vertically, and the common target is
`jX^* ⋙ (fU_* ⋙ gU_*)`. These checks resolved the potential bracketing and
compositor-direction mismatches before delivery; no node correction was needed.

The identity-open law removes `upperStar (id)` using the upper-star unit;
the identity-morphism law removes `lowerStar (id)` using the lower-star unit.
The final two unit clauses are the existing composition-unit normalizations.
The complex equations have `A(d) ≫ tau_m = tau_n ≫ B(d)`, so they express the
correct cochain-map equation, not its reversal. Empty schemes and opens are not
excluded by any family index or hypothesis. The final source has no additional
geometric or coefficient assumptions and the statement has no derived assertion.
