## Worker report

The module `Sheaf.Paper.CompactificationRefinementLocalizing` states
`AlgebraicGeometry.ProEtale.CondensedRing.localizingRefinement_coherence` for the actual
unbounded module-object derived categories. It supplies the canonical constructions
mentioned in the node, using the existing operations and coefficient identifications.
The node's natural-language statement and dependency lists are unchanged.

Hypothesis and clause correspondence:

- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field and characteristic are
  `(k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)`.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`, and
  `[IsCommMonObj Λ]` are the commutative condensed ring; `_hΛ :
  IsLocalizingAdmissibleCoefficient ℓ Λ` is precisely the recorded six-case convention,
  including finite discrete rings killed by an ℓ-power, valuation rings, finite
  subextensions, and all continuous maps into the indicated algebraic closure.
- Schemes `X Y : Scheme.{u}` have their `Over (Spec (.of k))` structures. Each structure
  morphism has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances.
  `f : X ⟶ Y` has `f.IsOver (Spec (.of k))`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`. Finite type is the latter two instances.
- `c d e : Compactification.DenseBoundaryCompactification f` use the dependency's
  category, without a copy of any compactification or refinement notion.
  `c.obj.obj.obj` is the recorded upstream compactification. Its `i`, `g`, `comm`,
  `isOpenImmersion`, and `isProper` give exactly j, q, f=qj, open immersion, properness.
  The middle `QuasiCompactObjects` property gives quasi-compactness of j; the outer
  full-subcategory property gives scheme-theoretic density. The schemes Z inherit their
  k-structure from q and Y (`Compactification.Over`, with the canonical `overZ`
  structure in the shared framework).
  Properness of q implies finite type and separatedness over Y, hence over k; j and q
  are over k by the compactification triangle. No independent extra choice or hypothesis
  on these middle schemes is imposed.
- For `r : d ⟶ c`, `r.hom` is the boundary-category arrow and
  `r.hom.hom.hom` is the upstream `Compactification.Refinement`. The scheme morphism h
  is `r.hom.hom.hom.hom`. Its `i_hom` and `hom_g` give hj'=j and qh=q'; the wide
  subcategory property gives the equality of inverse-image opens. Properness is the
  upstream instance `Compactification.Refinement.isProper`, using the proper q's.
- Every `K` is explicitly an object of
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X))`. This is the unbounded D(Mod_{Λ_X}) of the statement,
  with the existing Λ_X, internal modules, and universe convention. No boundedness,
  completion, fixed-scalar presentation, or etale-origin witness is substituted.
- `refinementOpenRestriction Λ r` is the canonical natural map j* Rh* M → j'* M.
  Its definition is derived exact pullback composition (using `r.i_hom`) followed by
  the counit of `derivedUpperStarLowerStarAdjunction`; the total/termwise pullback
  identification is `leftDerivedUpperStarIsoMapDerivedCategory`.
  Thus its action on a K-injective representative is precisely the restriction of
  direct image to the inverse-image open. It is not an arbitrary isomorphism.
- `refinementOpenRestriction_isIso` states the invertibility implicit in the displayed
  θ of the node; its proof docstring gives the sectionwise V×_Z Z'=V calculation,
  module-action compatibility, exactness, and K-injective argument for arbitrary M.
  `refinementOpenUnit_isIso` states the invertibility of the *actual* derived open
  adjunction unit, as used in the node. These are construction obligations within the
  refinement notion, rather than extra assumptions in the main theorem.
- `refinementTheta Λ r K` is `asIso` of that restriction map evaluated at j'!K,
  followed by the inverse of the actual open unit at K. The definition
  `localizingRefinementMap Λ r K` is exactly `homEquiv.symm` applied to θ.inv for
  `derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j`.
- Clause (1) is the first conjunct of `localizingRefinement_coherence`. For every
  dense c,d, refinement r, arbitrary unbounded K, and map b with the prescribed source
  and target, it states
  `η.app K ≫ D(j*).map b ≫ θ.hom = 𝟙 K ↔ b = localizingRefinementMap ...`.
  Lean composition runs left to right. This biconditional includes the normalized
  restriction of e itself (substitute b=e), and uniqueness of every such b.
- Clause (2) is the second conjunct: the sole additional condition is
  `localizingClosureProEtale Λ X K`, and the conclusion is `IsIso` of that same map.
  The imported closure uses the recorded constant-model bounded constructible
  finite-Tor objects and ambient sums; no replacement of Dctf or Loc is made.
- Clause (3), identity, is the third conjunct. `localizingRefinementMap Λ (𝟙 c.obj) K`
  followed by `refinementDerivedLowerStarId ... .hom.app (D(j!).obj K)` is the identity.
  The explicit identification is derived from the abelian-sheaf `lowerStarId`, lifted
  to modules with the same underlying components and derived using the generic
  `rightDerivedFunctorNatIso` and exact identity-functor identification. It has real
  data, not an unnormalized existence witness.
- Clause (3), successive refinements, is the fourth conjunct. For r:d→c and s:e→d,
  the map for `(s ≫ r).hom` followed by
  `refinementDerivedLowerStarComp ... .hom.app (D(j''!).obj K)` equals the map for r
  followed by `R(h*).map` of the map for s. The compositor is constructed from
  `lowerStarComp` and `rightDerivedFunctorCompIso`, hence normalized by the canonical
  K-injective derived-functor units. Its orientation is
  `R(a ≫ h)_* ≅ Ra_* ⋙ Rh_*`, representing Rh_*Ra_* in function notation.
  Both identity and composition quantify over arbitrary unbounded K.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField`, and the imported `Compactification.Over` structures
  `overZ`, `isOver_i`, `isOver_g`, and their finite-type/separatedness instances;
  the standing setting is rendered by explicit binders, as its record prescribes.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, publicly importing
  `Sheaf.Paper.LocalizingClosure.localizingClosureProEtale` (namespace
  `AlgebraicGeometry.ProEtale`).
- `def-weil-size-convention`: a recorded metatheoretic convention; explicit universe u,
  the object/morphism levels of `Scheme.ProEt.topology`, `Ab.{u+1}`, and the existing
  internal-module/derived-category instances implement it. No new object is defined.
- `det-def-sfb-constructible-tor-amplitude`: `Sheaf.Paper.ConstantModelTorAmplitude`,
  `constantModelConstructibleFiniteTor_wellDefined`, importing
  `CondensedConstantConstructibility` and its constant-model constructible finite-Tor
  category and bounded-constructibility predicate. The recorded closure uses these.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `CondensedRing.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`,
  `lowerStarComp`, and `upperStarComp`.
- `sk-def-sfb-module-derived-pushpull`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `CondensedRing.derivedUpperStarLowerStarAdjunction`,
  `leftDerivedUpperStarIsoMapDerivedCategory`, and generic
  `Functor.rightDerivedFunctor` applied to the recorded underived composite.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `CondensedRing.openImmersionLowerShriek` and its adjunction; its exact termwise
  derived adjunction is the published
  `ModuleObject.Derived.OpenImmersionLowerShriek.derivedOpenImmersionLowerShriekUpperStarAdjunction`
  in the same `CondensedRing` namespace.
- `sk-def-nagata-sketch-data`: `Sheaf.Compactification.BoundaryRefinement`,
  `Compactification.QuasiCompactObjects`, `boundaryRefinementProperty`,
  `BoundaryCompactification`, and `DenseBoundaryCompactification`.

All recorded statement modules and available proof modules are imported. Proof nodes
`det-sf-comp-coherence-single` and the finite/integral/rational proper-base-change
statements currently have no recorded Lean module, so there is no import to add for them.
They are proof dependencies only: they are not assumed in this statement, and no
replacement theorem is silently supplied. Existing exact adjunction, K-injective,
open/closed, localization, composition, and localizing-isomorphism-locus proof interfaces
are imported. No import cycle is introduced.

Searches for an existing statement:

- `msearch.py ... leansearch "proper refinement of a compactification preserves derived
  extension by zero on localizing constructible module complexes"`: eight hits,
  including `Functor.mapDerivedCategoryFactors`, derived localization and bounded
  representatives, plus compactly supported functions; none is this refinement theorem.
- `msearch.py ... leanfinder "proper refinement comparison from extension by zero to
  unbounded derived module pushforward is invertible on localizing closure"`: eight
  hits concerning homological localization and derived-category bounded representatives;
  no matching refinement comparison.
- `msearch.py ... loogle '"pushforwardComp"'`: twelve hits in presheaf/module-sheaf
  underived pushforward composition, including `SheafOfModules.pushforwardComp` and
  `Scheme.Modules.pushforwardComp`; none has this coefficient category or conclusion.
- `msearch.py ... grep 'refinement|lowerShriek' Algebra/Category/ModuleCat/Sheaf`: zero hits.
- `rg` in the upstream WeilConjectures source for the blueprint id: zero hits.
  Searching refinement maps found Etale/Derived/LowerShriekCoherence, a different
  sheaf-coefficient setting. The shared pro-etale ModuleObject framework has the
  exact operations but no refinement map or restriction comparison of this statement.
- `rg` in `lean/Sheaf` found `CompactificationCoherence` and `RefinementExchangeCoherence`:
  their domains are witnessed finite etale-origin objects or strict towers, respectively;
  neither states the ambient internal-module localizing theorem. Searching all proposed
  declaration names in Mathlib, WeilConjectures, and `lean/Sheaf` found no collision.
- Read the complete recorded dependency declarations, the current blueprint node and
  proof route, and `coord/pefw-upstream-framework.md`. The live coefficient source was
  additionally confirmed with `scompile.py --source Sheaf.Paper.LocalizingAdmissibleCoefficients`.

Edge cases checked before writing:

- Empty X and the zero complex impose no nonemptiness or nonzero hypotheses. Boundary
  equality and scheme-theoretic density are retained even for the empty compactification.
- Identity refinements are genuine arrows of the recorded category; their raw scheme
  maps reduce to the identity and the equation includes the actual derived identity iso.
- Successive refinements use the recorded category composition, retaining the boundary
  equality and both triangles. The target type checks with the canonical compositor.
- Arbitrarily unbounded K is allowed in uniqueness, the definition of θ and e, and both
  coherence equations; only invertibility uses Loc(Dctf).
- Finite zero coefficient rings are not excluded, nor is exponent zero in the recorded
  ℓ-power torsion condition. Z_l/Q_l and all other coefficient cases remain present.
- The field has positive characteristic unequal to ℓ, exactly as in the standing setting.
  All universes and variables are explicit (`autoImplicit false`); the small pro-etale
  site's different object and morphism levels are unchanged.

There are no statement faults or STATEMENT-DISPUTED claims. Eleven declarations belong
to the node: six real-data definitions, and five named theorems with `sorry`:
`refinementLowerStarId_linear`, `refinementLowerStarId_naturality`,
`refinementOpenUnit_isIso`, `refinementOpenRestriction_isIso`, and
`localizingRefinement_coherence`. Their source/proof docstrings cover the construction
obligations already implicit in the node and its three conclusions. No extra independent
notion or new DAG node is introduced.

Validation: `scompile.py N1 det-sf-comp-coherence-refinement <module>` compiled the
sandbox probe and its final library module cleanly under the default 60-second per-file
limit. An initial missing `open scoped CategoryTheory.Obj` was repaired to expose the
recorded coefficient ring-object instances. No universe restriction or extra assumption
was added to resolve the elaboration error.

## Second reading by N1

This is a separate self-audit pass by the dispatched worker, not a claim of a second
independent agent: the dispatch brief prohibits starting agents and specifies that the
maintainer independently reviews the delivery.

With the node and the final file open, rechecked the standing field/characteristic and
all six coefficient cases; the compactification category's three nested object layers
and four refinement projections; quasi-compactness, density, both triangles and boundary
preservation; the exact source/target of θ and its inverse; and that `homEquiv.symm` is
in the j! ⊣ j* direction. The first conjunct is an iff for every map b, which gives both
existence of the identity-normalized e and uniqueness, rather than uniqueness conditional
on a forgotten normalization. The localizing hypothesis appears only in the second
conjunct. The final two conjuncts quantify over all K, and their compositors have the
orientation required for the right-hand side `e_h ≫ Rh_*(e_a)`. The identity iso is
specified on actual underlying sheaves. The restriction comparison is the canonical
counit mate, so no arbitrary iso, stronger proper-base-change assumption, or finite-origin
restriction enters the construction. No statement mismatch was found. Added direct
imports for the recorded operations and existing proof interfaces before the final checks.
