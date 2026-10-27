## Worker report

Item: lem-pur-integral-orientation-reduction-injectivity. The module
`Sheaf.Paper.IntegralOrientationReductionInjectivity` states
`AlgebraicGeometry.ProEtale.SpIntegralOrientation.reduction_injectivity` with one
postponed proof. Its other declarations are actual constructions from recorded
interfaces: `realizedRight` abbreviates the existing derived-limit right adjoint;
`beta` composes its fully faithful reduction Hom equivalence with its specified
right-comparison isomorphism; `delta` is `Adjunction.rightAdjointUniq`;
`targetComparison` is beta(identity); and `rho` reduces the given arrow and composes
the actual target comparison and the supplied finite exceptional comparison.
No theorem is proved, and no definition chooses data from an undetermined existence.
The node's statement, dependencies and proof are unchanged.

Hypothesis and clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum`; its prime, finite base field and
  fixed algebraic closure are the recorded fields. `l`, `[Fact l.Prime]` and `_hl`
  say that ell is prime and different from the characteristic. `E`, its field,
  algebra and finite-dimensional instances say E/Q_ell is finite. `Ω` and `_iE`
  retain its inclusion in a fixed algebraic closure (a field algebra hom is injective).
- X and Y are schemes over `Spec D.k`; each structure morphism is separated,
  locally of finite type and quasi-compact. These are exactly separated finite type.
  The compactification is the specified open/proper factorization `j,p`; f is
  `j ≫ p`. `IsOver` makes it a k-morphism and `SmoothOfRelativeDimension d` gives
  pure relative dimension `d : ℕ`. Its separatedness follows from the factorization.
  Quasi-compactness and compactifiability required by the existing interfaces are
  implied by this geometry, not new geometric restrictions.
- Completed coefficient modules and their derived-complete constructible full
  subcategory are the recorded `scalarReductionSource` and
  `sfIntegralConstructibleCategory`. No discrete constant O_E module category is used.
  RX/RY are the recorded simultaneous derived reduction models; q.abelian fixes
  the actual strict coefficient-tower categories. NX/NY are their normalized
  equivalences. The index n represents exponent n+1, so every positive power of
  ell, including the first, occurs. The quotient tower is the recorded ell-power
  tower; its relation to uniformizer-power completed coefficients is already part
  of the published reduction interfaces.
- The common finite Tor domain is retained by the published constructible-Tor tower
  categories `SpTowerCalculus.C`. The integral unit and shifted Tate line belong to
  the finite-Tor subcategory; working with their representatives in the ambient
  full constructible subcategory gives identical Hom sets. T and U are *not*
  arbitrary replacements: `_hT` identifies T.obj with
  `(singleFunctor _ 0).obj (integralTwistLine l E X d)` shifted by 2d; `_hU`
  identifies U.obj with the completed coefficient sheaf's regular module in degree
  zero. Thus the theorem's Hom is exactly Hom(1_X(d)[2d], J 1_Y), in full-subcategory
  coordinates. The full-subcategory representative is allowed to be any isomorphic
  representative of that fixed object; no membership or isomorphism assertion is
  inferred from an arbitrary object.
- `hF,G,a,lv` are the existing tower compact-support/right-adjoint realization with
  its actual finite units and counits. `R : SpIntegralAdjunction.Realization ...`
  is precisely the realization specified by det-sp-integral-adjunction-bijection;
  the dependency asserts its existence. It contains the diagonal tower orientation
  as `R.purity.orientation` and all normalization data. These are the fixed
  constructions the node asks to use, not arbitrary maps or conclusions assumed
  anew in place of injectivity.
- P is `SpIntegralAdjunction.support ... R.support_closed`, the separately
  constructed completed compactification composite. H is `realizedRight`, exactly
  the existing `SpIntegralAdjunction.right`, constructed by the total limit of
  G_bullet r_Y. J and adjJ specify the integral exceptional inverse image with its
  adjunction to that same P. The theorem works for every such specified right
  adjoint, so in particular for the node's G. `delta` is the unique canonical
  counit-preserving comparison R.adjunction.rightAdjointUniq adjJ.
- `beta` has the displayed integral-to-tower direction. Its target is the full
  constructible subcategory of the actual derived tower category; `.hom` forgets
  only the full-subcategory wrapper. The Hom arrows are the same derived arrows.
  `targetComparison` is exactly beta at H(U) applied to its identity.
- The first conjunct is beta_T(delta^{-1} h) = r_X(delta^{-1} h) followed by
  targetComparison. Lean uses diagrammatic composition, hence `h ≫ delta.inv`
  for the node's delta^{-1} h and r_X(u) ≫ lambda for lambda composed with r_X(u).
- `rho` is defined independently of beta's value: evaluate the ordinary reduction
  of h ≫ delta.inv, then compose evaluation of R.rightComparison and lv.comparison.
  The latter is the specified target identification with the finite exceptional
  image of the reduction of U. Thus the second conjunct is exactly level evaluation
  of beta equal to rho, with that target identification displayed. `_hU`, `_hT`
  identify these finite representatives with the finite unit and shifted Tate line;
  transporting along those isomorphisms leaves both identities and injectivity
  unchanged. Evaluation is `spDerivedCoefficientEvaluation`, not an arbitrary family.
- The last conjunct is `Function.Injective (fun h ↦ fun n ↦ rho ... h n)`.
  It ranges over every morphism T → J(U), with no IsIso assumption on h.

Dependency declarations read and used (including their recorded source docstrings):

- def-pur-conventions: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`; finite-field and coefficient datum conventions
  are reused in the explicit field and closure parameters, not redefined.
- def-weil-scheme-morphism-properties: a convention-only node with no declaration;
  the collected actual Mathlib instances are used as above.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its Smooth superclass).
- def-weil-completed-integral-coefficients:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, together with its publicly
  imported `completedIntegralCoefficientSheafUnrestricted` used for U's unit.
- sk-def-sp-coefficient-towers: `Sheaf.Paper.SmoothPurityCoefficientTowers`,
  `AlgebraicGeometry.ProEtale.spCoefficientTowers` and its ell-power quotient system.
- def-weil-derived-complete-integral-detailed: `Sheaf.Paper.SfIntegralConstructible`,
  `WeilConjectures.sfIntegralConstructibleCategory`.
- def-weil-finite-tor-amplitude: `Sheaf.Paper.FiniteTorAmplitudeSites` and the
  publicly imported integral finite-Tor predicate; tower finite-Tor domains use
  the same recorded notion.
- def-pur-integral-derived-operations:
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices`; the dependency construction
  realizes the specified completed operations; no alternative tensor is introduced.
- def-coefficient-twists-detailed:
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, publicly imported
  `WeilConjectures.integralTwistLine`, the signed completed root line.
- def-weil-compactifications-refinements:
  `WeilConjectures.Compactification.RefinementCategory`,
  `AlgebraicGeometry.Compactification` and its refinement interface;
  `SpTowerGamma.factorization j p` is the recorded compactification.
- def-weil-integral-rational-qbar-compact-support:
  `Sheaf.Paper.QcqsCompactSupportRealization`; the prescribed completed image is
  the one used by the recorded SpIntegralAdjunction.support interface.
- def-weil-exceptional-inverse-image:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`; its specified
  exceptional adjoint is accommodated by J and adjJ, and uniqueness fixes delta.
- det-sp-integral-adjunction-bijection: `Sheaf.Paper.IntegralAdjunctionBijection`,
  `SpIntegralAdjunction.Realization`, `right`, `reduce`, `support`, and the fields
  `fullyFaithfulX`, `rightComparison`, `adjunction`, `purity` of the realization.
- det-sp-unique-right-adjoint: `Mathlib.CategoryTheory.Adjunction.Unique`,
  `CategoryTheory.Adjunction.rightAdjointUniq` with its counit normalization.
- det-sp-tower-gamma: `Sheaf.Paper.SmoothPurityTowerGamma`,
  `SpTowerGamma.Purity.orientation` in the existing realization.
- det-sp-coefficient-towers-abelian:
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
  `SpCoefficientTowersAbelian` and its derived exact evaluation
  `spDerivedCoefficientEvaluation` (publicly imported by the adjunction framework).
- Proof imports: lem-sp-twisted-pullback-reduction-tower is already imported by
  IntegralAdjunctionBijection; the derived shifts and triangulation are the existing
  Mathlib structure. `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` imports
  the recorded degree-zero full and faithful single-functor instances for
  lem-weil-pbc-derived-single-fully-faithful.

Edge cases checked before finalizing: d=0 gives the unshifted coefficient unit;
index n=0 denotes ell^1 rather than ell^0; empty X or Y is not excluded; arbitrary
zero maps are included and need no inverses; ramification of E is not restricted;
no tensor change of coefficients is assumed flat merely because it is a quotient.
The small pro-etale site's object/morphism universes remain u+1/u; no equality of
these universes is imposed. Source and target identifications are genuine fixed-object
isomorphisms; they do not assert that arbitrary derived arrows are determined by levels.

Searches for an existing statement:

1. `msearch.py NN lem-pur-integral-orientation-reduction-injectivity leanfinder
   "Maps from an integral shifted Tate line to a smooth dualizing complex are detected
   by all finite reductions"`: 8 hits, consisting of generic derived-category
   t-structure, fraction and single-functor results (including
   DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective and
   DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE). None states this
   integral/tower geometric detection theorem.
2. The same wrapper with loogle query
   `DerivedCategory.singleFunctor, CategoryTheory.Adjunction.rightAdjointUniq`:
   OK, 0 hits. The two individual recorded Mathlib APIs were read directly.
3. Wrapper grep `orientation.*reduction|reduction.*orientation`: OK, 0 Mathlib hits.
   `rg` of that expression in lean/WeilConjectures and lean/Sheaf found the finite
   orientation/reduction modules and the existing tower-gamma dependency, none
   the integral Hom injectivity assertion. A direct grep for this item id in
   lean/WeilConjectures found no attachment. Further project searches for
   `Function.Injective`, finite detection and integral-unit/Tate-line names confirmed
   the actual recorded interfaces instead of a duplicate private category or line.

Source read: the latest blueprint tower-geometric gamma proof, clause (1), including
its degree-zero rank-one uniqueness argument; the source's construction, rather than
an arbitrary product of finite Hom groups, determines the reduction maps.
No STATEMENT-DISPUTED issue, statement correction, new node or dependency repair.

Validation: the final module is compiled through the prescribed scompile.py wrapper;
its theorem is the only sorry. The delivery dry run and push follow that compile.

## Second reading by NN

Independent clause-by-clause reading of the node against
`Sheaf.Paper.IntegralOrientationReductionInjectivity` (maintainer second reader,
2026-10-25; it replaces the earlier self-check, which was not an independent reading).

Objects and hypotheses:

- k, p, ell != p, E/Q_ell finite in a fixed closure: `D : FiniteFieldDatum`,
  `_hl : l ≠ D.p`, `[Fact l.Prime]`, `E` with `FiniteDimensional (Padic l) E`, `Ω`
  with `IsAlgClosure` and `_iE : E →ₐ Ω`. Same pattern as the landed
  `integral_adjunction_bijection`. Correct.
- X, Y separated finite type over k: `Over`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact` structure morphisms. f smooth separated of pure dimension d with a
  compactification: `f = j ≫ p`, `IsOpenImmersion j`, `IsProper p`, `IsOver`,
  `SmoothOfRelativeDimension d`, `d : ℕ`. The section instances `QuasiCompact (j ≫ p)`
  and `HasCompactification (j ≫ p)` are Props implied by the geometry
  (`HasCompactification` is a `Prop` class in WeilConjectures/Compactification/Defs.lean),
  so no extra assumption. Correct.
- R_W, 1_W, A_{n,W}, D^b_ctf, reductions r_W: `sfIntegralConstructibleCategory`,
  `SpReductionTower` (pinned: ordinary reduction by level identifications, universal
  left derived, K-flat computation), `SpIntegralAdjunction.reduce`. Index n is level n+1,
  so all n ≥ 1 occur. Working in the full constructible category gives the same Homs.
- P, G = Rf^! with adjunction and counit: `SpIntegralAdjunction.support … R.support_closed`
  and an arbitrary right adjoint `J` with `adjJ`. Quantifying over every right adjoint
  includes the node's G; the conclusion is invariant under the unique comparison. Correct.
- H and its comparisons: `realizedRight` = `SpIntegralAdjunction.right` with
  `R.rightComparison : H ⋙ r_X ≅ r_Y ⋙ G_•`, pinned by `right_normalization` (NX counit).
  δ: `R.adjunction.rightAdjointUniq adjJ`, the unique counit-preserving iso (Mathlib).
- T = 1_X(d)[2d], 1_Y: full-subcategory objects `T, U` with explicit isomorphisms
  `_hT` to `single 0 (integralTwistLine l E X d)⟦2d⟧` and `_hU` to `single 0` of the
  completed coefficient unit. Isomorphic representatives leave every clause unchanged.
- a_•: `R.purity.orientation` (det-sp-tower-gamma), inside the realization; used only
  in the proof, as in the node.
- β_M: `beta` = `R.fullyFaithfulX.homEquiv` followed by `R.rightComparison.app K`; this
  is the inverse of the last two bijections of `homChain` in the landed
  det-sp-integral-adjunction-bijection, so it is that bijection in the displayed
  direction Hom(M,HK) → Hom(r_X M, G_• r_Y K). λ = `targetComparison` = β(𝟙). Correct.
- ρ_n(h): `rho` = e_n(r_X(h ≫ δ⁻¹)) ≫ e_n(rightComparison) ≫ `lv.comparison n`, i.e.
  ordinary derived reduction of h (the evaluated reduction is pinned to derived scalar
  extension by `SpReductionTower.evaluation`), with target identified through δ⁻¹, the
  H reduction comparison and the finite exceptional comparison. Matches the node.

Conclusions:

1. β_T(δ⁻¹h) = λ ∘ r_X(δ⁻¹h): first conjunct, diagrammatic order
   `r_X.map (h ≫ δ.inv) ≫ targetComparison`. Correct direction.
2. e_n(β_T(δ⁻¹h)) = ρ_n(h): second conjunct, with the same finite target
   identification displayed on the left. Correct.
3. Injectivity of h ↦ (ρ_n(h))_n over all h : T → J U, no IsIso: third conjunct.

Truth: Hom(T, JU) ≅ Hom_{D(Tow)}(L[2d], L[2d]) = End_Tow(L) ⊂ ∏_n End(L_n) by the
orientation and source comparison, so injectivity holds; edge cases X or Y empty,
d = 0, h = 0, disconnected X all included. Universes: schemes, E, Ω in `Type u`,
pro-étale sites unchanged; no universe equality imposed beyond the dependency's.

Definitions `realizedRight`, `beta`, `delta`, `targetComparison`, `rho` are genuine
constructions with source and blueprint docstrings; the theorem docstring carries the
node's five steps; one `sorry`. The `lean.statement` equals the file verbatim; only the
item's `lean` record changed. Searches: the worker's three kinds of search are recorded;
I found no existing statement in lean/Sheaf or lean/WeilConjectures (grep for
orientation/reduction injectivity names). Advisory: `SpIntegralAdjunction.reduce/right/
support` are owned by def-sp-integral-reconstruction-comparison-data, reached through the
cited det-sp-integral-adjunction-bijection; some public imports of stmt_dep modules carry
no used declaration. Nothing changed in the Lean.
