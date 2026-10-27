# Q148 — lem-trf-roos-cone-compositor-descent

## Worker report

The module `Sheaf.CategoryTheory.RoosConeCompositorDescent` states
`CategoryTheory.roosConeCompositorDescent`. Its sole postponed theorem has proof
`sorry`; every helper has explicit data. The helpers package exactly the comparisons
and equations belonging to this node, not separate mathematical assumptions. No new
node, dependency repair, or statement correction is needed. Only the item's `lean`
field changes. The theorem docstring carries all eight proof steps.

The prior worker's “stale dispatch” diagnosis confused stages. Q118's 08:33 landing
was the stage-1 split, with no Lean record or module for this item. I read that split,
its review, and its dependency interfaces and carried out stage 2. The specified
CompactObject example is now a withdrawn module with no declarations, so the module
header follows the currently landed StrictRoosModel and StrictRoosComparison modules.
There is no repair note for this item in the supplied checkout.

Hypotheses, in node order:

- The arbitrary site is `{C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)`.
  The module universe is `max uC vC r`, so it contains both site universes without
  identifying them. `HasSheafify` and `WEqualsLocallyBijective` are the standard
  structural instances on this small site, not additional geometric restrictions.
- `R : Sheaf J RingCat.{max uC vC r}` and `_hcomm` say precisely that the ring sheaf
  is commutative on every object. `ringedSiteModules R` is the dependency's transparent
  abbreviation of Mathlib's actual `SheafOfModules`, with its usual abelian instance.
- `HasExactLimitsOfShape (Discrete ℕ)` is exact countable products in that category.
- `{S : Type uS} [Category.{vS} S] [Abelian S]` is the arbitrary abelian source.
  The three `HasDerivedCategory` assumptions supply the ordinary unbounded derived
  categories of S, Mod(R), and its strict tower category. Source and target derived
  morphism universes `wS` and `wA` are independent.
- `U : S ⥤ ℕᵒᵖ ⥤ ringedSiteModules R`, with `Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits`, is exactly the given additive exact functor.
- `F : Fin 3 → A ⥤ A` lists F0, F1, F2. Each is additive and exact by the same
  instances, and `PreservesLimitsOfShape (Discrete ℕ)` is countable-product
  preservation. `G : Fin 3 → S ⥤ S` has exactly additivity and exactness.
- `b i : U ⋙ tower (F i) ≅ G i ⋙ U` is the strict tower natural isomorphism. The
  abbreviation `tower` is actual postcomposition, not an unrelated tower functor.
- `d : F 0 ⋙ F 1 ≅ F 2`, `t : G 0 ⋙ G 1 ≅ G 2`, and `_hb` are the given compositors
  and their equation. Lean composition is left-to-right: `whiskerLeft (U.obj M)
  d.hom ≫ (b 2).hom.app M` equals F1 applied to b0, then b1 at G0 M, then U(t_M).
  Thus the equation is the node's displayed hypothesis in exactly its orientation.
- `RL`, `eta`, and `_hRL` specify total right-derived inverse limit, with its unit,
  using the same `IsRightDerivedFunctor` interface as strictRoosComparison and
  exactProductFunctorStrictLimit. This quantifies over a presentation of the
  specified right-derived functor, not an arbitrary functor. `total U RL` is exactly
  `U.mapDerivedCategory ⋙ RL`, the node's L.

Conclusion clauses, in node order:

- The products P, 1-s, H, and H(f) are `roosP`, `roosU`, `roosF`, and `roosF.map`
  from StrictRoosModel. `coordinates X p` is `(roosχ X p).hom`, then the biproduct
  swap, then `biprod.map (𝟙 _) (-𝟙 _)`. This is the precise change (old y,old z)
  to (old z,-old y), not a second cone construction.
- `HasSignedCoordinates` first states the full signed differential in degree p+1:
  the matrix is ((d,0),(1-s,-d)). Its second clause states the action of every strict
  chain map, with `roosPmap f` in degrees p+1 and p on the two diagonal entries.
  Thus all signed-coordinate conventions are explicitly retained.
- The existential `Comparisons.theta` is a natural isomorphism
  `Q ⋙ RL ≅ roosF ⋙ Q`. `HasNormalization` says that on **every** K-injective tower
  the actual `roosι` is a quasi-isomorphism, has coordinates `(iota,0)`, and its
  image equals `eta ≫ theta`. This fixes theta and hence its inverse's ordinary-limit
  normalization. General K-injectives need not have injective terms: refine to one
  with injective terms and transport along the homotopy equivalence, as explained
  in the theorem's proof docstring. No existence of K-injectives in S is assumed.
- `Comparisons.psi i M` is a chain isomorphism `Fi P(UM) ≅ P(UGiM)`.
  `HasProducts b` gives its entire chain projection equation, with `b` applied
  termwise using `NatIso.mapHomologicalComplex` and then evaluated at n. This is
  pr_n psi = b_n Fi(pr_n), for every n, not an unconstrained isomorphism.
- The second clause of `HasProducts` is strict chain naturality for every M → M'.
  Its third clause is exactly `Fi(s_UM) ≫ psi = psi ≫ s_UGiM`, where s is the
  recorded `towerProductShift`.
- `Comparisons.kappa i` is a **natural chain isomorphism**, rather than a family of
  arbitrary degreewise maps. `HasDiagonal` specifies both complete biproduct
  projections: the first uses psi in degree p+1, the second psi in degree p. These
  equations specify the two diagonal entries and force both off-diagonal entries
  to be zero under the canonical additive-biproduct comparison. They retain the
  shifted coordinate, including its sign.
- `Comparisons.a i` is a natural isomorphism `L ⋙ Fi_D ≅ Gi_D ⋙ L` on the entire
  unbounded derived category. `HasDerivedModel` is the node's conjugation formula
  written as its commuting square. `toRoos M` includes `RL.map` of U's exact-functor
  localization identification and then theta_UM. The left side is a_i,[M], then
  L of G's factorization, then theta_UGiM. The right side is Fi(toRoos M), then
  F's factorization, then Q(kappa). Cancelling the target identifications gives
  exactly theta_UGiM inverse ∘ [kappa] ∘ Fi(theta_UM). The normalized theta and
  projection-specified kappa force this to be the canonical exact-product comparison
  of exactProductFunctorStrictLimit, composed with RL(b), with the same ordinary
  limit/resolution normalization. It is not a newly chosen unnormalized iso.
- `HasCompositors` has three clauses. The first is d_P then psi2 = F1(psi0), then
  psi1 at G0 M, then P(U(t_M)). The second replaces P and psi by H and kappa.
  They are equalities of whole strict complex maps, not just cohomology maps.
  With `HasDiagonal` and the strict-map clause of `HasSignedCoordinates`, both
  off-diagonal entries vanish and the two diagonal entries agree. The third is
  the exact derived equation on every `M : DerivedCategory S`, using the canonical
  `Functor.mapDerivedCategoryCompNatIso d` and t. These upstream isomorphisms include
  the composite exact-functor localization comparisons and have the specified
  degreewise representatives. Naturality of a includes every derived morphism.
- There is no boundedness, constructibility, or faithfulness-of-evaluation binder.
  In particular neither strict nor derived coherence is replaced by a per-degree
  cohomology assertion.

Dependencies read and used:

- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`; read its full
  docstring and the Mathlib category and abelian-instance definitions.
- `lem-sf-exact-functor-derived-triangulated`: Mathlib's
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and the
  shift and triangulated instances in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `def-weil-strict-roos-model`: `Sheaf.CategoryTheory.StrictRoosModel`,
  `CategoryTheory.roosF`, and its actual helpers `roosP`, `roosU`, `roosχ`, `roosPmap`,
  `roosι`, `roosLimitFunctor`. The tower shift is the upstream
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism` construction.
- `lem-weil-strict-roos-comparison`: `Sheaf.CategoryTheory.StrictRoosComparison`,
  `CategoryTheory.strictRoosComparison`; read the entire signature, especially the
  naturality and K-injective unit-normalization clauses. It is a statement dependency
  and an input for the postponed proof, not an assumption that its conclusion holds.
- `lem-cbc-exact-product-functor-strict-limit`:
  `Sheaf.Paper.ExactProductFunctorStrictLimit`,
  `CategoryTheory.exactProductFunctorStrictLimit`; read the complete signed-cone,
  normalization, conjugation, beta/resolution, and augmentation clauses. They fix
  which canonical comparison is represented in `HasDerivedModel`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, `Q`
  from `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-inverse-system`: the category `ℕᵒᵖ ⥤ A` and natural transformations, as
  recorded by `Functor.ofOpSequence` and `NatTrans.ofOpSequence` in
  `Mathlib.CategoryTheory.Functor.OfSequence`. Reindex n as n+1 for positive indices.
- `lem-weil-tower-category-levelwise-abelian`: Mathlib's
  `CategoryTheory.Abelian.functorCategoryAbelian` and exact evaluation instances in
  `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`, exposed through the imports.
  No second abelian instance or copied tower category is introduced.
- The proof dependencies exact-derived-factorization and localization-universal-property
  have exact Mathlib matches `mapDerivedCategoryFactors` and `Localization.lift`,
  `liftNatIso`, `fullyFaithfulWhiskeringLeft`, `natTrans_ext`, already available through
  the dependency imports. Their recorded declarations and docstrings were read.
- The canonical compositors are reused from
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle`,
  `Functor.mapDerivedCategoryCompNatIso` (full definition and Q-component lemma read).
  The strict compositors use Mathlib's `Functor.mapHomologicalComplexCompIso`.

Searches performed through the prescribed wrapper:

- LeanFinder: “Composition coherence of product comparisons and diagonal signed Roos
  cone comparisons descending to derived inverse limits”: eight hits, including
  `prodComparison_comp`, product projection and sequential-product lemmas; none is
  this three-comparison theorem.
- Loogle: `CategoryTheory.Limits.piComparison,
  CategoryTheory.NatIso.mapHomologicalComplex`: zero hits for the combined query.
- Mathlib grep: `roos.*[Cc]ompositor|[Cc]ompositor.*[Rr]oos|piComparison.*comp` in
  CategoryTheory: eighteen hits, consisting of product comparison projection lemmas
  and their uses. Their signatures do not state the requested coherent comparisons.
- LeanSearch: “Composition coherence of the normalized product and shifted mapping
  cone model for the derived inverse limit”: eight hits including `mappingCone`,
  `mappingCone.map_δ`, mapping-cone homotopy equivalences and limit cone iso projections.
  These are ingredients, not the statement of this node.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for compositor/Roos/coherence and the
  exact node id: no exact statement exists. The specialized downstream
  `PointSystemPowerRoosCoherence` has point-power comparisons and compositor clauses;
  I read those definitions. Its extra finite-field and coefficient data prevent it
  from being an existing match for this arbitrary F/G/U statement. No module is
  duplicated. Searches also found the unsigned `strictRoosCoordinates` helper in
  StrictRoosDerivedLimitComparison; it uses the opposite coordinate order, so the
  signed coordinate change here is genuinely the node's specified conversion of
  `roosχ`, not a replacement definition of the cone.

Sources opened: Stacks sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok and
its proof; current main-20261015 trace-transport proof Step 1, Global powers; the
full node statements and recorded interfaces of every statement dependency; Q118's
stage-1 report. Q118's eight proof steps are retained unchanged.

Edge cases checked before and while writing:

- Zero U and zero complexes: products and both cone coordinates are zero; all map
  identities retain their typed meanings.
- Identity functors and identity b,d,t: the projection and diagonal requirements
  force the identity comparisons; derived conjugation cancels theta with its inverse.
- Nontrivial scalar d with b0=b1=1 and t=1: compatibility forces b2=d inverse.
  Thus d then psi2 gives the same identity as the right side, checking orientation.
- Constant towers with identity transitions and towers with zero transitions: both
  signed coordinates are present; the latter has 1-s=1, with the same differential.
- Unbounded M and arbitrary negative degrees: p ranges over ℤ; p+1 and p cover every
  adjacent pair. There is no totalization sum or boundedness assumption.
- All three indices 0,1,2 are the elements of Fin 3, not an arbitrary possibly empty
  index family. The tower itself is the full positive natural-number tower via the
  explicit shift n↦n+1; there is no truncation or dropped initial level.
- A general K-injective tower is allowed even without injective terms. Only the
  theorem docstring's proof reduces to the standard injective-term normalization.
- Distinct site, source and target universe sizes remain separate.

Validation: scompile.py compiled the complete module in module mode, both its sandbox
and library-path passes, without errors or non-sorry warnings. The first probe caught
an incorrect whiskering spelling in `_hb`; it was repaired to `Functor.whiskerLeft`.
The final version also states normalization on arbitrary K-injective towers. The
normal dry run and delivery below compile that final version again.

No statement dispute or node fault remains. The existing imports provide every
required notion. The only independent review is the maintainer's delivery review;
no second worker was started, as the dispatch brief expressly forbids it.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
