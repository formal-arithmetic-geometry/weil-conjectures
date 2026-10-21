## Worker report

Module: `Sheaf.AlgebraicGeometry.SemilinearAlphaPullback`.
Main declaration: `AlgebraicGeometry.ProEtale.VaryingRing.alpha_baseChange`.
The ordinary companion `moduleAlpha_baseChange` records the system-level equality
established by the node's proof before exact localization. Both theorem proofs
are `sorry`; no mathematical claim is proved in this delivery.

Hypothesis and clause correspondence:

- Arbitrary commutative ring sequence: `R : ℕ → CommRingCat.{u + 1}` and
  `φ : ∀ n : ℕ, R (n + 1) ⟶ R n`. Starting at zero is reindexing the displayed
  sequence starting at one. There is no flatness, finite-ring, surjectivity,
  boundedness, torsion, or cartesianness restriction on systems.
- Small pro-etale sites and strict semilinear categories: the recorded `Modules`
  and `Derived` of `VaryingRingOperations`, with coefficient universe `u + 1`
  and scheme universe `u`. These use the actual sequence-site ring/module data
  of `SemilinearDerivedSections`, not a new tower category.
- Node notation `P_v = D(v* bullet)` is dependency notation `G R φ v`.
  `J_j` is `J R φ j`. The dependency's `P` is proper direct image and does
  not occur in either conclusion. No mate has been taken.
- The original square has objects `U V W Z`, arrows `k i r p`, and
  `w : k ≫ p = r ≫ i`. The two `[IsOpenImmersion]` and `[QuasiCompact]`
  instances encode precisely the two quasi-compact open immersions, and
  `[IsProper r] [IsProper p]` encode properness.
- Base change by `h : Z₁ ⟶ Z`: objects `U₁ V₁ W₁ Z₁`, projections `a c d`,
  and arrows `k₁ i₁ r₁ p₁`. The four face equalities are `wk wi wp wr`;
  their cartesianness witnesses are `sk si sp sr`. The top square is `w₁`.
  This uses arbitrary models of the specified fibre products, as permitted
  by `IsPullback`, rather than restricting to one representative.
- The top-square open/quasi-compact/proper instances spell out properties
  inherited by base change. They exclude no base change: they follow from
  `sk si sp sr` and the original properties. They are explicit for elaborating
  the dependency's `alpha` interface. No cartesianness of Q or Q₁ is assumed.
- For every `M : Derived R φ W`, the left side is exactly the first displayed
  path: `(G p₁).map beta.app M`, then `alpha Q₁` at `(G c).obj M`.
- The right side is the second displayed path: the square compositor for
  `wp`, pullback by `a` of `alpha Q`, beta for `sk` at `(G r).obj M`, then
  extension by `k₁` of the inverse square compositor for `wr`.
- `alphaPullbackBeta` is the exact localization of the dependency's
  `moduleBeta`, conjugated only by `mapDerivedCategoryCompIso`.
  `alphaPullbackSquareG` likewise localizes the recorded `moduleSquareG`,
  which uses the specified unit-preserving `moduleGComp`. Thus neither helper
  selects an arbitrary comparison. Open compositors occur inside the existing
  `moduleAlpha` and `alpha` constructions, unchanged.
- Equality at every M is equality of the displayed natural transformations
  by natural-transformation extensionality. The ordinary companion states
  the identical formula with `pull`, `extension`, `moduleAlpha`, `moduleBeta`,
  and `moduleSquareG`. Exact localization, rather than derived evaluation,
  gives the main conclusion. Both docstrings contain all seven proof steps.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`:
  `AlgebraicGeometry.ProEtale.VaryingRing.Modules`, `Derived`, `pull`,
  `extension`, `G`, `J`, `moduleGComp`, `gComp`, `moduleJComp`, `jComp`.
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`:
  `AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG`, `moduleBeta`,
  `modulePi`, `moduleAlpha`, `alpha`. The full signatures and the normalization
  docstrings were read. The recorded main declaration `gamma` is a mate;
  the item correctly uses its module's underlying alpha instead.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`;
  cartesian faces are expressed by `CategoryTheory.IsPullback`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node,
  with no declaration. Its named notions are Mathlib's `IsOpenImmersion`,
  `QuasiCompact`, and `IsProper`.
- Proof imports include `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
  (clopen square lift; its `CartesianNormalization.alpha_baseChange` only
  handles one constant coefficient ring), `Sheaf.Paper.SemilinearDerivedSections`
  (`WeilConjectures.SemilinearSections.semilinearDerivedSections`),
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
  (`SheafOfModules.localizedSystemExact`),
  `Sheaf.CategoryTheory.RingedSiteModules`
  (`CategoryTheory.ringedSiteModules`), the Mathlib proper/open/quasi-compact
  base-change modules, `Mathlib.AlgebraicGeometry.Sites.Proetale`
  (`AlgebraicGeometry.Scheme.ProEt`), and
  `Mathlib.CategoryTheory.Localization.Predicate`
  (`CategoryTheory.Localization.liftNatTrans`, `comp_liftNatTrans`, `natTrans_ext`).

Source read: `literature/stacks-project/more-etale.tex`,
`lemma-shriek-proper-and-open-base-change` (Tag 0F7F), including its square,
hypotheses, derived comparison diagram and proof. Its fixed-ring etale mate
is the source analogy, not a claim that Stacks already states the varying-ring
alpha theorem; the node explicitly credits the latter extension to an agent.

Edge cases checked: zero coefficient rings, non-flat transition maps, zero
systems, empty schemes/empty opens, identity base changes, empty selected
clopen component, and non-cartesian Q. None is excluded by the binders. The
argument works for all unbounded complexes and uses no assertion that derived
coefficient evaluations are faithful. The four cartesian faces specify base
change; they do not assert the original square is cartesian.

Searches for an existing statement:

- `msearch.py ... leanfinder "Pullback cube compatibility of the clopen alpha
  transformation for semilinear inverse systems of sheaves of modules"`:
  eight hits, generic module-pullback/free-module and gluing declarations;
  no varying-ring alpha cube.
- `msearch.py ... loogle "SheafOfModules.pullback, SheafOfModules.pushforward"`:
  twelve generic module-pullback, adjunction and compositor hits; no match.
- `msearch.py ... grep "alpha_baseChange|moduleAlpha.*pullback|semilinear.*alpha"`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, alpha pullback/base-change
  names and semilinear-alpha patterns: no exact varying-ring theorem.
  `StrictTowerProperOpenCalculus` has a constant-ring tower alpha cube, which
  was read and cannot replace this statement for arbitrary varying rings.
  `VaryingRingProperOpenPasting` has vertical/horizontal pasting, not this cube.
- The two new helper names and both full theorem names were checked against
  the source tree and upstream declaration index; no duplicate was found.

Validation: prescribed `scompile.py Q03 lem-sf-semilinear-alpha-pullback`
compiled this module in both sandbox and library module modes cleanly. Final
preflight/delivery results are reported by the prescribed delivery wrapper.
No statement correction, new node, or dependency repair is required.

## Second reading by Q03

Author's separate second pass, with the node and complete module open:
checked the eight scheme vertices, twelve arrows, six square equalities,
four cartesian faces, all open/quasi-compact/proper properties, and both
four-factor/two-factor paths. The source of the first square comparison is
`G h ⋙ G p₁` and its target is `G p ⋙ G a`; the last square comparison is
used inversely to turn `G r ⋙ G d` into `G c ⋙ G r₁`. This verifies the two
otherwise easy-to-reverse orientations. Every object M is arbitrary.
The helper definitions localize exactly the recorded ordinary maps. The
ordinary theorem retains the pre-localization assertion; the main theorem
uses the existing localized alpha, with no proper direct-image mate.
No mismatch or statement change was found. This is an author audit;
the independent maintainer review described in the dispatch brief remains
separate, and no second agent was started.
