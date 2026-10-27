## Worker report

The module `Sheaf.Paper.ComponentPushforwardExactUnit` states
`AlgebraicGeometry.Scheme.ProEt.component_pushforward_exact_unit`. The theorem has one
`sorry`; no theorem is proved. Four helper declarations give real coefficient and
adjunction data: `componentUnitSliceRing`, `componentUnitSchemeRing`,
`componentUnitRingMap`, and `componentUnitDirectEvaluation`. The last is an identity
natural isomorphism, not a postponed existence construction. No statement correction,
new node, dependency replacement, or disputed statement is needed.

Source read: Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*, the
paragraph constructing (4.1), Proposition 4.3(1), and its proof through (4.2),
especially the paragraph beginning “As X times over pi_0 X S”. The source PDF was
read with `pdftotext -layout`. Also read Bhatt--Scholze Lemmas 2.2.8 and 2.4.8,
and Stacks `sites-modules.tex`, `lemma-adjoint-pullback-pushforward-modules`
(Tag 03D7), including its tensor/restriction proof. The node's ordinary module assertions implement the
abelian argument that this proof invokes. The theorem docstring carries all seven
accepted DAG proof steps, including the normalized Kan unit and the descent argument.

Hypothesis and clause correspondence:

- The affine scheme is `W : Scheme.{u}` with `[IsAffine W]`. Its w-contractibility
  is `[IsWContractibleRing Γ(W, ⊤)]`, exactly the recorded ring predicate applied
  to the global ring of this affine scheme. No choice of coordinates or affine
  presentation restricts W.
- `componentProfinite W` is the actual connected-component quotient with quotient
  topology. This is definitionally the same profinite object as
  `AlgebraicGeometry.ProEtale.affineComponentSpace W` in the relative-site node.
  The site is `(coherentTopology Profinite.{u}).over (componentProfinite W)`;
  its covers are the required finite jointly surjective families.
- `Λ : Profinite.CondensedRing.{u}` and `[IsCommMonObj Λ.X]` give an arbitrary
  commutative condensed ring, with no topological presentation or discrete-ring
  hypothesis. `InternalAbelianSheafModule.sectionRingSheaf` reconstructs its
  actual section rings, restrictions, multiplication and unit.
- `componentUnitSliceRing W Λ` is that ring sheaf restricted to the profinite
  slice using `.over`; this is q_S^*Λ. `componentUnitSchemeRing W Λ` is the
  section-ring presentation of `ProEtale.condensedRingObj Λ.X W`, hence the
  actual p_W^*Λ. `L`, `adj`, and `c` supply inverse image on rings with its
  adjunction to actual restriction and the identification L(Λ_S) ≅ p_W^*Λ.
  An adjoint with its unit is determined by the right adjoint up to the unique
  adjunction-compatible isomorphism; this is not an arbitrary substitute map.
- The site functor is the existing `genericComponentFunctor W`, characterized
  by the fibre ringed space in `affine_component_site_projection`.
  Its set geometric morphism is the existing `genericComponentProjection W`.
  The relative-site dependency supplies p_W ≅ q_S π_W. These constructions
  are reused, not redefined by a private functor with weaker properties.
- Every `E : Over (componentProfinite W)` with `[ExtremallyDisconnected E.left]`
  occurs in the first conjunct. The first two clauses say its test scheme is
  affine and has a w-contractible global ring (`Nonempty` packages the
  Type-valued `IsWContractibleRing` structure).
- The next clause is `∀ x, IsIso (...hom.stalkMap x)`, the claimed isomorphisms
  on local rings from W. The following biconditional says x is closed exactly
  when its image in W is closed. Under the dependency's canonical fibre-space
  homeomorphism, this is exactly `(W_E)^c = W^c ×_S E`, including the topology
  inherited from that fibre space. The final geometric clause gives a
  homeomorphism `ConnectedComponents W_E ≃ₜ E.left`, with its value on every
  quotient point equal to `genericComponentCoordinates W E x`; it is the
  specified component identification, not an unspecified homeomorphism.
- `componentUnitRingMap` is `adj.unit.app Λ_S` followed by direct image of
  `c.hom`. `SheafOfModules.pushforward` therefore is G_W with exactly the
  scalar action induced by the unit, not merely a functor on underlying sets.
  `componentUnitDirectEvaluation` identifies G_W followed by evaluation at E
  with evaluation at W_E followed by restriction of scalars along this ring
  unit. It is `Iso.refl _`, so `(G_W N)(E) = N(W_E)` is literal on sections,
  restriction maps, and module morphisms, with the stated scalar action.
- The existential right-adjoint instance records the existence of module
  pullback. `SheafOfModules.pullback` is its ordinary left adjoint;
  `pullbackPushforwardAdjunction` is the actual module adjunction F_W ⊣ G_W.
  These are Mathlib's ringed-site functors, whose pullback is presheaf module
  pullback followed by module sheafification, not an arbitrary F_W.
- `G_W.Additive`, `PreservesFiniteLimits G_W`, and
  `PreservesFiniteColimits G_W` express exactness on module sheaves.
- `∀ M, IsIso (...unit.app M)` is invertibility of the ordinary adjunction
  unit for every Λ_S-module sheaf M.
- `e E` is a natural isomorphism of ModuleCat-valued evaluation functors
  `F_W ⋙ G_W ⋙ evaluation_E ≅ evaluation_E`, giving the second evaluation
  identity `(G_W F_W M)(E) = M(E)` linearly over Λ_S(E). Naturality in M is
  part of the natural isomorphism type. The final equation imposes naturality
  in E for every arrow between extremally disconnected tests. The preceding
  equation maps the actual module unit by evaluation and composes with `e E`;
  its result is `𝟙 _`, precisely η_M(E) = id under this identification.
- The mention of ordinary unbounded derived categories introduces notation
  but no additional derived assertion in this node. The module retains the
  recorded `DerivedCategory.Basic` import; its conclusions are all the
  ordinary assertions required before passing to unbounded derived categories.

Dependency declarations used (the modules were opened and signatures and
relevant docstrings read):

- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`;
  its inherited `IsWStrictlyLocalRing`/`IsWLocalRing` and `WLocalSpace` were
  read in their owning source files.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  The source preserves object universe u+1 and morphism universe u.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`:
  `AlgebraicGeometry.ProEtale.component_relative_profinite_site` and
  `affineComponentSpace`.
- `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection`:
  `componentProfinite`, `ComponentSiteEvaluation`,
  `affine_component_site_projection`, including its geometric and
  split-cover evaluation clauses.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` (ordinary unbounded notation, no derived claim added).
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`; read its tensor
  formula and normalized transpose. It is retained as a proof import. For the
  statement, Mathlib's `SheafOfModules.pushforward`, `pullback`, and
  `pullbackPushforwardAdjunction` provide the same canonical construction with
  independent site and coefficient universes; no equal-universe restriction
  from that general theorem is imposed.
- Existing added statement dependencies:
  `def-zl-generic-component-data`, with module
  `Sheaf.AlgebraicGeometry.GenericComponentData`, supplies
  `genericComponentFunctor`, `genericComponentCoordinates`,
  `genericComponentRingPush`, and its continuity instance;
  `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, with module
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, supplies
  `InternalAbelianSheafModule.sectionRingSheaf`;
  `sk-def-sfb-pulled-back-coefficients`, with module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, supplies
  `ProEtale.condensedRingObj` and its commutativity instance. These nodes
  already exist and have usable landed Lean records. Only their IDs are added
  to the item's stmt_deps.
- The named proof-dependency modules are imported, including exact contractible
  sections, Stonean covers, clopen partitions, w-local components, geometric
  module transport, module colimits, finite coproduct evaluation, and stalk
  isomorphism lifting. For the three Mathlib-only proof nodes, the recorded
  matches are in `Sites.Pullback`, `ModuleCat.Sheaf.Limits`, and `Sites.EpiMono`;
  these imports and the actual declarations were checked directly.

Edge cases checked before writing: E empty gives W_E empty by the existing
fibre-space construction; `ConnectedComponents` and its identified E are empty,
local-ring claims are vacuous, and sheaf module sections are zero by the empty
cover. W empty gives S empty, with only empty tests and zero module categories.
Neither `[Nonempty W]` nor `[Nonempty E.left]` is present. The zero coefficient
ring, zero module, infinite condensed section rings, and arbitrary module sheaves
are included. A strictly henselian local W with S a point recovers the familiar
Stonean-test calculation. Coefficients and module sections use u+1 above scheme
universe u, with no equality between site object and morphism universes.

Searches actually run:

- `msearch.py ... leanfinder`: “The direct image of the component morphism of a
  weakly contractible affine scheme is exact on module sheaves and its
  adjunction unit is an isomorphism”. Eight hits, headed by affine-scheme
  global sections/spectrum equivalences; none is this pro-etale component result.
- `msearch.py ... loogle`: `"Sheaf", "unit", "IsIso"`. Twelve hits include
  sheafification counits, dense subsites, pullback of the coefficient unit,
  and discrete condensed adjunctions. None states exact component direct image
  and the normalized ordinary unit for general condensed module sheaves.
- `msearch.py ... grep`: `component.*(pushforward|adjunction|unit)|[wW]Contractible`
  in CategoryTheory. Twenty-five generic unit-component hits; no exact match.
- `rg` of `lean/WeilConjectures` for the item ID returned no match. Searches of
  `lean/WeilConjectures` and `lean/Sheaf` for component pushforward, exactness,
  unit, and component-module interfaces found the recorded constructions and
  sibling `ComponentPullbackUnboundedEvaluation`. That sibling calculates
  inverse-image evaluation on arbitrary w-contractible affine tests; it does
  not assert exactness of G_W or invertibility of the ordinary module unit.
  No existing declaration says the whole assigned node.

Validation: the final `scompile.py N6 lem-sfb-component-pushforward-exact-unit`
run passed both the sandbox-name and actual-library-name compiles, with no errors
and no warnings (reported times 53.3 s and 10.1 s, both within the prescribed
per-file limit). Static inspection checked the 100-character line limit, the
verbatim `lean.statement` signature, all five listed declarations, the single
expected theorem `sorry`, and that only `lean` and `stmt_deps` differ in the node.
The prescribed delivery dry run follows. All writes are confined to this item's sandbox;
only the prescribed compilation and delivery wrappers manage external bookkeeping.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
