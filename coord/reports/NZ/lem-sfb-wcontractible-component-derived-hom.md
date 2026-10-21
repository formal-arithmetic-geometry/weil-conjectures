## Worker report

The module `Sheaf.Paper.WContractibleComponentDerivedHom` states Hemo–Richarz–Scholbach
2305.18131, Proposition 4.3(1), including equation (4.2) at U=W. I read the source PDF
through pdftotext: the component morphism (4.1), Proposition 4.3(1), and its proof through
the final sentence on internal Hom. The statement and proof of the DAG item are unchanged.
The only theorem in the module is
`AlgebraicGeometry.ProEtale.CondensedRing.wContractible_component_derived_hom`, with sorry.
Its docstring contains the nine proof steps of the node and the role of the cited tools.

Hypothesis and clause correspondence:

* An affine scheme W is `(W : Scheme.{u}) [IsAffine W]`.
* W-locality, strict henselianity of the closed local rings, and extremal disconnectedness
  of the component quotient are exactly `[IsWContractibleRing Γ(W, ⊤)]`. I read the
  recorded upstream class, its inherited w-strictly-local and w-local classes, and
  `WLocalSpace`. For affine W its global-section spectrum is canonically W.
* The site is the genuine `Scheme.ProEt.topology W`, objects in universe u+1 and arrows
  in u. The profinite slice has topology
  `(coherentTopology Profinite.{u}).over (affineComponentSpace W)`; the latter is the
  actual quotient by connected components, as in the recorded relative-site theorem.
* Arbitrary commutative condensed coefficients are
  `(Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]`. This admits condensed rings
  without a chosen topological presentation. Coefficients and modules have size u+1,
  and the published ordinary derived-category instances supply the compatible sizes.
* `profiniteCoefficient Λ.X (affineComponentSpace W)` is q_S^*Λ, using the existing
  `overPullback`. `condensedRingObj Λ.X W` is p_W^*Λ. The coefficient isomorphism α and
  the monoidal β with `α.hom.hom = β.hom.app Λ.X` specify p_W=q_Sπ_W at coefficients.
* `componentTests`, `componentInverse`, and `componentModules` are the previously
  published relative-test inverse image and its mapMod/comap coefficient transport.
  Continuity, braidedness, exactness and colimit preservation are existential
  conclusions of this theorem, not extra assumptions on W or Λ. The left adjoint
  preserves small colimits, in particular the countable sums defining total tensors.
* `componentModuleCanonicalMonoidal` merely exposes the already constructed ordinary
  `mapMod ⋙ Mod.comap α.inv.hom` monoidal structure by `inferInstanceAs`; it has real
  data and no postponed proof. It does not choose an auxiliary tensor product.
* `(componentModules Λ.X W α).mapDerivedCategory` is definitionally the recorded
  `componentDerived Λ.X W α`: it localizes the exact functor termwise. The theorem
  supplies its strong monoidal structure and
  `ComponentDerivedMonoidalNormalization Λ W α`. This predicate writes out the tensor
  and unit localization squares using `mapDerivedCategoryFactorsh`, the canonical
  ordinary `mapHomotopyCategory` oplax maps and the standard lax maps of Qh. Thus the
  derived structure is fixed by the usual representative construction, rather than
  being an unrelated existential monoidal structure. The ordinary braiding and its
  Koszul descent supply the symmetry of this normalized construction.
* Every K and L of the full unbounded `Evaluation.D` on the profinite slice is covered
  by the universal quantifier. `IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app L)`
  is exactly the evaluation-adjoint internal-Hom comparison. I read its defining mate
  and its evaluation formula in the upstream monoidal closed module. Internal Hom
  here is the existing closed internal-module derived Hom, not a new definition:
  the section-module equivalence identifies its relative tensor with the sectionwise
  tensor, and uniqueness of right adjoints identifies it with the recorded
  `derivedInternalHomOfUniverses` construction. The imported sections-model theorem's
  `tensorRightAdjoint_iso` is precisely this identification. The upstream pro-etale
  `derivedHom` and `derivedTensorHomAdjunction` use this same internal Hom.
* Full faithfulness is `Nonempty F.FullyFaithful` on that whole derived category.
* `componentGlobalSections` is only a transparent abbreviation of
  `preadditiveCoyoneda.obj (op (𝟙_ ...))`: ordinary global sections of internal modules.
  It carries no independent notion or construction of sheaves. θ is the natural
  ordinary section comparison, fixed on each f:1→M by `ε F ≫ F.map f`.
* γ is a natural isomorphism between the full right-derived global-sections functor
  and F followed by the target right-derived global sections, in the derived category
  of additive groups. Its hom is required to satisfy the right-derived unit square
  for θ, using the existing `mapDerivedCategoryCompRightDerivedFunctorUnit`. This is
  the canonical derived pullback map for every complex, and its natural transformation
  type enforces naturality. It is not merely an isomorphism of cohomology groups.
* There are no perfectness, dualizability, coefficient discreteness, boundedness or
  t-admissibility predicates anywhere in the theorem's hypotheses or K,L binders.

Dependencies used and inspected:

* `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing` and its
  inherited `IsWStrictlyLocalRing`, `IsWLocalRing`, `WLocalSpace` hierarchy.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.ComponentRelativeProfiniteSite`: `affineComponentSpace` and
  `component_relative_profinite_site`, including its universal property and factorization.
* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf` and `sectionModuleEquivalence`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  transparently `SheafOfModules`; the chosen internal presentation is related by the
  recorded equivalence, not by a private category.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, Q, and
  `HasDerivedCategory`; the size-convention node is a metatheoretic convention.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses` and its arbitrary-representative comparison.
* `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`: `profiniteCoefficient`,
  `componentTests`, `componentInverse`, `componentModules`, `componentDerived`,
  `Evaluation.D`; the module of the landed definition node is added to stmt_deps.
* `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`:
  `Functor.LaxMonoidal.ihomComparison`; its formula is the mate of pulled-back evaluation.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp`:
  `mapDerivedCategoryCompRightDerivedFunctorUnit`, the actual canonical unit square.

Every recorded, stated proof-dependency module is also imported privately. In particular
this retains the geometric inverse-image exactness, module adjunction, canonical derived
tensor pullback, affine component site, clopen partition, contractible sections, Stonean
cover, exact derived adjunction, weakly-etale localization, contractible basis, independent
universe Hom calculus, sections model, slice evaluation transpose, and ringed closed
derived structure. No proof dependency is omitted for a cycle.

Edge cases checked against the signatures and source: empty W (hence empty S), empty
profinite test objects, the zero condensed ring, K=0 or L=0, S a point, and complexes
unbounded in both directions. None is excluded by a Nonempty, nontriviality, truncation
or finiteness hypothesis. The site object and arrow universes remain u+1 and u.
The chosen coefficient size is exactly that of the published arbitrary condensed ring.

Searches actually run:

* `msearch.py ... leanfinder "On a w-contractible affine scheme component pullback preserves
  derived internal Hom and is fully faithful"`: eight irrelevant scheme pullback,
  adjunction and affine-limit hits, no statement match.
* `msearch.py ... loogle "CategoryTheory.Functor.Full, ihom"`: no hits; service reports
  unknown identifier ihom for that query. This is not evidence of absence of ihom.
* `msearch.py ... grep "(component|[Ww]Contractible).*(internalHom|ihom|[Dd]erived)"`:
  four generic derived-functor/closed-category hits, no component theorem.
* `rg` in both project trees for component/derived/internalHom patterns and the item id:
  found the existing component inverse-image data and lisse compatibility theorem;
  neither asserts closedness/full faithfulness on all unbounded objects. Reused the
  data module; no theorem or notion was copied.
* `rg` for `ihomComparison` found the exact canonical comparison in the upstream
  monoidal closed module and its evaluation identity. Reused it verbatim.
* `tools/blueprint_refs.py search 'component pullback'`: zero blueprint-node matches.
* Full new declaration names were searched in Sheaf, WeilConjectures and
  `dag/lean_names_upstream.json`; no conflicts found.

There are no new DAG nodes, dependency replacements, statement corrections or disputed
statements. The added stmt_dep `def-zl-condensed-lisse-evaluation-model` is already landed
and owns the component functor data used here.

Validation uses only scompile.py against the server's live published library. An initial
incorrect import spelling was corrected from the exact recorded node module. A later
instance error exposed that homotopy functor transport is only oplax monoidal in the
published API; the final normalization therefore writes the actual tensor and unit
squares explicitly using that canonical oplax structure. This preserves the specified
canonical maps and avoids introducing an arbitrary replacement.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
