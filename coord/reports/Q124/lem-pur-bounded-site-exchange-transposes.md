## Worker report

Module: `Sheaf.Paper.BoundedSiteExchangeTransposes`. Main declaration:
`AlgebraicGeometry.ProEtale.boundedSiteExchangeTransposes`.
The node is unchanged outside `lean`. No new or repaired dependency nodes.
All five new theorem proofs are `sorry`; all definitions have real construction data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite field, coefficient prime, finite coefficient extension, positive level
  and actual quotient are `P : PurityFiniteSetting.{u}` and `P.Coefficient`.
  This is the existing quotient with its standard ULift, not a replacement ring.
- The four schemes and their finite-type structure maps are `X X' Y Y'`,
  `aX aY aX' aY'`, with `LocallyOfFiniteType` and `QuasiCompact` instances.
  The four equations `hf`, `_hf'`, `_hv`, `_hw` say all four maps are k-morphisms.
  There is no separatedness condition on a structure map.
- Separated finite-type compact-support morphisms are `f`, `f'`, with
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`. The primed properties follow
  from the pullback and the unprimed properties; retaining their instances permits
  the recorded bounded Hom interfaces to elaborate. They exclude no square.
- The arbitrary base-change morphism is `v`; `w` and `sq : IsPullback w f' f v`
  retain any chosen realization of the fiber product. In particular the literal
  fiber product in the node is included. No smoothness, properness or separatedness
  of `v` is required.
- The chosen compactifications are `c` and exactly `c.ofIsPullback sq`.
  The existential `d,hd` is a conclusion supplying a finite dimension certificate
  for the existing bounded-origin counit interface, not an extra hypothesis.
- Ordinary constant-module categories are the existing `Etale.DerivedCategoryModule`
  and `DerivedCategory (Sheaf (Scheme.ProEt.topology _) (ModuleCat P.Coefficient))`.
  `K : DerivedCategory.Plus ...` is the bounded-below input. `hHK`, `_hH'K`
  retain bounded-below exceptional images. Exact inverse images of these Plus
  objects are Plus; the right-adjoint intermediate used in `boundedSiteCounit`
  has its lower bound supplied by `boundedSiteRightAdjointPlus` in the dependency.
- `H`, `H'`, `adj`, `adj'` retain the chosen ordinary etale right adjoints to
  these very compactification functors. Quantifying over the choice is the usual
  formulation of 'choose the right adjoint'; such adjoints exist by the recorded
  ambient etale theorem. The pro-etale exceptional object is the exact composite
  `C_X H Rnu_Y,*`, visible in the main signature. No pro-etale ambient exceptional
  adjunction is introduced.
- `B` is the existing `compactSupportSiteComparison` with inverse orientation:
  its `.inv` is the node's forward B. `boundedSiteCounit` and
  `boundedSiteTranspose` use this exact proper-counit-mate/open comparison.
- `a=rho` is `boundedSiteRho`, the comparison image of H applied to the actual
  site-adjunction unit. `boundedExchangeRhoIso` merely packages that same map as
  an isomorphism using the existing unit-isomorphism theorem.
- `E_e` is `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
  `boundedExchangeEtaleMap` inserts its two existing Plus/unbounded compatibility
  isomorphisms; it does not change the proper/open exchange. `E_p` is the actual
  ambient `rightDerivedLowerShriekOfCompactificationBaseChangeMap`.
  The two initial `IsIso` conjuncts assert their required componentwise
  invertibility, including the pro-etale exceptional input with its rho-origin.
- The two equations on `qe` and `qp` are respectively
  `E_e ≫ qe = v_e^*(epsilon_e)` and `E_p ≫ qp = v_p^*(epsilon_p)`.
  Since the just-asserted exchanges are isomorphisms, these uniquely prescribe
  `qe=E_e^{-1} ≫ v_e^*epsilon_e` and `qp=E_p^{-1} ≫ v_p^*epsilon_p`.
  Thus they are an inverse-free characterization of the specified composites,
  with existence following from those isomorphisms, not free replacements for
  the canonical maps. `adj'.homEquiv qe` is exactly d_e.
- `boundedExchangeProTranspose` is d_p: precompose qp with F_p of its canonical
  origin isomorphism, apply the *specified* `boundedSiteTranspose`, and then
  precompose with the inverse origin isomorphism. `boundedSiteTranspose` is
  definitionally the forward map of the proven bounded-origin Hom equivalence.
  This evaluates the ordinary bounded Hom chain on a retained origin; it does
  not select a new Hom bijection or an arbitrary adjunction.
- `boundedExchangeSourceIso` is `kappa_w` followed by `w_p^*rho`.
  The main equality's left side is C(d_e), then rho at v_e^*K, then
  `C H' Rnu_Y',*(kappa_v)`. Its right side is this canonical source isomorphism
  followed by d_p. These are precisely the node's equality with all boundary
  pullback comparisons restored. No assertion that d_e or d_p is invertible.
- The coefficient-unit clause is `boundedExchangeDualizingNormalization`:
  it identifies the normalized inverse-exchange/counit adjunct with the named
  `Etale.dualizingComplexBaseChangeMap`, including the final
  `Etale.leftDerivedUpperStarUnitIso` (v^*A_Y to A_Y'). Combined with the main
  equality at the constant degree-zero bounded-below object, this is exactly
  the arrow in `finiteComparedBaseChangeClause` of the recorded co-smoothness
  definition. Global compactification choices in this auxiliary normalization
  are arbitrary `HasCompactification` instances and may be set to c and c'.
- The forward-mate clause is `boundedSiteExchangeDiagramMates`. Its `L` is an
  arbitrary D+ object on X'_et. The two helpers
  `boundedExchangeEtaleForwardMate` and `boundedExchangeProEtaleForwardMate`
  apply `mateEquiv` to the ACTUAL forward exchanges separately, using the
  existing `Etale.derivedUpperStarLowerStarAdjunctionPlus` for w and v on the
  etale site and `derivedUpperStarLowerStarAdjunction` for w and v on the
  pro-etale site. Thus these are two different pairs of specified adjunctions,
  on different sites. Their components have respective types
  `F_f^e Rw_e,* L → Rv_e,* F_f'^e L` and
  `F_f^p Rw_p,* C_X' L → Rv_p,* F_f'^p C_X' L`.
- Write `delta_g` for `boundedExchangeDirectImageComparison ... g`, whose
  data are exactly the included `fixedComparisonDirectImageMatePlus` and its
  existing comparison/derived-functor Plus compatibility maps. With Lean's
  left-to-right composition the forward-mate theorem says
  `C_Y(m_e) ≫ delta_v(F_f'^e L) ≫ Rv_p,*(B_f',L) =
   B_f,Rw_e,*L ≫ F_f^p(delta_w,L) ≫ m_p(C_X' L)`.
  The two `coherenceBoundaryComponent` factors are the already recorded
  proper-mate/open B, not replacement endpoint isomorphisms. The kappa squares
  occur through their specified right-adjoint mates `delta_w`, `delta_v`:
  `fixedComparisonDirectImageMatePlus_counit` identifies their left-adjoint
  comparisons with `fixedComparisonPullbackPlus`, the canonical kappa on D+.
  No alpha/beta squares, arbitrary adjunctions, component-specification
  hypotheses or assumed comparison equalities remain. This explicitly repairs
  H3 in the returned immutable head `1fd15ad7eaa6`.
- The finite-field and morphism hypotheses of this additional clause are the
  same as those of its exchange generator: the four `Over (Spec k)` objects
  are finite type, all four arrows are over k by construction, `f.left` is
  separated finite type, `sq` is Cartesian and `c` is chosen. No restriction
  is added on v. `L`, `Rw_e,* L` and `F_f'^e L` are all D+ objects by their
  actual functor codomains; the pro-etale mate is evaluated at `C_X' L`.
- The identity/pasting/refinement/restriction clauses are retained by
  `BoundedExchangeDiagram`: `inherited` includes the existing proper-refinement,
  compact-support-composition, identity and compatible-open diagrams;
  `exchange` and `inverseExchange` add arbitrary Cartesian squares and their
  actual inverse exchanges; `comp`, `push`, `pull`, `change` retain concatenation,
  horizontal/vertical whiskering and the compatible canonical endpoint changes.
  The etale and pro-etale maps are computed separately from the existing maps.
  `boundedSiteExchangeDiagramComparison` asserts comparison for every generated
  assembly and equality of the pro-etale assemblies whenever the etale
  pasting/refinement law identifies them. `boundedSiteExchangeDiagramTransposes`
  then compares the exceptional adjoints of these assemblies, and the repaired
  forward-mate theorem compares the two ordinary pullback/direct-image mates
  of each Cartesian exchange. Existing `mateEquiv_vcomp`, `mateEquiv_hcomp` and conjugation/identity laws identify those
  adjuncts with either pasted assembly of mates. Every etale intermediate is
  an explicit Plus object; no all-unbounded pro-etale assertion occurs.

Dependency declarations read and reused (including the exact recorded interfaces):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, the actual positive quotient and its ring instance.
- The scheme-properties dependency is a convention record; its named Mathlib
  `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsPullback`
  notions are used directly.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and its category; `WeilConjectures.Compactification.BaseChange`:
  `Compactification.ofIsPullback`, `.baseChange`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, ordinary derived categories.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`
  and its fixed-module realization; the node requests the ordinary constant-A
  fixed-module presentation, used by the recorded comparison and compact supports.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`.
- `Sheaf.Paper.CompactSupportSiteCoherence`: `compactSupportSiteCoherence`,
  `CompactSupportSiteBoundary`, `CompactSupportSiteDiagram`, the two map
  evaluators and their `coherence*Boundary` constructors; no private copies.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, whose finite component has
  the same transported ordinary derived functor. The bounded ordinary interface
  used here is the recorded `boundedSiteRho`/`boundedSiteHomEquiv` interface.
- `Sheaf.Paper.BoundedSiteAdjunctionTranspose`: `boundedSiteTranspose`,
  `boundedSiteRho`, `boundedSiteHomEquiv`, `boundedSiteCounit`,
  `boundedSiteAdjunctionTranspose`, its naturality and bounded intermediate.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparison_pullback_coherent`; its specific fixed-module derived
  comparison is the existing `leftDerivedUpperStarComparisonIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`;
  the proper/open pro-etale map in the matching finite-coefficient module.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `SuppliedExchangeProjection.ExchangeProjectionStage` and its compactification
  exchange, with the concrete finite-level maps above used here.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `IsCohomologicallySmoothFiniteCompared`, `finiteComparedBaseChangeClause`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `mateEquiv_counit`,
  `mateEquiv_vcomp`, `mateEquiv_hcomp`, conjugation and identity laws.
- Proof prerequisites: `Sheaf.Paper.CompactSupportExchangeTransport`
  (`compactSupport_exchange_transport`, its two endpoint paths and witness
  formula); `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
  (`Etale.compactSupportFiniteTorsion`); `Sheaf.Paper.PurityFiniteSettingComparisonHypotheses`
  (`PurityFiniteSetting.finite_setting_comparison_hypotheses`);
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
  (`fixedComparisonDirectImageMatePlus`, `fixedComparisonPullbackPlus`,
  `fixedComparisonDirectImageMatePlus_counit`); its module is now a public
  import because the forward-mate statement uses its canonical construction.
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`
  and `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` supply the two
  sites' respective existing derived pullback/direct-image adjunctions,
  with the etale Plus version used in the actual etale mate. Other dependencies are already
  public dependencies of these imported modules.

Sources opened: the current `literature/blueprint/latest` locality and composition
proofs, not an obsolete snapshot; Stacks `categories.tex`,
`lemma-transformation-between-functors-and-adjoints` (Tag 0B65).
The complete seven-step node proof is in the main theorem's docstring; the other
four statements have their own source and proof docstrings matching their clauses.
The repaired forward-mate docstring specifies the two pasted comparison squares,
which canonical comparisons are their mates, and which mate-pasting laws identify
the displayed boundary composites.

Edge cases checked before and after writing: identity squares and either empty
scheme, including the zero object; dimension bound zero on an empty compactification;
positive level 1; no absolute separatedness of X or Y; arbitrary finite-type v
including nonproper and nonseparated v; noninvertible exceptional mates remain
allowed. The diagram type is universe u+2, and coefficient modules are u+1 on the
actual small sites (objects u+1, morphisms u); no universe equality is imposed.
The unit identification direction was checked against the actual definition of
`dualizingComplexBaseChangeMap`. The two ordinary derived compact-support
compatibility maps were checked against their full signatures: an initial draft
omitted them, which the compiler detected and this delivery repairs explicitly.

Searches for an existing statement:

1. `msearch.py ... leanfinder "Etale proetale bounded site comparison compact support
   base change exchange exceptional adjoint transposes"`: eight results about
   condensed counits, Kan extensions, or etale topology, none this theorem.
2. `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_vcomp"`:
   `CategoryTheory.mateEquiv_vcomp`; it supplies the generic pasting tool only.
3. `msearch.py ... grep 'mateEquiv|baseChange.*[Tt]ranspos' CategoryTheory/Adjunction`:
   five entries in `Adjunction/Mates.lean`, the generic mate definition/counit
   formula, no scheme or site-comparison statement.
4. `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for the item id and bounded/exchange/transpose names: no exact statement.
   `FiniteSiteCounitProjectionTransport.finiteSiteExchangeTransposes` compares
   forward transposes, but does not state this node's actual inverse-exchange/
   counit equality; moreover its DAG proof depends on this item, so importing it
   here would reverse the dependency. `ExceptionalMateSiteComparison` uses
   absolutely separated schemes and a different Plus-adjoint interface, so it
   cannot state the nonseparated-domain result here. Neither is duplicated.
   Existing componentwise invertibility was found in the pro-etale upstream
   base-change module and used directly to construct inverse diagram generators.

Repair searches repeated on 2026-10-24:

- `msearch.py ... leanfinder "Comparison between etale and proetale mates of compact
  support base change under pullback direct image adjunctions"`: eight hits about
  general scheme-module pullbacks and their adjunctions, none this comparison.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_vcomp"`:
  found `mateEquiv_vcomp`, the generic pasting law.
- `msearch.py ... grep 'mateEquiv_(vcomp|hcomp)' CategoryTheory/Adjunction`:
  five matches in `Mathlib/CategoryTheory/Adjunction/Mates.lean`; no scheme/site
  comparison result.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`
  for the three new helper names and `boundedSiteExchangeDiagramMates`: no hit.
  The helpers only expose existing constructions/composites belonging to this
  node; they do not introduce a separate notion or duplicate a comparison.

No statement correction, disputed statement, or missing dependency interface.

## Second reading by Q124

This is a fresh self-check after the substantive H3 repair. The dispatcher expressly
forbids starting another agent, so this is not represented as an independent review
(the returned H11 advisory is acknowledged). Independent review is the maintainer's.

The saved packet's initial prescribed dry run passed (commit `8d701d67fec`), but
opening the saved Lean confirmed that H3 was still present: the old theorem applied
one mate equivalence to two squares in the same categories. It was not retained as
a mathematical repair. Removed that theorem and its generic category/universe
binders; replaced its statement with the cross-site boundary equation above.

Reread the original node and the final module against each clause. The main
inverse-exchange/counit equation, both invertibility assertions, the exact rho and
kappa source/target factors, the coefficient-unit normalization, and the generated
pasting/refinement/open-restriction diagrams are retained. The returned review
explicitly checked these sound; their mathematical content has not changed.
The repair adds exactly the previously missing ordinary-adjunction case of Step 6:
each mate is formed from its own actual exchange and own pullback/direct-image
adjunctions; the two sides are joined by the canonical direct-image mates and B.
This is not reducible to injectivity of a single mate equivalence. Its conclusion
can be used directly on arbitrary bounded-below L without supplying a square or
assuming any equality between its boundary composites.

For the new clause, tracked the common source
`C_Y(F_f^e(Rw_e,* L))` and target `Rv_p,*(F_f'^p(C_X' L))` through all three factors
on each side. Checked the direction of both delta maps against the full signature
of `fixedComparisonDirectImageMatePlus`; both go from comparison of etale direct
image to pro-etale direct image of comparison. Checked that the compatibility
factors go first from ambient comparison to Plus inclusion, then from Plus pro-etale
direct image to the ambient one. The kappa direction agrees with the counit formula
of `fixedComparisonDirectImageMatePlus_counit`. Neither v nor w is assumed separated:
the finite-type k-scheme hypotheses give the qcqs setting where that normalization
is available. No invertibility of the forward mates is asserted.

Identity v=w=id gives the same B boundary on both paths after the canonical
identity adjunction identifications. Empty X' and L=0 are allowed and add no
inhabitedness hypothesis. Arbitrary nonproper and nonseparated v remain included.
Etale direct images and compact supports preserve bounded-below inputs, as their
actual Plus codomains retain; no exceptional adjunction on ambient pro-etale inputs
has been introduced. The sole universe remains free u, with coefficient modules
in u+1 and the original small-site universes. All five theorem proofs are exactly
`sorry`; every helper has real construction data and a source/blueprint docstring.
All new helper declarations are listed in the owning node's lean record. Compared
sandbox and current main node: there are no differences outside `lean`.

Validation: the repaired module compiled cleanly with the prescribed scompile.py
in both sandbox and library module modes (16.0 s and 16.2 s). The final required
dry run and delivery follow with the updated record and report.
