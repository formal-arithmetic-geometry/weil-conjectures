## Worker report

The module `Sheaf.SixFunctors.RefinementProjectionCounit` states
`AlgebraicGeometry.ProEtale.AmbientProperOpen.refinementProjectionCounit` with proof `sorry`.
It adds two real constructions of the specified directed refinement comparison, one in each
coefficient setting. They belong to this node's displayed definition of C_u, are listed in
lean.declarations, and contain no postponed proofs or arbitrary choices. No statement correction,
new DAG node, or dependency repair is needed; only the item's lean field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The fixed algebraic closure of a finite field is `F : WeilConjectures.FiniteFieldDatum.{u}`.
  This is the dependency convention: F contains p, a finite field Fq of characteristic p,
  and k as its algebraic closure. The prime coefficient characteristic is `l : ℕ` with
  `[Fact l.Prime]`, and `_hl : l ≠ F.p` retains the prime-to-characteristic condition.
* The finite extension is `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. Its valuation ring and chosen uniformizer are exactly
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`, used
  by `Padic.coefficientExtensionRing`. The level is encoded as `n + 1` for `n : ℕ`, so
  every positive level, including level one, occurs. The existing ULift presentation
  puts the same finite ring in the small site's coefficient universe.
* `X Y : AmbientProperOpen.Spaces F` are finite-type k-schemes, bundled over Spec k.
  By definition their structure maps are locally of finite type and quasi-compact.
  Neither structure map has a separatedness requirement. `f : X ⟶ Y` is over k.
* `c₁ c₂ : Compactification f.hom.left` are the actual dependency's compactifications,
  not abstract operation data. Their fields are the open immersions c_a.i, proper
  maps c_a.g, and c_a.comm : f.hom.left = c_a.i ≫ c_a.g.
  Compactification.isSeparated and Compactification.locallyOfFiniteType already imply
  the separated and locally-finite-type parts of the stated hypothesis on f;
  `[QuasiCompact f.hom.left]` supplies its remaining finite-type condition.
  Thus no separatedness assumption on X or Y was introduced.
* `r : c₁.Refinement c₂` is the proper refinement u, with r.i_hom and r.hom_g
  precisely u j₁ = j₂ and p₂ u = p₁. Properness is the existing instance r.isProper.
  The proper maps equip the compactification schemes with their induced k-structures,
  which are finite type; their opens are quasi-compact by the recorded
  c_a.quasiCompact_openImmersion applied to f.
* F_a is the existing `ProperOpenShriek A c_a.i ⋙ ProperOpenPush A c_a.g` in the
  first setting, and `Operations.shriek l E o c_a.i ⋙ Operations.push l E o c_a.g`
  in the second. No new compact-support functor is chosen.
* `RefinementProjection.finiteComparison F A r K` is C_u(K). It first inserts
  S_id using `(ordinary F A).sId X`, then applies the intrinsic properOpenMate
  at (j₁,id,u,j₂), applies S_p₂, and follows by the adjunction-conjugate direct-image
  compositor and equality transport r.hom_g. Thus its direction is F₂ K → F₁ K.
  This is Gamma of the ambient-pasting node, which defines gamma by mateEquiv of
  this same properOpenAlpha. The finiteComparison code spells out precisely the
  sComp formula of that node for the ambient schemes of the compactifications.
* `IntegralSystemRealization.RefinementProjection.systemComparison l E F o z r K`
  has the identical direction and factors. Its identity normalization is
  z.canonicalBridge.push at id followed by SemilinearProperOpen.sId. Its Gamma is
  z.properOpen.gamma, identified with the intrinsic clopen proper-adjunction mate
  by the ambient-pasting and proper/open dependencies. Its compositor is
  z.compositors.pushComp, defined by conjugateIsoEquiv of z.compositors.pullComp.
  The only inverses are the canonical identity comparison; C_u and Gamma are never inverted.
* At a fixed finite level `K` and `L` quantify over `ProperOpenDerived` on the actual
  small pro-etale sites, with no boundedness, constructibility or Tor predicate.
  The projection is the existing `projectionMapOfCompactification (ModuleCat A) c_a`.
  Its read source definition is exactly pi_p followed by S_p(delta_j), and the
  canonical identification P_j P_p ≅ P_f via leftDerivedUpperStarCompactificationIso.
* The first conjunct says `PF_c₂ K L ≫ C_u(K tensor P_f L) =
  (C_u K tensor identity_L) ≫ PF_c₁ K L`. Lean's `≫` composes left to right,
  so this is exactly the displayed right-to-left-composition equation in the node.
  The tensor on C_u K is `(ProperOpenTensor A Y).map ...` evaluated at L.
* The second conjunct quantifies over the canonical operations presentations
  `o : Operations l E`, `z : Realizations l E F o` used by the already published
  proper/open tensor-compatibility theorem. These records normalize the actual
  simultaneous ringed-site operations; they impose no extra property on K or L.
  K,L are arbitrary `System l E` objects, the ordinary unbounded derived categories
  of semilinear quotient systems. The projection is the existing
  `compactificationProjection l E o z.compositors z.openComparisons c_a`.
  The two sides use the systemClosed tensor bifunctor, `pull l E f.hom.left`, and
  the systemComparison just constructed. The equality is an equality of system
  morphisms itself: no evaluation, total limit, or normalized-system predicate occurs.
* Joint naturality is retained by using the actual bifunctorial projection transformations
  and the canonical comparison (composites of natural identity comparisons, Gamma,
  compositors, and equality transports). The universal K,L equality equates their
  components; no independently chosen component maps are supplied.
* Every displayed composition or equality transport is explicit. Binary tensors here
  need no additional triple-tensor associator. There is no IsIso C_u assumption.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  Padic.finite_coefficientExtensionRing, importing CoefficientExtension and its actual
  valuation ring, uniformizer, quotient rings and quotient transitions.
* `def-weil-scheme-morphism-properties` is a convention node with no declaration:
  use Mathlib's QuasiCompact, IsProper, IsOpenImmersion, LocallyOfFiniteType and IsSeparated.
* `Sheaf.Paper.SemilinearDerivedSections`:
  WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData and
  semilinearDerivedSections; these supply the ordinary unbounded system meaning.
* `Sheaf.SixFunctors.AmbientProperOpenPasting`:
  Spaces, geometry, ordinary, Calculus.sId, Calculus.sComp, Calculus.gamma,
  ambientProperOpenPasting; read the system realization as well.
* `WeilConjectures.Compactification.RefinementCategory`:
  AlgebraicGeometry.Compactification.Refinement, its hom, i_hom, hom_g and isProper;
  Compactification itself comes from the public imported Defs module.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage and
  compactificationProjectionFromData; the finite realization already has the exact
  upstream `projectionMapOfCompactification` in
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection.
  This is reused rather than restating the notion carried by def-exchange-projection.
* `Sheaf.SixFunctors.OpenTensorNormalization`:
  SheafOfModules.openTensorNormalization, including its constant-finite specialization
  and ringed-system clauses. The finite delta is the canonical
  derivedOpenImmersionLowerShriekProjectionIso inverse in the existing projection.
* Proof imports: `Sheaf.SixFunctors.ProperOpenProjectionMate` gives
  AlgebraicGeometry.ProEtale.properOpenProjectionMate and the system version
  WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems; this is
  also the module recorded by lem-sf-proper-open-tensor-compatibility.
  `Sheaf.Paper.RingedProjectionTensorComposition` gives
  SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition.
* Existing system helpers are public dependencies of ambient pasting:
  IntegralSystemRealization.compactificationProjection, Compositors.pushComp,
  CanonicalBridge.push and SemilinearProperOpen.sId. Their full definitions were read.

Edge cases checked before writing:

* r=id: Gamma is the identity under the identity and conjugate compositors; the
  equation reduces to naturality under identity, with no cancellation assumption.
* K=0 or L=0: the two actual natural composites have the same zero-source/target
  behavior. Empty schemes and empty opens remain allowed by Spaces and Compactification.
* n=0 means A₁, retaining the first permitted level; no A₀ is used.
* Non-Cartesian refinement: for the fold Y ⊔ Y → Y and inclusion into one component,
  Gamma is a directed summand comparison. No Cartesian witness or inverse is requested.
* Nonseparated structure maps are admitted; only f's separatedness follows from its
  compactifications. Unbounded noncartesian coefficient systems and nonflat quotient
  transitions are allowed; the theorem never invokes normalizedness or finite evaluations.
* Universe u is explicit, as are all other binders. The coefficient ULift follows the
  published small pro-etale interface, and no equality of object and morphism universes
  is imposed. Both helpers have actual construction data.

Searches for existing statements (2026-10-24 UTC):

* msearch.py leanfinder, query: "Proper refinement of compactifications intertwines the
  counit defined projection formula maps on unbounded pro etale coefficient systems".
  Eight hits, chiefly CompHausLike.LocallyConstant counits, Condensed.profiniteSolidCounit,
  and LightProfinite transition projections: none states this result.
* msearch.py leansearch, query: "Proper refinement of compactifications commutes with
  the projection formula on unbounded derived sheaves". Eight hits on proper maps,
  affine-cover refinements, discrete quotients and sheaf restriction: no match.
* msearch.py loogle, query: "CategoryTheory.Adjunction.counit, CategoryTheory.MonoidalCategory".
  Twelve hits on monoidal adjunction/counit identities. These are generic ingredients,
  not the geometric/system refinement assertion.
* msearch.py grep, query: "refinement.*projection|projection.*refinement", subdirectory
  CategoryTheory: zero hits. Direct rg of the same expression in the source and Sheaf
  found the bounded finite refinement statements PfRefinementCompatibility and
  system_compactification_pf_substitution, and upstream etale refinement formulas.
  They require etale-origin/bounded/normalized domains, an inverse comparison, or a
  Cartesian square; they do not cover this ambient unbounded directed equality.
* Direct rg in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  refinementProjectionCounit and the two new full helper names: no declarations.
  grep of the node id in WeilConjectures likewise found no declaration.

The current literature/blueprint/latest composition/refinement sentence and the
prop-sf-pf-coherence compactification-independence paragraph were read. The node's
four-step agent expansion fixes the ambient version and supplies the proof docstring.
No STATEMENT-DISPUTED or node fault was found.

Validation: scompile.py compiled the module separately in sandbox and library modes;
its sole initial line-length warning was repaired. The final dry run and delivered
compile results are recorded by the delivery wrapper.

## Second reading by Q105

Reread the DAG statement against the completed file directly. This is the dispatcher's
single-worker reading; no independent worker was started, in accordance with the explicit
instruction not to start agents. The maintainer's independent review remains separate.
Checked every hypothesis and clause listed above against the source definitions, particularly:
Compactification.Refinement has no hidden Cartesian hypothesis; Spaces has no separated
structure-map condition; positive coefficient levels are n+1; the system category and tensor
are the actual simultaneous constructions. The left comparison inserts the inverse identity
normalization and the forward Gamma, then the forward conjugate compositor, whereas the existing
comparison-isomorphism results use the reverse direction and invert Gamma. Both conclusion
conjuncts have PF_c₂ followed by C_T on the left, and C_K tensor 1 followed by PF_c₁ on the right.
Existing finite and system PF definitions include P_j P_p → P_f with the correct orientation.
The componentwise equalities use only natural transformation factors and retain jointly natural
meaning. No mathematical mismatch was found; the one style warning at the system tensor line
was corrected. The existing DAG statement, dependency lists, proof, and all non-lean metadata
are unchanged.
