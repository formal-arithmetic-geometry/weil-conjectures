## Worker report

The module `Sheaf.Paper.OrdinaryPullbackStratifiedModels` states the ordinary,
uncompleted transport of the *given* strata, charts and scalar complexes. It does
not merely conclude existence of another stratification or constructibility.
All theorem proofs are `sorry`; every definition has real construction data.
Every postponed theorem is an auxiliary clause of this item's statement, carries
this node's blueprint tag, and has its source and complete proof plan in its docstring.
All declarations are listed in `lean.declarations`.

Clause-by-clause correspondence:

* A prime ell and finite E/Q_ell: the explicit section binders `l`, `Fact l.Prime`,
  `E`, `Field E`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`. The valuation ring
  is the published `PbcIntegralRing l E`, the universe lift of the actual
  `Padic.coefficientExtensionIntegers l E`. Its uniformizer and quotient rings
  are the already fixed coefficient-extension constructions. Natural index n
  stands for the positive exponent n+1, so no level or case is removed.
* Any scheme map: `f : X ⟶ Y`, with no additional morphism assumptions.
  The original `ProEt` sites have objects in u+1 and morphisms in u. Sheaves,
  scalar modules and coefficients use u+1; these site universes are not identified.
* C_n, B and pi_n: `integralCoefficientSheafSystem`,
  `completedIntegralCoefficientSheafUnrestricted` and its `limit.π`.
  `coefficientMap` is the inverse-image adjoint of the existing
  `ordinaryIntegralDirectRingMap`, already uniquely fixed by every pi_n.
* Ordinary module and complex pullback and its derived counit: the published
  `ordinaryIntegralModulePull`, `ordinaryIntegralPullComplex`,
  `ordinaryIntegralDerivedPull` and `ordinaryIntegralPullComplexCounit`.
  None is completed pullback. The counit is the universal total-left-derived
  counit, conjugated by the cochain/homotopy quotient comparison isomorphisms.
* Noetherian X and Y: `[IsNoetherian X] [IsNoetherian Y]`. Mathlib's class
  extends `IsLocallyNoetherian` and `CompactSpace`, exactly locally noetherian
  plus quasi-compact. There is no dimension or ell-invertibility hypothesis.
* An arbitrary K in D(B_Y): `K : DerivedCategory (integralTowerModules l E Y)`.
  There is no boundedness, constructibility or completeness hypothesis on K.
* The given finite constructible locally closed stratification: the recorded
  `s : FiniteLocallyClosedStratification Y`, with `_hs` requiring constructibility
  of every `s.stratum i`. The recorded structure includes locally closed images,
  disjointness, covering, actual domain schemes and actual immersion arrows.
* The given pro-etale chart families: `A : Fin s.n → Type v` (independent index
  universe), `U i a : (s.domain i).ProEt`, and `_hcover` says the sieve generated
  by their arrows to the final site object is covering. Their arrows to the
  stratum are `(U i a).hom`; being objects of ProEt supplies weak etaleness.
* The *same* bounded finite-projective complexes: `L i a`, `_hfinite`,
  `_hprojective` and `_hbounded`. A finitely generated projective module is a
  retract of a finite free module. The zero module and zero complex are included.
  `modelModule` composes the existing constant-module sheafification with the
  existing scalar-extension functor along `scalar`; the latter is the existing
  constant-to-completion map with commutativity retained. `modelComplex` is its
  ordinary termwise application, not a selected perfect replacement.
* The supplied chart identifications: `e i a` is the isomorphism from ordinary
  immersion pullback followed by chart pullback to Q(modelComplex(L i a)).
  `immersionExact` states the former is exact restriction, including its ordinary
  computation counit. `weaklyEtaleExact` identifies the chart pullback with exact
  slice restriction, also with its counit. Thus this hypothesis has exactly the
  meanings of i_i^*K and restriction to U in the node.
* X_i, j_i and f_i: `pullback f (s.immersion i)`, `pullback.fst` and
  `pullback.snd`, respectively. The first conjunct produces `sX` and a bijection
  `b` with precisely the indices whose actual X_i is nonempty. It states the
  preimage formula for the stratum and gives a scheme isomorphism compatible
  with its immersion, in addition to constructibility. Therefore it deletes
  exactly empty X_i while retaining the original immersed schemes.
* V_ia and v_ia: `pullback (pullback.snd f (s.immersion i)) (U i a).hom`, and
  its `pullback.snd` to U. In the covering-family clause `proEtaleBaseChange`
  uses the variable-factor-first convention U times_S X_i. Fibre-product
  symmetry canonically identifies it with the X_i times_S U convention in
  `localComparison`, with the same two projections and covering property.
* Coefficient coherence of equal composites and finite projections:
  `coefficientMap_comp` states the completed composition equality under
  `inverseComp`, the canonical adjunction mate of fibre-product associativity,
  AND every finite projection equation. Substitute either pair of maps in
  f j_i = i_i f_i and transport along `pullback.condition`. No completed
  coefficient map is assumed invertible.
* The first displayed ordinary derived comparison is `derivedSquare f i`,
  with domain P_j(P_f K) and codomain P_fi(P_i K). `moduleSquare` is uniquely
  normalized on iterated adjunction-unit generators through `squareSite`.
  `complexSquare` applies it termwise. `derivedSquare_existsUnique` specifies
  the equation with both successive ordinary computation counits and Q of
  `complexSquare`. Thus it retains the canonical comparison, rather than
  postulating an unrelated derived isomorphism.
* The slice comparison is `localExchange`, the explicit composite of the
  stratum comparison with the square comparison for the chart U. Slice
  restriction is the ordinary pullback along its weakly etale chart arrow,
  as specified by `weaklyEtaleExact`. Apply P_v to the supplied e i a.
* The final model comparison and its normalization: `modelPullback_existsUnique`
  specifies a natural isomorphism on all scalar modules by its values on
  `modelSection` of 1 tensor x, followed by the ordinary adjunction-unit
  generator. These generators locally generate the scalar-extended module;
  B-linearity gives b tensor (a e_j) mapped to b c_v(a)e_j. Naturality in
  scalar module homomorphisms forces compatibility with the same splitting
  maps and idempotent matrices. `modelPullbackComplex` applies this identical
  natural comparison to every term, so it also commutes with every differential.
  `perfectModelPullback` states invertibility of the specified computation
  counit and of its composite with Q of the termwise comparison.
  `localComparison` is explicitly the composite of `localExchange`, P_v(e),
  this counit and Q of the same termwise comparison. The last conjunct of
  `ordinaryPullbackStratifiedModels` asserts that *this map* is invertible.
* The excluded assumptions at the end of the node are indeed absent: there
  is no completeness of P_fK, flatness/invertibility of c_f, separatedness,
  finite type, base field, or ell-invertibility binder.

Dependency declarations used (their full signatures/docstrings were read):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient ring,
  integer ring and fixed uniformizer constructions.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the existing quotient cone,
  coefficient system and completed ring with its projections.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`,
  `proEtaleSheafAdjunction` and the constant-ring maps.
* `Sheaf.Paper.RingedTopoiDerivedPullback`:
  `SheafOfModules.ringedTopoiDerivedPullback` (ordinary resolving-class counit).
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory`; `Sheaf.CategoryTheory.RingedSiteModules`:
  `ringedSiteModules`, transparently the actual `SheafOfModules` category.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the published tensor scalar extension.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (not a private copy).
* `Sheaf.Paper.SfImmersionCompletedPullbackComparison`:
  `ImmersionCompletedPullback.immersion_completed_pullback_comparison`,
  specifically its unconditional exact-ordinary-restriction clause.
* Added already-landed statement dependency
  `def-sf-ordinary-integral-pullback-construction`: its existing bindings in
  `Sheaf.Paper.OrdinaryCompletedIntegralPullback` supply the ordinary module
  functors and adjunction. The module also supplies their total derived
  functor and computation counit; its constructibility/completion theorem
  `ordinaryCompletedIntegralPullback` is never invoked. That downstream
  theorem is not added as a DAG prerequisite. This is the existing definition
  node's published physical module, not a second definition of pullback.
* Added already-landed statement dependency
  `def-weil-pbc-integral-stratified-perfect-models`:
  `Sheaf.Paper.IntegralStratifiedPerfectModels` reexports the existing constant
  module and scalar-extension components `adicLisseConstantModules`,
  `completedConstantExtension` and `completedConstantMapComplex`.
  Our `modelModule` merely composes those existing factors for the actual
  completed-integral coefficient presentation (the recorded integralConstantModule
  uses the canonically isomorphic pbcAdicCompletion presentation).
* Recorded proof dependency modules are imported as ordinary imports; Mathlib
  facts about constructible preimages, weakly etale/fpqc base change,
  limit projections and subcanonicity arrive through those modules. The
  sheaf-slice derived comparison has no recorded Lean declaration at this
  snapshot; the available ordinary composition/localization interfaces are
  imported, and the specific covering-chart comparison is spelled out by
  `localExchange`, `derivedSquare_existsUnique` and `weaklyEtaleExact`.

Sources checked directly: pdftotext of the supplied Bhatt--Scholze PDF,
Proposition 6.6.11 (local perfect values on finite strata) and Remark 6.8.15
(ordinary pullback and exact restriction for etale/closed immersions).
The eight-step reviewed DAG proof is reproduced in the main docstring.
No source correction or disputed statement is needed.

Edge cases checked before and during drafting: X empty (the subtype and sX may
both be empty), empty strata and empty chart families over an empty stratum;
K=0 and L=0; f the identity; open and closed immersions; rank-zero and rank-one
free models; a retract eR^r with a nontrivial idempotent; a two-term complex
with nonzero differential. Boundedness permits zero complexes; no nonempty
cover index or positive rank is assumed. No uniform bound across different
chart complexes has been added. The independent cover-index universe v is explicit.

Searches made:

* msearch leanfinder: "Ordinary derived pullback preserves stratified perfect
  local models over completed integral proetale coefficients"; 8 hits on
  etale objects, fibre products and base change, no match.
* msearch loogle: `"SheafOfModules.pullback", "Comp"`; 8 hits, including
  `SheafOfModules.pullbackComp` and `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`;
  ordinary underived comparisons only, no stratified derived statement.
* msearch grep: `pullbackObjFreeIso|pullbackComp`, subdirectory
  Algebra/Category/ModuleCat/Sheaf; 10 hits in PullbackContinuous/PullbackFree.
* Project rg: stratified/localModel/finiteProjective/perfectModel/modelComplex
  in Sheaf/Paper and WeilConjectures/ConstructibleSheaf; found the published
  integral stratified models, ordinary pullback construction and generic comparisons,
  all reused. Exact item-id grep in WeilConjectures found no statement.
* Name-clash rg for ordinaryPullbackStratifiedModels,
  WeilConjectures.OrdinaryStratifiedModels, modelPullback_existsUnique and
  weaklyEtaleExact in both source roots found no existing declaration.
* blueprint_refs.py search 'stratified perfect': zero blueprint matches.
  DAG searches located the existing ordinary-construction and constant-model
  definition nodes, so no new notion or definition node was created.

Validation: scompile.py compiled the complete module as both sandbox and named
library module with no warnings. Final validation and the prescribed deliver2.py
preflight are run on this same packet.

## Second reading by Q85

A separate clause-by-clause self-audit was done with the node and module open;
no independent-worker reading is claimed (the dispatched brief prohibits spawning
other agents and provides the maintainer's independent review on delivery).
The audit caught and repaired two typing faults: implicit scheme-to-type coercion
at `Nonempty (pullback ...)` needed an explicit `: Scheme.{u}` annotation, and
the inverse-image compositor needed the correct mate orientation. It also added
the explicit weakly-etale exactness/counit statement so the site-of-U convention
in the local formulas has its stated slice-restriction meaning.
The first displayed isomorphism, finite coefficient projections, actual chart
complexes, basis normalization and deletion of precisely empty strata were
checked against their explicit declarations above. All definitions have real
terms and every postponed theorem has the owning blueprint tag and proof plan.
