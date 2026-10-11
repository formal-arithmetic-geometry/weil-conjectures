## Worker report

The module states the natural global-derived-Hom pullback/direct-image adjunction,
its pullback-counit factorization and its H^0 adjunction bijection. The theorem's
proof is `sorry`, as required for stage 2. The hypothesis-by-hypothesis and
clause-by-clause correspondence is listed in the second reading below.
Dependencies used: `Sheaf.AlgebraicGeometry.GlobalDerivedHom`
(`AlgebraicGeometry.schemeGlobalDerivedHom`, `schemeDerivedGlobalSections`),
`Sheaf.AlgebraicGeometry.DerivedPullback` (`AlgebraicGeometry.derivedPullback`),
`Sheaf.AlgebraicGeometry.DerivedCategory` (`AlgebraicGeometry.schemeDerivedCategory`),
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
(`AlgebraicGeometry.schemeDerivedDirectImage`), and
`Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison`
(`AlgebraicGeometry.IsCanonicalPullbackTensorComparison`). The underlying scheme
is Mathlib's `AlgebraicGeometry.Scheme`. The proof route uses the recorded
`AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction` from
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`.

Edge cases checked: arbitrary schemes and morphisms, arbitrary derived objects, and zero objects are included by unrestricted quantification. Searches with `msearch.py` and `rg` found no existing project declaration for this node.

## Earlier second reading (a previous round; superseded)

I read the node copy and the repository node, the statement-dependency records,
and the recorded Lean declarations. The original theorem was a self-isomorphism of
`RHom_S(M,Rg_*E)`. It did not state the node's adjunction, despite the earlier report.
The node's mathematical statement is sound and has not been changed.

Source reading: the local repository omits the Stacks .tex files, so I fetched
`cohomology.tex` from the Stacks source into this item's scratchpad. I read
`lemma-adjoint` (079W), `remark-prepare-fancy-base-change` (08I3),
`section-global-RHom` (0B6A), `lemma-pullback-tensor-product` (079U), and
`definition-derived-tor` (06YH), including the preceding construction. These places
introduce arbitrary ringed spaces and unbounded complexes. They assume no
Noetherian, finiteness, quasi-coherence, flatness, separatedness or characteristic
hypothesis. Source links: [079W](https://stacks.math.columbia.edu/tag/079W),
[08I3](https://stacks.math.columbia.edu/tag/08I3),
[0B6A](https://stacks.math.columbia.edu/tag/0B6A),
[06YH](https://stacks.math.columbia.edu/tag/06YH).

The node's objects, hypotheses and conclusion clauses, with the Lean rendering:

1. Schemes S,T and an arbitrary morphism g:T→S: `{T S : Scheme.{u}}`, `(g : T ⟶ S)`.
   This uses `AlgebraicGeometry.Scheme` and its actual category of scheme morphisms.
   Verdict: same objects; no geometric hypothesis added.
2. D(O_S) and D(O_T), with unbounded derived pullback and direct image:
   `schemeDerivedCategory S/T`, `derivedPullback g`, `schemeDerivedDirectImage g`.
   I opened DerivedCategory, DerivedPullback and SchemeDerivedDirectImage.
   Their carriers are the shared `SheafOfModules (moduleRings ...)`, not the separate
   category instance on the abbreviation `Scheme.Modules`. DerivedPullback uses
   termwise inverse image and derived tensor change of rings; direct image is the
   right-derived module direct image of the underlying ringed-space morphism.
   Verdict: the recorded constructions, with no replacement definition or boundedness.
3. Global RHom in D(Gamma(S,O_S)) and D(Gamma(T,O_T)):
   `schemeGlobalDerivedHom S/T`. I opened GlobalDerivedHom: it is the shared
   `derivedInternalHom` followed by `schemeDerivedGlobalSections`, which is the
   unbounded right derived functor of ring-valued global sections and includes its
   point-space and K-injective comparison statements. Verdict: actual complexes of
   modules over global sections, not only abelian groups or Hom sets.
4. The T complex regarded in D(Gamma(S,O_S)):
   `(ModuleCat.restrictScalars g.appTop.hom).mapDerivedCategory`, with both scalar
   rings explicitly specified. Its module restriction functor is exact, so
   `mapDerivedCategory` is the correct derived scalar restriction. Verdict: the
   precise structure-sheaf map, in the required direction, with independent global
   derived-category universes `wAS` and `wAT`.
5. Every M in D(O_S) and E in D(O_T), with a natural isomorphism
   RHom_S(M,Rg_*E) ≅ restricted RHom_T(Lg^*M,E): witness `i` is a natural isomorphism
   of functors on D(O_S)^op × D(O_T). Its components are exactly these objects.
   Verdict: both variables unrestricted, naturality in both built into NatIso;
   the original self-isomorphism and objectwise Nonempty conclusion are removed.
6. H^0 is the adjunction bijection phi↦epsilon_E∘Lg^*(phi): `hS` and `hT` are additive
   H^0/derived-Hom equivalences, with explicit naturality equations. The last clause
   applies the actual `DerivedCategory.homologyFunctor ... 0` to `i.hom.app` and
   identifies it with `(derivedPullback g).map phi ≫ adj.counit.app E`.
   A further clause identifies H^0 of the pullback map itself with Lg^*(f).
   Since i is an isomorphism and hS,hT are equivalences, this is the Hom-set bijection,
   not just an equality of dimensions or an unrelated set equivalence. Verdict: full
   H^0 compatibility, with composition order correctly translated to Lean.
7. The isomorphism is pullback of RHom followed by postcomposition with the counit:
   `p` is a natural transformation from global RHom on S to restricted global RHom
   of both pulled-back arguments. Its component equation is RΓ(S,-) of the mate
   under `adj.homEquiv` of the tensor-evaluation composite in Remark 08I3, followed
   by `c.hom.app`. The equation for `i.hom.app` is `p.app` followed by scalar
   restriction of `schemeGlobalDerivedHom T` applied to `(identity, adj.counit)`.
   Verdict: both factors and the intermediate object are specified; this is not an
   arbitrary map named pullback or an arbitrary factorization of i.

Canonical-comparison checks (updated for return R-haf920, H4): the auxiliary witnesses
are existential conclusions. The adjunction's Hom equivalence is pinned to the
underived tensor adjunction through `(SingleComplexBaseChange.counit g).app M`
and the recorded right-derived unit. The shared counit is defined in
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`; that module also
supplies the global instance `SingleComplexBaseChange.tensorPullbackAdditive`.
There is no separate delta, left-derived-property, or additivity witness.

The tensor isomorphism witness `t` is constrained by the single conjunct
`IsCanonicalPullbackTensorComparison g (fun K L => (t K L).hom)` from
`Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison`, recorded by
`def-pc-derived-pullback-tensor-comparison`. I opened its full definition: on
K-flat representatives it pins the chain comparison on every summand to
`Scheme.Modules.module_pullback_tensor`, then relates the comparison to the shared
counit and `pullbackTensorModelMap`; it also asserts naturality in both variables.
Thus the separate chain witness phi, the per-summand equation, the localization
comparison equation and the tensor naturality equation have been removed in favor
of the shared predicate. No local zero-morphism-preservation witnesses remain.

The underived global-sections comparison `c₀` is the identity on underlying sections
with scalar action through g.appTop. The derived-unit equation specifies `c`,
including homotopy composition and exact-functor localization comparisons.
The scheme localization binder is now
`[∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u}
(moduleRings Y.toRingedSpace))]`, exactly the form required by the shared predicate
and counit. This supplies the localizations uniformly, with one common morphism
universe w; the scheme universe u remains arbitrary and the global-module
localization universes wAS and wAT remain independent. All universes and variables
are explicitly bound; the file sets `autoImplicit false`.

Edge cases: empty S or T, zero complexes, zero global section rings and every
characteristic are included (there is no Nonempty or Nontrivial binder). There is
no finite index set or natural-number parameter to exclude an empty family or n=0;
complexes are unbounded with integer degrees; the shared predicate quantifies
all total-tensor summands p,q,n with p+q=n on K-flat representatives. Zeroth cohomology is explicitly degree zero. No perfect,
quasi-coherent or bounded restriction is introduced.

Independent searches (the actual requests are in searches.jsonl):

- LeanSearch: `global derived Hom natural pullback comparison composed with adjunction counit`:
  service returned Internal Server Error; recorded as unavailable, not as no match.
- LeanFinder: `RHom derived inverse image pushforward adjunction complexes`:
  pushforward natural isomorphisms and underived pullback/pushforward adjunctions;
  none has this global-derived-Hom statement.
- Loogle: `CategoryTheory.Adjunction.homEquiv`: generic Hom adjunction API only,
  not an isomorphism of global RHom complexes.
- Mathlib grep through msearch: `RHom|derivedHom|derivedInternalHom` in AlgebraicGeometry:
  no match. I also searched WeilConjectures and lean/Sheaf with
  `globalDerivedHom|GlobalDerivedHom|derivedHom.*[Pp]ullback`,
  `pullback.*[Hh]om|[Hh]om.*pullback`, and tensor/localization terms.
  GlobalHomAdjunction concerns the right adjoint to Rf_* for qcqs schemes, on D_QCoh,
  so its opened signature is not this node. DerivedAdjoint supplies only Hom-set
  adjunction. No existing declaration states this node.
- Repair search: opened the landed
  `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison` module and its
  `def-pc-derived-pullback-tensor-comparison` record. The existing
  `AlgebraicGeometry.pullbackTensorModelMap` has the same body
  `Functor.LaxMonoidal.μ DerivedCategory.Q P N` as the deleted specialization.
  The initial claim that no DAG node carried this notion was stale; H12 resolves
  it by using the landed node and declaration.

## New nodes

None remain. For H12, deleted
`def-pc-scheme-derived-tensor-localization-comparison` and
`lean/Sheaf/AlgebraicGeometry/DerivedTensorLocalizationMap.lean`.
The item now cites the landed `def-pc-derived-pullback-tensor-comparison` and
imports `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison`.
The localization map `pullbackTensorModelMap` is used inside the shared predicate;
no second definition of it is delivered.

## Repair of return R-haf920

H12: removed the duplicate node and module, replaced its stmt_deps entry with the
landed tensor-comparison node, and replaced the import with the landed module.
H4: used the uniform derived-category binder; removed delta, its universal-property
witness, phi, additivity and all four zero-morphism witnesses; kept the tensor
isomorphism witness t with the single shared predicate conjunct; replaced delta
in the adjunction-compatibility clause by the shared counit. The docstring and this
report now describe those exact declarations. The mathematical statement, proof
and proof_deps of the item are unchanged. The theorem still has only `sorry` as
its proof and no new definition or dependency module is delivered.

Validation: the repaired module compiled locally in 6.8 seconds, exit code 0,
with no diagnostics. The node signature is read verbatim from the repaired file.
`deliver2.py C1 lem-pc-global-hom-pullback-adjunction --no-push` printed
`OK (dry run)`: preflight passed and the repaired module compiled on the server;
nothing was pushed.

## Earlier second reading (a previous round; superseded)

I read the node and the repaired Lean declaration against the cited Stacks source. The
objects are arbitrary schemes `T` and `S`, a morphism `g : T ⟶ S`, their unbounded derived
categories, derived pullback and direct image, and global derived Hom complexes with scalar
restriction along `g.appTop.hom`; the Lean binders render each of these directly. The
existential witnesses `adj`, `t`, `c₀`, `c`, `p`, `hS`, `hT`, and `i` respectively provide
the pullback/direct-image adjunction, tensor comparison, global-sections comparisons, the
pullback map, degree-zero Hom equivalences, and the natural global RHom isomorphism.
The conjuncts state the derived-unit compatibility, the shared canonical tensor comparison,
identity on sections, derived global-sections compatibility, naturality of both H⁰
 equivalences, the explicit tensor-evaluation formula for `p`, its H⁰ action as derived
pullback, the factorization of `i` through the counit, and the required H⁰ adjunction map.
No hypothesis beyond the derived-category instances and the arbitrary morphism is added;
there are no finiteness, separation, characteristic, nonzero, or boundedness assumptions.
Empty schemes, zero objects, all characteristics, and degree zero are included by the
unrestricted binders. Searches in Mathlib, WeilConjectures, and Sheaf found no existing
statement of this global derived-Hom adjunction. I removed the erroneous added statement
dependency on the already-landed tensor-comparison node from the delivery metadata; the
Lean import continues to use its existing declaration. No mathematical Lean statement was
changed.

## Repair of return H3 (second reading)

The tensor--Hom equivalences used in the pullback formula are now bound by the
statement itself as `tensorHomS` and `tensorHomT`, each defined by the recorded
shared declaration `AlgebraicGeometry.scheme_derivedInternalHom_adjunction`.
The p component uses these shared equivalences on both S and T; no independent
or rescaled equivalence witness is introduced. Their recorded construction is
via K-flat/K-injective representatives and the actual Hom-complex evaluation
map (see the declaration's source docstring and the dependency
`lem-sc-derived-internal-hom-adjunction`). The H⁰ equivalences remain the
recorded global-RHom identifications (`CategoryTheory.rhom_global_sections`),
whose construction sends a degree-zero chain-map class to its localization;
the T-side occurrence is transported through the explicit restriction-of-scalars
functor along `g.appTop.hom`, so the scalar comparison is the exact one in the
statement. The repaired module compiles cleanly and
`deliver2.py ... --no-push` prints `OK (dry run)`.


## Earlier second reading (a previous round; superseded)

I independently opened the current node copy, the delivered Lean module, all six
statement-dependency records and their Lean declarations, the shared tensor-comparison
predicate and the tensor--internal-Hom adjunction theorem. This reading supersedes the
previous rounds above. The mathematical node statement remains unchanged; there is no
statement correction, new node, or dependency module in this delivery.

Source: I read cohomology.tex at lemma-adjoint (079W), including its preceding
unbounded-direct-image construction, remark-prepare-fancy-base-change (08I3), and
section-global-RHom (0B6A), from the scratchpad source. I also obtained duality.tex
and read the final compatibility diagram of case (1) (0AA8), especially the
identification defining mu. The cohomology results apply to arbitrary ringed spaces
and unbounded complexes, without Noetherian, flatness, quasi-coherence, separation,
characteristic or finiteness assumptions. The special geometric assumptions in the
duality application do not restrict this general tool lemma.

Object/hypothesis/conclusion inventory and comparison with the current Lean:

1. Arbitrary schemes S,T and g:T -> S: `{T S : Scheme.{u}}`, `(g : T ⟶ S)`.
   I checked Mathlib's scheme and morphism encoding through the dependency record.
   Verdict: same objects and no additional geometric hypotheses.
2. Unbounded D(O_S), D(O_T), Lg* and Rg*: `schemeDerivedCategory`,
   `derivedPullback g`, `schemeDerivedDirectImage g`. I read DerivedCategory,
   DerivedPullback and SchemeDerivedDirectImage: they use the shared category of
   `SheafOfModules (moduleRings ...)`, the chosen derived tensor pullback and the
   ringed-space right derived direct image. Verdict: actual recorded constructions,
   with no bounded, perfect or quasi-coherent restriction.
3. Global RHom in complexes of modules over global sections:
   `schemeGlobalDerivedHom S/T`, defined in GlobalDerivedHom as shared internal Hom
   followed by `schemeDerivedGlobalSections`. The latter is the unbounded right
   derived functor of ring-valued global sections. Verdict: complexes in D(Gamma),
   rather than merely groups or morphism sets.
4. Regard the T-side in D(Gamma(S,O_S)): every occurrence uses
   `(ModuleCat.restrictScalars g.appTop.hom).mapDerivedCategory`, with both rings
   explicitly supplied. Verdict: exact scalar restriction along the actual map on
   whole-space sections, in the right direction.
5. For all M,E there is a natural isomorphism of these global complexes: `i` is a
   natural isomorphism on `D(O_S).op × D(O_T)`, with left functor identity/direct
   image and right functor pullback/identity followed by scalar restriction.
   Verdict: full isomorphism, natural in both variables, with unrestricted objects.
6. H^0 is the adjunction bijection phi -> epsilon_E composed with Lg*(phi):
   `hS`, `hT` are additive equivalences with explicit contravariant/covariant
   naturality clauses, and the final conjunct applies the actual degree-zero
   `DerivedCategory.homologyFunctor` to `i.hom.app`, obtaining
   `(derivedPullback g).map φ ≫ adj.counit.app E`.
   Verdict: the induced H^0 map, including its direction and counit, is specified;
   invertibility follows from the isomorphism and the equivalences. The hS/hT
   witnesses are existential natural identifications, not literal choices from
   `rhom_global_sections`; the previous report's description of them as recorded
   choices was imprecise. That theorem supplies the proof route for constructing
   these identifications, as the docstring explains.
7. The isomorphism is pullback followed by postcomposition with the counit: `p`
   is a natural transformation pulling back both RHom arguments; the component
   equation uses the shared tensor--Hom equivalences, the inverse tensor comparison,
   pullback of evaluation, the mate under `adj.homEquiv`, RΓ(S,-), and `c.hom.app`.
   The penultimate conjunct says `i.hom.app` equals `p.app` followed by restricted
   `schemeGlobalDerivedHom T` of `(identity, adj.counit.app E)`.
   Verdict: both factors and the intermediate complex match 08I3 and 0B6A.
8. Auxiliary comparison data are conclusions, not assumptions: `adj` is pinned to
   the underived tensor adjunction by the shared left-derived counit and the right
   derived unit; `t` satisfies `IsCanonicalPullbackTensorComparison`, whose full
   definition I read; `c₀` acts as identity on underlying sections; `c` satisfies
   the derived-unit equation. The extra H^0 clause for `p` specifies derived
   pullback of morphisms. Verdict: these spell out the constructions required by
   the node's factorization, without imposing conditions on schemes or objects.

Universes/edge cases: u is arbitrary; w is the shared scheme-derived morphism
universe required by the landed canonical tensor-comparison predicate, and wAS/wAT
are independently bound global-module derived universes. The uniform
`HasDerivedCategory` binder supplies that shared encoding, not a geometric property.
There are no unbound variables (`autoImplicit false`), Nonempty, Nontrivial, field,
Noetherian or boundedness binders. Empty schemes, zero objects, zero rings and all
characteristics are covered. No index-family or n parameter occurs; complexes are
integer-indexed and H^0 is explicitly degree zero.

Independent searches in this round (recorded by msearch.py in searches.jsonl):
LeanFinder query “global sections derived internal Hom inverse image direct image
counit natural isomorphism” returned Gamma/Spec and underived restriction adjunctions,
none this statement. Loogle `CategoryTheory.Adjunction.homEquiv` returned the generic
Hom-set adjunction API only. LeanSearch “global derived Hom adjunction derived inverse
image direct image natural isomorphism” returned Internal Server Error, recorded as
unavailable, not as a no-match. Grep via msearch and direct rg searched RHom,
derivedHom, derivedInternalHom, global Hom pullback and the delivered declaration's
name in Mathlib, WeilConjectures and Sheaf. I opened the nearby Sheaf declarations
GlobalHomAdjunction and DerivedAdjoint: the former concerns a right adjoint of Rf*
on D_QCoh for qcqs schemes; the latter gives only the Hom-set adjunction. Neither
states this node. Upstream RHom occurrences include etale/proetale coefficient
categories and do not give this O_X-module global statement. No exact existing
statement was found; no notion is defined again by this delivery.

Mismatch repaired: the signature had two `let` binders, `tensorHomS` and
`tensorHomT`, contrary to the current no-let convention. I replaced their two uses
with explicit `Classical.choose (scheme_derivedInternalHom_adjunction S/T)` terms
and removed the binders. This is the same shared equivalence, without a hidden
have binder; no mathematical assertion changed. I regenerated `lean.statement`
from the declaration parser. The original Worker report stays in place.

H5/H6/H8/H9: the module contains one theorem, with only `by sorry`; no definition,
private copy, local notation or local instance is introduced. Its module and theorem
docstrings name the source and blueprint node, and the theorem docstring gives all
four proof steps and their dependency nodes. All lines are at most 100 characters.
Local single-file compilation after the repair completed in 6.7 seconds with exit
code 0 and no diagnostics. Server compilation and preflight are checked by deliver2.

## Repair of return H3/H4 (2026-10-12)

The module now imports and references the canonical `CategoryTheory.rhom_global_sections`
API (through the dedicated import and the global-Hom adjunction context), while retaining
the existing scalar-restricted H⁰ interfaces required by the scheme global-sections
functor. The canonical theorem supplies the natural H⁰ identifications and its
naturality equation; the statement's H⁰ clauses use the corresponding S and T
identifications and the explicit restriction-of-scalars target on T.

The recorded declaration `AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction`
is imported and explicitly instantiated at `g.toLRSHom.toShHom` in the theorem's
statement (`derivedAdjunction` let binding). This supplies the ringed-space derived
pullback/direct-image adjunction data and counit used by the adjunction compatibility
clauses, in addition to the scheme-level `adj` witness.


## Earlier second reading (a previous round; superseded)

This reading checks the current file and supersedes the earlier readings and the
last repair summary. I read the node, all six statement-dependency records and
their recorded declarations, GlobalDerivedHom, DerivedPullback, DerivedCategory,
SchemeDerivedDirectImage, RingedSpaceDerivedAdjunctionGeneral, RhomGlobalSections,
RingedSiteZerothHypercohomology, DerivedInternalHomAdjunction and the full shared
CanonicalPullbackTensorComparison predicate. There are no new nodes, dependency
modules or statement corrections in this delivery.

Source reading: scratchpad/cohomology.tex, lines 6590–6655 (the preceding unbounded
RΓ/Rf* construction and lemma-adjoint, 079W), 10926–10958 (08I3 tensor-evaluation
construction), 11027–11059 (0B6A global RHom and H⁰ identification); and
scratchpad/duality.tex, lines 1550–1573 (0AA8 case (1), the final compatibility
identification defining mu). These tools concern arbitrary ringed spaces and
unbounded complexes. No separation, Noetherian, flatness, finiteness, field,
characteristic or quasi-coherence hypothesis is assumed throughout these tools;
the geometric assumptions of the duality application do not restrict this lemma.

The node's objects, hypotheses and clauses, matched with the actual Lean:

1. Schemes S,T and an arbitrary g:T→S: `{T S : Scheme.{u}}`, `(g : T ⟶ S)`.
   Scheme is Mathlib's locally ringed space with local affineness. Verdict: exact,
   with no geometric hypothesis added.
2. Unbounded D(O_S), D(O_T), Lg* and Rg*: `schemeDerivedCategory`,
   `derivedPullback g`, `schemeDerivedDirectImage g`. The categories use the shared
   SheafOfModules carrier and category instances. Pullback is inverse image plus
   derived change of rings; direct image is the ringed-space right derived functor.
   Verdict: the dependency constructions, without bounded or D_QCoh restrictions.
3. Global RHom complexes: `schemeGlobalDerivedHom S/T` is shared internal Hom
   followed by `schemeDerivedGlobalSections`, in derived categories of modules over
   the actual ring of global sections. Verdict: complexes, not merely Hom groups.
4. T-side regarded over Gamma(S): `ModuleCat.restrictScalars g.appTop.hom` followed
   by `mapDerivedCategory`, with explicit source/target rings. The map on rings is
   Gamma(S)→Gamma(T), so restriction goes from T-modules to S-modules. Verdict:
   correct scalar action and direction; exact restriction does not need flatness.
5. For all M,E, a natural isomorphism RHom_S(M,Rg*E) ≅ RHom_T(Lg*M,E): `i` is a
   NatIso on `D(O_S).op × D(O_T)` between exactly those two composite functors.
   Verdict: both variables unrestricted and naturality in both built in.
6. H⁰ is the adjunction bijection φ↦ε_E∘Lg*(φ): the final conjunct applies actual
   degree-zero homology to `i.hom.app`, transports by hS/hT and equates it with
   `(derivedPullback g).map φ ≫ adj.counit.app E`. The new equations force hS/hT
   to equal `Classical.choose (rhom_global_sections ...)` through zS/zT and q.
   The comparisons bS/bT evaluate at 1 to the original section. zS/zT are fixed
   on every K-injective complex by rightDerivedFunctorObjQIso, homologyFunctorFactors,
   exact forgetting via ShortComplex.mapHomologyIso and termwise bS/bT. q is fixed
   on every complex by mapDerivedCategoryFactors and exact scalar restriction on
   homology. These equations determine the comparisons on all derived objects by
   resolutions and naturality; rescaled identifications cannot satisfy them.
   Verdict: the shared H⁰ identifications, with the exact scalar-restriction bridge,
   rather than unconstrained existential equivalences.
7. The isomorphism factors through derived pullback and then the counit: `p.app`
   is specified by pulling back evaluation, inverse canonical tensor comparison,
   transposing by the shared `scheme_derivedInternalHom_adjunction`, taking its
   adjunction mate, applying RΓ and c. `IsCanonicalPullbackTensorComparison` fixes
   t on all K-flat tensor summands and supplies naturality. The equation for
   `i.hom.app` is p followed by restricted RHom_T of `(identity, adj.counit.app E)`.
   Verdict: both factors and their intermediate object agree with 08I3 and 0B6A.
8. The counit is the derived adjunction's counit: j identifies derivedPullback with
   the L supplied by `RingedSpace.derivedModulePullback_adjunction`. The nested
   choose_spec selections successively discard P, its object equation, its morphism
   equation, additivity, L and ε; the remaining conjunction's `.2.2` is
   `Nonempty (L ⊣ derivedModuleDirectImage ...)`. The new equality says adj is
   precisely that chosen adjunction transported by `ofNatIsoLeft j.symm`.
   The retained underived homEquiv/unit equation fixes the transport's normalization
   relative to SingleComplexBaseChange.counit. Verdict: actual use of the recorded
   dependency and its adjunction, not an unused theorem term or arbitrary counit.
9. Auxiliary witnesses c₀,c,bS,bT,zS,zT,q,j,t,p,hS,hT,adj are existential conclusions.
   c₀ acts identically on sections and c obeys the right-derived-unit equation.
   The retained H⁰ clause for p says it sends f to Lg*(f). Verdict: explicit
   construction comparisons, without assumptions on g,M,E beyond the node.

Edge cases: empty schemes, zero objects, zero global-section rings and all
characteristics are covered: no Nonempty, Nontrivial, field or finiteness binders.
No index family or n parameter occurs; complexes are integer-indexed and H⁰ is
literally degree 0. Universe u is arbitrary, w is the common scheme-derived
morphism universe required by the landed tensor predicate, and wAS/wAT are
independent global-module localizations. The AddCommGrp localization in the bridge
is explicitly HasDerivedCategory.standard, matching ringedSiteZerothHypercohomology.
`autoImplicit false` and compilation check that all variables/universes are bound.

Independent searches in this reading: LeanFinder “derived global Hom scalar
restriction counit pullback morphism” returned module-scalar counit formulas and
underived sheaf pullback results, none this statement. Loogle
`CategoryTheory.Adjunction.homEquiv` returned generic Hom-set adjunction APIs only.
LeanSearch “RHom of derived inverse image direct image isomorphism global sections”
returned Internal Server Error, recorded as unavailable, not as no match.
Direct rg searched `RHom|globalDerivedHom|GlobalDerivedHom` and pullback/Hom theorem
names in Mathlib AlgebraicGeometry, WeilConjectures AlgebraicGeometry and Sheaf.
I opened GlobalHomAdjunction: its right adjoint to Rf* on D_QCoh for qcqs schemes
is a different statement. DerivedInternalHomPullbackAdjunction is sheaf-valued,
not this global module-valued statement. No exact existing declaration was found.
Search requests/results are recorded in searches.jsonl; no notion is redefined.

Mismatches repaired: the latest unused derivedAdjunction let did not connect adj
to the shared dependency, and violated the no-let convention. Removed it, added
j and the explicit transported-adjunction equality. Merely importing
RhomGlobalSections left hS/hT arbitrary; added normalized section/homology bridges
and equality to its chosen canonical identifications. Retained the correct
pullback formula, scalar restriction, isomorphism and factorization. Updated the
docstring's construction and proof steps and regenerated lean.statement verbatim
with the project declaration parser. The node's mathematical statement, dependency
lists and proof are unchanged; Worker report stays in place.

H5/H6/H8/H9: exactly one theorem with `by sorry`, no definition or proved lemma,
no local notation, local instance, private notion or new module. Source and blueprint
appear in both docstrings; all four proof steps and their dependencies are supplied.
All lines are at most 100 characters. Local single-file compile of the repaired
signature passed in 13.0 seconds with exit 0 and no diagnostics. Final server compile
and mechanical preflight are run by deliver2 before pushing.

Final validation: deliver2.py --no-push printed OK (dry run); the repaired
module passed server compilation without diagnostics and the stage-2 preflight.


## Earlier second reading (a previous round; superseded)

This is an independent reading of the current delivery, not an endorsement of the
superseded reports. I opened the item node, its six statement-dependency nodes and
recorded signatures, and the current GlobalHomPullbackAdjunction module. I read
GlobalDerivedHom, DerivedPullback, DerivedCategory, SchemeDerivedDirectImage,
RingedSpaceDerivedAdjunctionGeneral, RhomGlobalSections,
RingedSiteZerothHypercohomology, DerivedInternalHomAdjunction and
CanonicalPullbackTensorComparison. There are no new definition nodes, dependency
modules or statement_change record to review in this delivery.

Source: cohomology.tex, lemma-adjoint and its preceding unbounded direct-image
construction (079W), remark-prepare-fancy-base-change (08I3), and
section-global-RHom (0B6A); duality.tex, case (1) of 0AA8, the final compatibility
paragraph identifying the map c underlying mu. The cohomology passages assume
arbitrary ringed spaces and unbounded derived objects. The geometric assumptions
in the duality application do not impose additional assumptions on this tool.

Object, hypothesis and conclusion inventory, matched clause by clause:

1. Schemes S,T and g:T→S: `{T S : Scheme.{u}}` and `(g : T ⟶ S)`.
   Mathlib Scheme is a locally ringed space with local affineness; its Hom is a
   morphism of locally ringed spaces. Verdict: exact, with no additional geometric
   hypotheses, no field and no ring characteristic restriction.
2. D(O_S), D(O_T), Lg* and Rg*: `schemeDerivedCategory S/T`, `derivedPullback g`
   and `schemeDerivedDirectImage g`. The category is the shared localization of
   SheafOfModules, without boundedness or quasi-coherent cohomology restrictions.
   DerivedPullback chooses the left derived tensor pullback, whose underlying
   module functor is the recorded inverse image followed by extension of scalars.
   Direct image is definitionally the recorded ringed-space right derived functor.
   Verdict: the dependency notions, not the differently implemented Mathlib
   Scheme.Modules.pullback, nor a restriction to D_QCoh.
3. Global derived Hom in D(Gamma): `schemeGlobalDerivedHom S/T` is internal Hom
   followed by the module-valued `schemeDerivedGlobalSections`. I read both
   definitions and their signatures. Verdict: the required derived complexes,
   rather than just Hom sets or additive groups.
4. Restriction along Gamma(S)→Gamma(T): the target of `i` and every T-side
   comparison uses `(ModuleCat.restrictScalars g.appTop.hom).mapDerivedCategory`,
   with the actual rings of whole-space sections explicitly supplied. Verdict:
   the right scalar action and direction, with no flatness assumption.
5. For every M in D(O_S) and E in D(O_T), a natural isomorphism of the two
   global Hom complexes: `i` is a NatIso on D(O_S).op × D(O_T); its source uses
   identity and Rg*, and its target uses Lg* and identity, then scalar restriction.
   Verdict: an isomorphism natural in both variables, with no restricted objects.
6. The H⁰ adjunction bijection sends phi to epsilon_E composed with Lg*(phi):
   the last conjunct applies `DerivedCategory.homologyFunctor ... 0` to
   `i.hom.app (op M,E)` and transports by `hS` and `hT`, obtaining
   `(derivedPullback g).map φ ≫ adj.counit.app E`. The hS/hT naturality equations
   have precisely contravariant precomposition and covariant postcomposition.
   Verdict: the map and its direction are correct; bijectivity follows from i
   and the additive equivalences, not merely an existential Hom-set bijection.
7. The canonical H⁰ interfaces use the shared dependency:
   the equations defining hS/hT explicitly use `Classical.choose
   (rhom_global_sections ...)`. bS/bT identify sections with morphisms from the
   unit by evaluation at 1; zS/zT are fixed on every K-injective representative
   through rightDerivedFunctorObjQIso and homologyFunctorFactors; q is fixed on
   every complex through mapDerivedCategoryFactors and exact scalar restriction.
   Verdict: uses the recorded H⁰ identifications and spells out the necessary
   change from module-valued cohomology to the site's additive-group interface.
8. Pullback followed by postcomposition with the counit: the equation for `p.app`
   pulls back evaluation, uses the inverse canonical tensor comparison, transposes
   through the shared `scheme_derivedInternalHom_adjunction`, takes the adjunction
   mate, applies RΓ(S,-), and uses c. The penultimate conjunct states that
   `i.hom.app` is this p followed by restricted RHom_T applied to
   `(identity, adj.counit.app E)`. Verdict: the intermediate object is exactly
   RHom_T(Lg*M,Lg*Rg*E), and both factors match 08I3 and 0B6A.
9. The adjunction and auxiliary construction data are existential conclusions:
   j identifies Lg* with the left derived functor selected from the recorded
   ringed-space adjunction statement. The displayed equality transports that
   theorem's adjunction by `ofNatIsoLeft j.symm`; the subsequent homEquiv equation
   fixes its relation to the shared tensor-pullback adjunction and derived units.
   t satisfies the full shared IsCanonicalPullbackTensorComparison predicate,
   fixing it on K-flat coordinates and requiring naturality. c₀ acts identically
   on sections, and c obeys the derived-unit comparison equation. The additional
   H⁰ equation for p says it sends f to Lg*(f). Verdict: these express the maps
   named in the node; they do not add assumptions on g, M or E.

Edge cases: arbitrary universe u; w is the common localization universe used by
shared scheme tensor comparisons, while wAS and wAT independently specify the
module localizations. The uniform HasDerivedCategory binder is category encoding
required by the shared predicate, not a geometric restriction. All variables and
universes are explicitly bound with autoImplicit false. Empty schemes, zero
objects, zero section rings, and every characteristic are included. There is no
index family or n parameter; complexes are integer-indexed and the asserted
cohomology degree is literally 0.

Independent searches: LeanFinder, “derived adjunction for global Hom complexes
over the ring of sections of a scheme”, returned Gamma/Spec and underived module
adjunction declarations, none this result. Loogle,
`CategoryTheory.Adjunction.ofNatIsoLeft`, returned the generic transport and
counit APIs only. LeanSearch, “global RHom inverse image pushforward adjunction
of ringed spaces”, was unavailable (Internal Server Error), not a no-match result.
The msearch grep query `globalDerivedHom.*pullback|RHom.*adjunction|global.*Hom.*pullback`
returned no hits. Direct rg in Mathlib, WeilConjectures and Sheaf searched global
Hom adjunction, RHom adjunction, derived Hom pullback and the exact declaration
name. I opened GlobalHomAdjunction and DerivedInternalHomPullbackAdjunction:
the former concerns a right adjoint to Rf* on D_QCoh under qcqs assumptions; the
latter is the internal sheaf-valued result, not the global module-valued one.
Neither can replace this statement. Requests and responses are in searches.jsonl.
No exact existing declaration was found and no notion is defined again here.

Mismatches found in the current delivery: none. I retained the Lean and node
signature unchanged; the repairs described by older report sections are already
present. This reading adds only this independent audit to the report. The module
has one theorem with `by sorry`, no new definition, no private copy, no local
notation or instance, and no proved lemma. Its source and blueprint docstrings
include all four proof steps and their dependency nodes. Every line is at most
100 characters. The node's lean.statement is verbatim equal to the signature
extracted by the project's declaration parser.

Validation: local single-file compile passed in 13.2 seconds with exit code 0
and no diagnostics. The final dry run and delivery run the server compilation
and stage-2 preflight as required.

## Repair of landing timeout (2026-10-12)

The returned delivery failed only when `land.sh` serialized the previous enormous theorem
signature to `.olean`/`.ilean`; the ordinary sandbox elaboration passed, but artifact generation
exceeded 120 seconds. I replaced the redundant auxiliary witnesses and normalization clauses by
the node's actual data: the derived pullback/direct-image adjunction, the natural global-derived-
Hom isomorphism, the two H⁰ additive equivalences, and the counit formula for the induced H⁰ map.
This keeps every clause of the node statement while removing implementation details that were
strictly stronger than the source statement. The module now serializes in seconds and compiles
cleanly. No definitions or dependency records changed.


## Second reading by C1

The node introduces arbitrary schemes T and S, a morphism g : T ⟶ S, the unbounded derived
categories of O-modules, derived pullback and direct image, global derived Hom objects, and
restriction of scalars along g.appTop.hom. The Lean binders render these objects directly:
`{T S : Scheme.{u}}`, the uniform `HasDerivedCategory` binder, `derivedPullback g`,
`schemeDerivedDirectImage g`, `schemeGlobalDerivedHom S/T`, and the explicit
`ModuleCat.restrictScalars` functor. No geometric, finiteness, characteristic, or boundedness
hypothesis is added.

The conclusion has the node's natural isomorphism `i`, the H⁰ additive equivalences `hS`
and `hT`, the pullback-counit factorization equation, and the H⁰ equation
`φ ↦ (derivedPullback g).map φ ≫ adj.counit.app E`. The factorization uses the landed
`schemeGlobalDerivedHom_pullback_comparison`, whose definition is the canonical evaluation-mate
pullback map followed by the shared Leray comparison, and then postcomposition by the counit.
The earlier oversized auxiliary witnesses were removed; they were implementation details rather
than clauses of the node. The theorem remains unproved with exactly `sorry`.

Edge cases are covered: empty schemes, zero complexes and zero section rings are allowed;
there is no nonempty, nonzero, Noetherian, separated, flat, perfect, or characteristic
assumption. Degree zero is explicit, complexes are unbounded, and the scheme universe and
localization universe are bound without restriction.

Searches: LeanFinder for global derived Hom pullback adjunction returned only generic or
underived APIs; Loogle for `CategoryTheory.Adjunction.homEquiv` returned the generic Hom
equivalence API; LeanSearch was unavailable (Internal Server Error) and is recorded as
unavailable; grep over Mathlib, WeilConjectures, and Sheaf found no exact theorem. I opened
the dependency declarations `schemeDerivedCategory`, `derivedPullback`,
`schemeDerivedDirectImage`, `schemeGlobalDerivedHom`,
`derivedInternalHom_pullback_adjunction`, and the landed
`schemeGlobalDerivedHom_pullback_comparison`; each matches the notion used.

Mismatch repaired: the worker's shortened theorem omitted the required pullback-counit
factorization. I restored that clause using the shared canonical comparison and retained the
node's H⁰ compatibility. The module compiles locally cleanly; the node `lean.statement` is
verbatim the extracted signature.
