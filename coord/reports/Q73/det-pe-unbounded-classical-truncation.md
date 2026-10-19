## Worker report

The item is stated in `lean/Sheaf/SixFunctors/UnboundedClassicalTruncation.lean`.
The module defines the constant coefficient ring sheaf for an arbitrary finite unital ring,
the category of its module sheaves, evaluation at `W` after forgetting scalars, the total right
derived evaluation functor, and degreewise cohomology.  The theorem
`AlgebraicGeometry.ProEtale.unbounded_classical_truncation` then states both clauses with `sorry`.

The binders render the node as follows.  `X : Scheme.{u}` is the scheme; `A : Type u` with
`[Ring A] [Finite A]` is the finite unital coefficient ring, with no commutativity assumption;
`W : X.ProEt` is the chosen small pro-etale object.  The typeclass binders provide the derived
categories and K-injective resolutions that the source's total derived functor requires, and the
additivity instance is the structural property of evaluation.  `e : ℕ` is the uniform bound.
The hypothesis `hbound` quantifies over every integer `q` and every module sheaf `H`, assumes
`IsClassicalModuleSheaf H` and `q > e`, and says `IsZero (sectionCohomology X A W q H)`.
`L` and `K` are objects of the unbounded derived category; `hL` and `_hK` say all their
cohomology sheaves are classical via `IsClassicalModuleComplex`.  The integer `b` and `hb`
state that the cohomology of `L` vanishes in every degree above `b`.

The first conclusion is the quantified bound `IsZero H^m RΓ(W,L)` for every
`b + e + 1 < m`.  The second conclusion quantifies over every classical `K` and integers `m,N`,
assumes `N < m - e - 1`, and asserts `IsIso` for the homology map induced by the canonical
`t.truncGEπ N : K ⟶ τ_{≥N} K`.  `AddCommGrpCat` is the underlying abelian-group target,
so this is exactly the node's explicitly permitted underlying-group formulation; the canonical
maps come from the additive evaluation and retain the coefficient action before forgetting.
The helpers use Mathlib's `constantSheaf`, `SheafOfModules.evaluation`,
`Functor.rightDerivedFunctor`, `DerivedCategory.homologyFunctor`, and the canonical t-structure.

Dependencies used: `def-pc-scheme` via Mathlib `AlgebraicGeometry.Scheme`; `sk-def-pe-site` via
Mathlib `AlgebraicGeometry.Scheme.ProEt`; `def-weil-pbc-constant-sheaf` via
`CategoryTheory.constantSheaf`; `def-weil-sheaf-of-modules-category` via
`Sheaf.CategoryTheory.RingedSiteModules` and Mathlib `SheafOfModules`; `def-weil-abstract-derived-category`
via Mathlib `DerivedCategory`; `sk-def-pe-classical-definition` via the dependency module
`Sheaf.SixFunctors.ClassicalDefinition`; `def-sp-kinjective-bridge` via the generic right-derived
functor API; and `def-kun-truncations` via Mathlib's canonical t-structure truncation map.

Edge cases checked from the source statement and construction: `A` may be noncommutative and may
be the zero finite ring; `e` may be zero; `b` and `N` are arbitrary integers (including negative
values); the index object `W` is arbitrary, including an empty or terminal site object; and the
complexes are genuinely unbounded below.  No nonemptiness or commutativity hypothesis was added.

Searches made:

- `msearch.py ... leanfinder "fixed-degree truncation for pro-etale derived sections classical cohomology"`:
  eight unrelated étale/presentation hits; no matching truncation theorem.
- `msearch.py ... loogle "DerivedCategory homologyFunctor truncGE rightDerivedFunctor"`:
  zero hits (the service reported unknown identifier `homologyFunctor`).
- `msearch.py ... grep "classical.*trunc|trunc.*classical|rightDerivedFunctor" Mathlib`:
  zero hits.
- `rg` over `lean/Sheaf` and the read-only `WeilConjectures` source found the existing
  `AlgebraicGeometry.ProEtale.IsClassical` continuity predicate and generic derived-section APIs,
  but no statement of this item.
- The dependency records and their source declarations were read in full.  The existing
  `ClassicalContinuityMap` only handled the commutative intrinsic module specialization, so the
  dependency module below records the general module-sheaf and derived-complex clauses without
  copying the continuity-map construction.

## Dependency modules

- `sk-def-pe-classical-definition`: `lean/Sheaf/SixFunctors/ClassicalDefinition.lean` defines
  `AlgebraicGeometry.ProEtale.IsClassicalModuleSheaf` from the existing set-sheaf predicate
  `AlgebraicGeometry.ProEtale.IsClassical`, and
  `IsClassicalModuleComplex` by applying it to every derived homology sheaf.  The current base record uses
  `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`: its module and complex predicates require
  commutative coefficients and a particular constant `CommRingCat` sheaf. Those interfaces cannot
  accept the noncommutative coefficients of this item. The dependency module supplies the
  general underlying-set interface and specializes to exactly the recorded node clauses; no
  alternate affine-presentation predicate or continuity map is introduced.

Self-check of the retained packet (2026-10-17): both modules compile cleanly through
`scompile.py` against the current published sources. The node signature was synchronized
verbatim with the compiling theorem (one closing parenthesis was missing from the metadata),
and all owning-module helpers are listed in `lean.declarations`. The dependency note now
identifies the current commutative-only interface instead of describing an absent record.
The mathematical statements were retained unchanged. The dry run also identified the
preflight signature convention (the stored signature ends before `:=`) and a wrapped
blueprint tag in the theorem docstring; both signature records and the tag layout were repaired.

## Earlier second reading (a previous round; superseded)

I read the source node statement, its detailed blueprint proof, the source place
`sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-truncation.md`, the item
module, and the repaired dependency module. The item-by-item rendering is:

- `X : Scheme.{u}` is the scheme, `A : Type u` with `[Ring A] [Finite A]` is an
  arbitrary finite unital ring (no commutativity), and `W : X.ProEt` is the chosen
  small pro-etale object. `coefficientRingSheaf X A` is the `RingCat` constant
  sheaf and `coefficientModules X A` is its left-module-sheaf category. Verdict: exact.
- The derived-category and K-injective binders provide the unbounded
  `D(coefficientModules X A)`. `evaluationAb` followed by `rightDerivedFunctor`
  is the node's evaluation `RΓ(W,-)` after forgetting scalars, while
  `sectionCohomology` is its degree-`q` cohomology on a degree-zero sheaf in
  `AddCommGrpCat`; the coefficient action is retained by the underlying-group
  forgetful functor. Verdict: exact.
- `e : ℕ` and `hbound` quantify over every `q : ℤ` and module sheaf `H`, require
  `IsClassicalModuleSheaf H` and `q > e`, and assert vanishing. The first
  conjunct binds `L`, `_hL : IsClassicalModuleComplex L`, `b`, and the implication
  hypothesis saying `IsZero (H^q(L))` for `b < q`. Verdict: exact.
- The first conjunct is `IsZero` of `H^m RΓ(W,L)` for every `b+e+1 < m`.
  The second independently quantifies over every classical `K` and integers `m,N`, assumes
  `N < m-e-1`, and asserts `IsIso` for the homology map induced by the canonical
  `truncGEπ N : K ⟶ τ₍≥N₎ K`. Verdict: these are exactly the two source clauses.

Edge cases were checked again: zero and noncommutative finite rings, zero sheaves
and complexes, `e = 0`, negative `b` and `N`, `m = 0`, empty or terminal site
objects (and the empty scheme), and complexes unbounded below. No extra
nonemptiness, commutativity, characteristic, Noetherian, or finiteness hypothesis
appears.

The duplicate searches were repeated with LeanFinder/Loogle-style queries and
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`; they found only the generic
`constantSheaf`, `SheafOfModules.evaluation`, derived-category, and truncation APIs,
plus the existing set predicate `AlgebraicGeometry.ProEtale.IsClassical`. No exact
statement or coefficient-module classicality declaration exists. The recorded
`sk-def-pe-classical-definition` declaration was unusable for this item because its
module/complex predicates are tied to a commutative `CommRingCat` constant sheaf;
the delivered `ClassicalDefinition.lean` repair generalizes those predicates to an
arbitrary ring sheaf using the same underlying-set predicate, and applies it in
every derived degree.

Mismatches found and repaired during this second reading:

- H3: `L`, its classicality, and its upper cohomology bound were outer binders,
  making clause (2) syntactically conditional on unrelated clause-(1) data. I
  moved them inside the first conjunct; clause (2) now needs only the shared
  hypothesis `hbound`, as the node does. The natural-language node is unchanged.
- H3/H4: the additive evaluation property was an explicit instance hypothesis.
  I made `evaluationAb` a transparent abbreviation of the existing additive
  forget/evaluation functors and removed that hypothesis everywhere. Its data and
  the map used by clause (2) are unchanged, and additivity is inferred.
- H8/H9: the four-sentence proof sketch did not carry the node's seven steps,
  and the recorded proof-dependency modules were missing. The docstring now gives
  all seven steps with their node references; the stated dependency modules are
  imported with proof-only visibility. Statement dependencies are public imports.
- H13: the repaired dependency gave module-sheaf and derived-complex predicates,
  but omitted the source's literal cochain-complex clause. I added
  `IsClassicalModuleCochainComplex`, quantifying over all integer homology objects,
  and listed it in the dependency record. The set-sheaf clause continues to use
  the publicly imported existing `IsClassical`; no continuity map is duplicated.

I synchronized `lean.statement` verbatim with the revised theorem and verified
all declaration records. There is no node statement correction, new node, or
change to the mathematical dependencies or proof. The worker's earlier metadata
parenthesis repair was already present when I started; it is retained.

Independent search results: LeanFinder's query about derived sections commuting
with sufficiently low truncation returned eight generic cochain-truncation hits;
LeanSearch's uniform-vanishing query returned eight generic homology/truncation
hits; Loogle `CochainComplex.truncGE` returned twelve canonical-truncation hits.
These do not state the pro-etale theorem. `rg` over the project and upstream
confirmed that the arbitrary-ring predicates are absent; the commutative
`IsClassicalModule`, `IsClassicalCochainComplex`, and `IsClassicalComplex` were
opened at their signatures and rejected as interfaces for noncommutative rings.

The small-site size check reads `X.ProEt : Type (u+1)` with morphisms in
`Type u`; the constant ring and module values live in `Type (u+1)`. The
`ULift` on `A : Type u` is the canonical size lift, not a restriction on the
finite ring or on the site morphisms. The continuity predicate quantifies over
all `I : Type (u+1)` with `SmallCategory I` and `IsCofiltered I`, as its recorded
presentation node specifies. An empty index category is therefore excluded by
the source's cofiltered hypothesis itself. The Postnikov proof includes `n=0`.

For source checks I also read Stacks `derived.tex`, Remark 08J5 (the canonical
truncation triangle and the quotient-to-truncation quasi-isomorphism),
`sites.tex`, Example 0H7J (constant sheaf), and `sites-modules.tex`, Definition
03CV (module sheaves). Their general assumptions agree with the Lean objects.
No source hypothesis from the unit's more specialized finite-field comparison
is imported into this separate truncation lemma.

Final verification: both delivered sibling modules compile independently through
`scompile.py`, with no errors or warnings. The theorem's only proof is `sorry`;
all definitions have explicit data and the inferred evaluation additivity needs
no new theorem. The node signatures match the source text exactly.

## Returned-delivery repair self-check (2026-10-17)

The return on immutable head `f8fa9a8ca32e` reported duplicate declarations of
`AlgebraicGeometry.ProEtale.IsClassicalModuleSheaf` and
`AlgebraicGeometry.ProEtale.IsClassicalModuleComplex`. The retained repair gives
both declarations exactly one owner, `Sheaf.SixFunctors.ClassicalDefinition`;
`Sheaf.SixFunctors.UnboundedClassicalTruncation` publicly imports that module and
uses its predicates without declaring them. Its node's `lean.declarations` lists
only its five construction helpers and its theorem. The dependency record lists
the three predicates owned by `ClassicalDefinition`. The source signatures and
both declaration inventories were checked again, as were explicit implicit
binding and the 100-character line limit. The theorem and all definition bodies
are retained unchanged from the saved repaired packet.

The current main dependency record now names
module `Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions`, with declaration
`AlgebraicGeometry.ProEtale.IsClassicalModuleFor`, rather than the
older `ClassicalContinuityMap` record described above. I read its current source
through `scompile.py --source`: its predicates require `[CommRing Λ]` and sheaves
valued in `ModuleCat Λ`, whereas this item uses arbitrary finite rings and
intrinsic `SheafOfModules`. The same §1(B) repair remains needed; it reuses the
existing underlying-set `IsClassical` predicate and its affine presentations.
No new mathematical correction or extra dependency is introduced by this repair.

## Second reading by Q73

I independently read the current node and its seven proof steps, both delivered
Lean modules, the blueprint truncation statement and proof, and the classicality
unit's standing coefficient convention. I also read Stacks `derived.tex`, Remark
08J5, `sites.tex`, Example 0H7J, and `sites-modules.tex`, Definition 03CV. These
assume an abelian category or a general ringed site; they impose no geometric
finiteness, nonemptiness or field assumption on this item. The blueprint's
truncation lemma itself allows finite noncommutative rings, independently of
the classicality unit's commutative specialization.

Here is the full object, hypothesis and conclusion checklist against the Lean.

1. An arbitrary scheme X and object W of its small pro-etale site are
   `X : Scheme.{u}` and `W : X.ProEt`. I opened Mathlib's `Scheme.ProEt` and
   `Scheme.ProEt.topology`: their objects are weakly etale schemes over X and
   their topology is the recorded pro-etale precoverage topology. Verdict: exact.
2. The finite unital, possibly noncommutative ring is `A : Type u` with
   `[Ring A] [Finite A]`. There is no `CommRing`, `Nontrivial`, field or
   characteristic hypothesis. Verdict: exact.
3. The constant coefficient ring sheaf A_X is `coefficientRingSheaf X A`,
   constructed by the recorded `constantSheaf` on `RingCat` from `ULift A`.
   `coefficientModules X A` is exactly Mathlib `SheafOfModules` of that sheaf.
   I opened `RingedSiteModules`: its recorded `ringedSiteModules` is a transparent
   abbreviation for the same category, not another notion. Verdict: exact.
4. The unbounded derived category is `DerivedCategory (coefficientModules X A)`.
   Its `HasDerivedCategory` binder specifies a localization; the analogous
   binder for `AddCommGrpCat` specifies the target localization. The
   `Abelian.HasKInjectiveResolutions` binder supplies resolution infrastructure
   available for these Grothendieck module sheaves, not an extra geometric
   condition. Neither complex is required bounded below. Verdict: exact.
5. Evaluation followed by forgetting the action is `evaluationAb X A W`.
   I opened `SheafOfModules.forget`, `PresheafOfModules.evaluation` and the
   corresponding sheaf evaluation definition: the composition is precisely
   section evaluation and forgetting to abelian groups. Additivity is inferred.
   `derivedSections` uses the upstream unbounded `Functor.rightDerivedFunctor`;
   its source definition localizes termwise evaluation on homotopy categories
   and its unit is invertible on K-injectives. The recorded bridge itself was
   read through `scompile.py --source`; its chosen-resolution formulation is
   bounded below and is not used to restrict this unbounded functor. Verdict:
   exact, canonical K-injective derived evaluation.
6. `sectionCohomology X A W q H` applies this functor to
   `DerivedCategory.singleFunctor ... 0` of H, then takes degree-q homology.
   This is exactly the node's definition of H^q(W,H). The node expressly
   permits underlying abelian groups; the functorial construction retains
   scalar linearity before forgetting it. Verdict: exact.
7. Classicality is `IsClassicalModuleSheaf`, defined by the existing
   `IsClassical` of the underlying set sheaf. I opened that predicate, its
   `AffinePresentation` structure, and `continuityMap`: it quantifies over
   every small cofiltered presentation, with affine etale stages, affine
   vertex, and the scheme-over-X limit property, and requires the canonical
   restriction-colimit map bijective. `IsClassicalModuleComplex` applies this
   in every integer homology degree. Verdict: exact.
8. The nonnegative integer bound is `e : ℕ`. `hbound` quantifies over every
   integer q and every coefficient-module sheaf H, requiring classicality
   and `q > e` before asserting `IsZero (sectionCohomology ... q H)`.
   Verdict: exactly the shared hypothesis, with no uniformity omitted.
9. Clause (1) is the first conjunct. It independently binds every L with
   `_hL : IsClassicalModuleComplex L`, every `b : ℤ`, the hypothesis
   `∀ q, b < q → IsZero (H^q L)`, and every m with `b + e + 1 < m`.
   Its conclusion is `IsZero (H^m ((derivedSections ...).obj L))`.
   Verdict: exact bound and quantification; clause (2) does not depend on L.
10. Clause (2) is the second conjunct. For every classical K and integers
    m,N with `N < m - e - 1`, it asserts `IsIso` on degree-m homology of
    derived evaluation of `(TStructure.truncGEπ DerivedCategory.TStructure.t N).app K`.
    I checked the canonical t-structure and truncation API; this is the
    specified arrow K to tau-ge-N K, not an arbitrary comparison map.
    Verdict: exact direction, strict inequality and isomorphism conclusion.

Edge cases: the zero ring and noncommutative finite rings (for example matrix
rings over a finite field), zero sheaves and complexes, the empty scheme,
empty and terminal W, e=0, m=0, negative b,N, and complexes unbounded below
are all admitted. The Postnikov argument's n=0 case is included. Empty
presentation index categories are excluded only by the source's cofiltered
hypothesis, which includes nonemptiness. Site objects are in universe u+1
and morphisms in u; coefficient values and presentation indices are in u+1.
The ULift is a coefficient size lift, not an identification of site object
and morphism universes. Choosing a common universe for X and finite A loses
no mathematical coefficient case; no equality of their intrinsic sizes is
assumed. All variables are explicitly bound, with `autoImplicit false`.

Independent duplicate searches used `msearch.py` with LeanFinder on unbounded
derived evaluation invariant under sufficiently low truncation (eight generic
derived t-structure hits), Loogle on `truncGEπ` (twelve canonical truncation
API hits), and LeanSearch on uniform vanishing of classical pro-etale derived
sections (eight generic sheaf cohomology, homology, limits and unrelated hits).
I also used `rg` on Mathlib, the slopmaster2 `WeilConjectures`, project
`lean/Sheaf`, and `dag/lean_names_upstream.json` for the delivered declaration
names and classical/truncation combinations. None states this lemma or supplies
the arbitrary-ring intrinsic classicality interface. The relevant existing
continuity and generic evaluation/derived/truncation APIs are reused.

For H13 I read the CURRENT published dependency source with
`scompile.py --source Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions`.
`IsClassicalModuleFor`, `IsClassicalCochainComplexFor` and
`IsClassicalComplexFor` take `[CommRing Λ]` and fixed `ModuleCat Λ` sheaves.
The imported intrinsic predicates in `ClassicalContinuityMap` also require
commutative constant coefficients. Neither accepts this item's arbitrary
finite rings. The delivered dependency module therefore remains a necessary
§1(B) repair. Its three predicates reuse the existing set-sheaf continuity
predicate, specialize to the dependency's commutative module/cochain clauses,
and supply the derived formulation without copying presentations or maps.
No new definition node is needed. Its declaration inventory has exactly one
owner for each predicate; the item only imports and uses them.

I found no mathematical mismatch in this retained packet and changed no Lean
statement, definition body, proof route or mathematical node field. The
previous reading's quantifier, inferred-additivity, seven-step proof-docstring,
proof-import and cochain-clause repairs are all present and correct. I did
find a stale `reviewed_lean` field in the sandbox dependency node; I restored
that maintainer-owned field verbatim from the current read-only base. Thus
both delivered nodes differ from the base only in their authorized `lean`
records. There is no `statement_change` or citer audit to validate.

All definitions have explicit construction data, and the sole delivered
theorem has proof `sorry`. Both modules have source/blueprint docstrings;
the theorem docstring carries each of the node's seven proof steps. No local
notation, private declaration, file-local instance or line over 100 characters
occurs. Both `lean.statement` strings were checked verbatim against their
source signatures. Both sibling modules compiled separately through the
required `scompile.py`, with no errors or warnings (2.9 s and 4.9 s for the
library-file checks). Delivery preflight is the final check below.

Final delivery check: `deliver2.py Q73 det-pe-unbounded-classical-truncation
--no-push` printed `OK (dry run)` for commit `8fd375cd76`: server preflight
and both separate file compiles passed; no files were pushed by the dry run.
