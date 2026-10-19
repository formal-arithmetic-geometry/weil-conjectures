## Worker report

This delivery states `lem-trf-open-square-exchange` in
`Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`, with primary declaration
`AlgebraicGeometry.Scheme.proEtale_openSquareExchange`. The single theorem has proof
`sorry`; every other declaration is an explicit construction or the structure specifying
exactly the coherent isomorphisms asserted by this node. No proof is supplied in stage 2.
The node statement, proof, dependency lists and source are unchanged. Q38's previous
review/merge was the stage-1 split, not a Lean statement: the base node has no `lean` record.
The earlier worker's split/preflight refusal therefore does not supersede this stage-2 task.

Hypothesis and clause correspondence:

- The coefficient ring is exactly `Padic.coefficientExtensionRing l E n`, the ring used by
  the recorded finite-torsion constructibility definition. The binders `l : ℕ`,
  `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`, `n : ℕ`, `hn : 1 ≤ n` give its recorded finite-level
  construction, including the chosen integer ring and uniformizer. The existing theorem
  `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness explicitly; the
  conclusion does not ask for any new coefficient identification or finiteness assumption.
  As in the intrinsic constructibility dependency, there is no unused global finite-field
  datum. The statement concerns these coefficients on arbitrary schemes.
- The four corners are `U' U Y' Y : Scheme.{u}`, and the four arrows are
  `gU : U' ⟶ U`, `j' : U' ⟶ Y'`, `j : U ⟶ Y`, `g : Y' ⟶ Y`.
  `IsPullback gU j' j g` is the Cartesian-square hypothesis, including exactly
  `gU ≫ j = j' ≫ g`. Both vertical open immersions are explicit instances
  `[IsOpenImmersion j] [IsOpenImmersion j']`. No affine, Noetherian, proper or etale
  condition on the horizontal arrows is introduced.
- The small sites and scalar category are precisely the published
  `Scheme.ProEt.topology`, `proEtaleRingModules X (proEtaleConstantRing X A)` and
  `proEtaleDerivedCategory X A`. No condensed, continuous-function-ring or completed
  coefficient category replaces these intrinsic categories. Module values are in universe
  `u+1`, with the coefficient lift already fixed by the recorded intrinsic realization.
- `sfIntrinsicDerivedOpen A j` is the exact termwise derivation of the recorded
  `sfIntrinsicExtensionByZero j A`. `sfIntrinsicDerivedPullback A g` is exact termwise
  inverse image in the same intrinsic category, supplied by the dependency repair below.
  Both operate on the full, possibly unbounded derived categories. There is no
  constructibility or boundedness hypothesis on their arguments.
- `SfOpenSquareExchangeData.exchange` has type
  `sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
   sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j'`.
  In Lean functor-composition order this is exactly `Lg^* j_! ≅ j'_! Lg_U^*`.
  The theorem asserts `Nonempty` of the structure containing this family and all the laws.
  Existence of the single coherent family also makes the pasting clauses meaningful for
  different squares, rather than selecting unrelated pointwise isomorphisms.
- Canonicity is substantive: `canonical` fixes the inverse to
  `sfIntrinsicDerivedOpenMate A gU j' j g sq.w`. That map is explicitly constructed from
  the open unit, the canonical commuting-pullback comparison, and the open counit, then
  descended termwise through localization. It is not an unconstrained map or a choice
  of an arbitrary isomorphism. Inverses of this fixed map are unique. The square comparison
  uses the existing fixed-scalar `upperStarComp` comparisons, themselves obtained from
  direct-image composition; it is the usual pullback identification in the node's proof.
  This is the inverse mate of the direct-image restriction comparison specified there.
- `restriction` says, for every `K : proEtaleDerivedCategory U A`, that applying `g_U^*`
  to the open unit, then the pullback identification, then `j'^*` of `b_g(K)`, equals the
  open unit at `g_U^* K`. The two open units are the canonical isomorphisms identifying
  restriction of extension by zero with the original complex. Thus the equation is
  exactly that the restricted comparison is the identity under those identifications.
- `horizontal_id` gives the exchange for `g = id`, `gU = id` using the canonical derived
  pullback identity comparisons. `vertical_id` gives the case `j = id`, `j' = id` using
  the open-extension identity comparisons. Identity arrows and arbitrary choices of
  Cartesian witnesses are covered, not excluded.
- `horizontal_pasting` handles `Y'' → Y' → Y` and their pulled-back opens. Its right side
  expands outer pullback using `sfIntrinsicDerivedPullbackComp`, then applies `b_g`
  followed by `b_h`, then collapses the top pullback composition. It equals the outer
  exchange. The `outer` binder is an arbitrary proof of the pasted Cartesian square,
  not an extra geometric hypothesis: the two inner Cartesian squares imply it.
- `vertical_pasting` handles nested opens `V → U → Y` and `V' → U' → Y'`. It expands the
  outer open extension by `sfIntrinsicDerivedOpenComp`, applies the lower then upper
  exchange, and collapses the primed open extension. The composition comparison is
  constructed by uniqueness of left adjoints with the composite units, matching the
  comparison specified in the node. Again the outer Cartesian witness is arbitrary.

Dependency declarations inspected and used:

- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`; its signature and body
  fix the same finite-level coefficient ring and intrinsic derived category. Its finite
  coefficient construction comes from `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties` is a convention node, with no notion of its own.
  Its open-immersion entry points to Mathlib's `AlgebraicGeometry.IsOpenImmersion`, the
  morphism property inherited from locally ringed spaces; no replacement is defined.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and universal property were read.
  `IsPullback` expresses the same property for any supplied square, not only the chosen
  pullback object, so arbitrary Cartesian squares are retained.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` is the standard derived localization
  of intrinsic constant-ring module sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` is exactly Mathlib's `SheafOfModules`, with its
  existing abelian structure; no chosen abelian instance is constructed.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` and
  `AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence` are used verbatim. Their
  middle functor is the upstream fixed-scalar left Kan extension and sheafification.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedDirectImage` and its exported
  operations were inspected; the missing intrinsic canonical pullback is repaired below.
  The original interface is publicly retained, not overwritten or restricted.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `ProEtale.openImmersionLowerShriekUpperStarAdjunction` supplies the actual open
  adjunction. `UpperLowerStar.Defs` supplies `upperStar`, `upperStarComp`, `upperStarId`.
  Their full signatures and docstrings were read, including exactness and the adjoint
  construction of composition. All coefficient categories have the required universe.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`, and
  `mapDerivedCategoryIdIso` are the canonical localization comparisons; natural maps
  descend by `Localization.liftNatTrans`, exactly as in the existing iso construction.

The already stated proof-dependency modules are imported: constant exactness, weakly etale
localization, inverse image, open-extension adjunction and exactness, and the ordinary
operations interface. The remaining abstract proof nodes have no module records yet;
the construction uses their existing Mathlib/upstream categorical operations, and their
proof descriptions are retained in the theorem docstring and DAG proof unchanged.
No new postponed helper theorem is introduced.

Edge cases checked before finalizing: empty schemes and empty opens; identity open
immersions; identity horizontal maps; arbitrary horizontal maps; two successive base
changes; nested opens; arbitrary, including zero and unbounded, complexes; `n = 1`;
and the impossibility of `n = 0` under the source's `hn`. The generic transport helpers
also permit the zero coefficient ring. No stalk detection, constructible restriction,
or independent smaller scheme/index universe is introduced. Both explicit open hypotheses
are harmlessly redundant when one follows from base change, but are exactly those in the
node. All variables and universes are explicitly bound (`autoImplicit false`).

Searches performed with `msearch.py NJ lem-trf-open-square-exchange`:

- LeanFinder: “Inverse image commutes with extension by zero in a cartesian square of
  open immersions on pro etale sheaves, naturally and compatibly with composition”.
  Eight hits, involving sheafed-space open-immersion section formulas and Zariski module
  restriction. None states this pro-etale exchange, normalization and coherence.
- Loogle: `CategoryTheory.Adjunction.leftAdjointUniq, CategoryTheory.conjugateEquiv`.
  Zero hits for this combined query. The generic adjunction APIs were inspected directly;
  they do not already assert the item.
- Mathlib grep: `openImmersion.*[Bb]ase[Cc]hange|openSquareExchange|open_square_exchange`.
  One hit, `Mathlib/AlgebraicGeometry/OpenImmersion.lean:842`, the stability of open
  immersions under base change; no exchange isomorphism.
- LeanSearch: “inverse image commutes with extension by zero along an open immersion
  of a site”. Service unavailable, Internal Server Error; no absence inference is made.
- Direct `rg` in the slopmaster2 project's `WeilConjectures` and the shared `lean/Sheaf`
  found no declaration of this exchange/coherence. `grep -rn` for the exact node id in
  upstream `WeilConjectures` returned no hit. Searches for `sfIntrinsicPullback`,
  `sfIntrinsicTransport`, `sfIntrinsicOpenMate`, and `SfOpenSquareExchangeData` found no
  existing names. The generic phrase search found etale base-change/open-square lemmas,
  which concern other sites and maps. The shared reports explicitly distinguish their
  etale clauses from this pro-etale node.
- Searches for intrinsic pullbacks and `sfIntrinsicModuleEquivalence` found the recorded
  extension-by-zero transport but no canonical intrinsic pullback/composition interface.
  The published scalar realization and fixed-scalar functors were reused, not copied.

Source check: read Stacks https://stacks.math.columbia.edu/tag/03S6 and
https://stacks.math.columbia.edu/tag/04J0. The first gives the inverse-image/open-extension
exchange via direct-image localization and adjunctions; the second gives that localization
identity for ringed sites. The full local blueprint Markdown is absent from this read-only
checkout, as Q38's report already records. The node preserves its complete blueprint
statement and detailed six-step pro-etale/unbounded/coherence proof, which is followed here.
The proof docstring carries that complete argument for stage 3. No statement correction,
new node, or `STATEMENT-DISPUTED` is needed.

Validation: both modules are compiled separately in dependency order through `scompile.py`.
The delivery dry run is required after the final metadata and warning repair. No global
build, direct Git command, shared-repository edit, or push is performed by this worker.

## Dependency modules

`def-weil-pbc-proetale-operations` receives the §1(B) module
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`, primary declaration
`AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback`. The old module specializes the
identified-coefficient interface to the continuous-function RingCat sheaf at coefficient
universe `u+1`. It does not expose the canonical inverse image on the intrinsic constant
CommRingCat-sheaf modules at `proEtaleDerivedCategory`, the category actually used by the
item and its extension-by-zero dependency. The new module publicly imports and retains the
old interface and supplies exactly this missing constant-coefficient specialization.
`sfIntrinsicPullback` is the existing `ProEtale.upperStar` conjugated by the existing
`sfIntrinsicModuleEquivalence`; its composition and identity comparisons insert the
realization unit/counit. Its additive and exact instances are inherited from those actual
functors; its derived functor is `mapDerivedCategory`. No map, equivalence, coefficient
identification, resolution system or extra assumption is chosen independently. The
copied dependency node changes only `lean`, with the required explanatory `lean.note`.

## Second reading by NJ

I independently read the base and sandbox nodes, both delivered modules, every statement
dependency's statement and recorded signature, and the actual declarations underlying the
coefficient ring, site, intrinsic module category, realization, extension by zero and
fixed-scalar inverse image. The sandbox changes only the two nodes' `lean` fields. There
is no `statement_change`, no new node, and no change to a target or unit statement.

Source check: the local literature checkout contains the literature lists but neither the
Stacks `.tex` files nor the blueprint Markdown. I read Stacks Tags
[03S6](https://stacks.math.columbia.edu/tag/03S6) and
[04J0](https://stacks.math.columbia.edu/tag/04J0), and retrieved and read the corresponding
`lemma-shriek-base-change` and `lemma-localize-morphism-ringed-sites` passages directly
from the Stacks project's upstream `etale-cohomology.tex` and `sites-modules.tex`.
03S6 assumes an arbitrary morphism of schemes and an etale localization; it imposes no
Noetherian, quasi-compact, separated, characteristic or base-field condition. An open
immersion is the localization used here. 04J0 specifies the induced ring map and the
direct-image/restriction identity. The node explicitly supplies the further pro-etale,
unbounded-derived, normalization and coherence argument. I checked all six proof steps
against the theorem docstring and the constructions, rather than attributing these further
clauses to 03S6 alone. The blueprint Markdown could not be retrieved at its recorded
repository path; the node's full statement and six-step proof are available and unchanged.

My item-by-item list and verdicts:

1. **Finite coefficient ring `A = A_{E,n}`.** The theorem binds `l : ℕ`,
   `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`, `n : ℕ`, and `hn : 1 ≤ n`.
   Its conclusion instantiates `SfOpenSquareExchangeData` with
   `Padic.coefficientExtensionRing l E n` and the existing
   `Padic.finite_coefficientExtensionRing l E n hn`. I opened the coefficient construction:
   it is the quotient by the power of the recorded uniformizer, not an arbitrary finite
   ring substituted for that quotient. These are the coefficient parameters of the
   recorded `intrinsicFiniteTorsionConstructible` dependency. No global finite-field
   datum, characteristic condition or constructibility predicate is needed by this node.
   Verdict: exact coefficient and hypotheses.
2. **Square and objects.** `exchange` quantifies over all four `Scheme.{u}` corners
   `U' U Y' Y`, arrows `gU j' j g`, instances `[IsOpenImmersion j]` and
   `[IsOpenImmersion j']`, and `sq : IsPullback gU j' j g`. I checked Mathlib's
   pullback and `IsPullback` interfaces: `sq.w` is `gU ≫ j = j' ≫ g`, and the
   remaining field is the universal property. The square need not be literally Mathlib's
   chosen pullback object. Neither horizontal arrow receives a geometric restriction.
   Verdict: all and only the node's geometric hypotheses.
3. **Small pro-etale sites and coefficient categories.** The actual
   `proEtaleDerivedCategory` is the unbounded derived localization of
   `SheafOfModules.{u+1}` over the constant commutative ring sheaf, with `ULift` of the
   scalar ring. `proEtaleRingModules` and `proEtaleConstantRing` in the functor types
   give this same category. I read the intrinsic realization: it extends the fixed scalar
   action along the canonical constant-sheaf unit and uses module sheafification.
   `sfIntrinsicModuleEquivalence` is its equivalence, using the existing exact-equivalence
   theorem. Verdict: same sites and modules, with no condensed-coefficient substitution.
4. **Functors and the isomorphism.** `sfIntrinsicDerivedOpen A j` derives the recorded
   `sfIntrinsicExtensionByZero j A` termwise. `sfIntrinsicDerivedPullback A g` derives
   the exact fixed-scalar inverse image transported through the same realization.
   `exchange` is a natural isomorphism
   `sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
   sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j'`.
   Reading `⋙` in application order gives precisely `Lg^* j_! ≅ j'_! Lg_U^*`.
   `Nonempty` asserts existence of the whole coherent family. It does not replace an
   individual natural isomorphism by a pointwise existence assertion. Verdict: every
   complex and every square are covered, with the correct direction and naturality.
5. **Canonicity.** `canonical` fixes `exchange.inv` to
   `sfIntrinsicDerivedOpenMate A gU j' j g sq.w`. I checked the unit insertion, the
   square comparison and the counit contraction in `sfIntrinsicOpenMate`, including
   their order. The pullback-square isomorphism uses the existing `upperStarComp`
   comparisons, which are defined by conjugating the sectionwise direct-image
   composition. This is the specified mate of the direct-image localization comparison;
   its inverse is the node's `b_g`. The derived map is its termwise localization with
   the canonical composition comparisons. Verdict: the canonical map is fixed, and
   inverses of that map are unique. The family packaging adds no choice of unrelated
   isomorphisms and no additional mathematical conclusion.
6. **Restriction is the identity.** For every `K`, `restriction` first applies `gU^*`
   to the unit `K → j^*j_!K`, uses the canonical square identification, and applies
   `j'^*` to `exchange.hom.app K`. The result equals the primed unit at `gU^*K`.
   Under the invertible open units, this says exactly that the restricted comparison
   is the identity. I checked the open-unit result's actual upstream signature, and the
   open adjunction used here is its canonical transport. Verdict: exact normalization,
   not merely equality of isomorphism classes.
7. **Identity squares.** `horizontal_id` handles `gU = 𝟙 U`, `g = 𝟙 Y` using
   the derived pullback identity isomorphisms. `vertical_id` handles `j = 𝟙 Y`,
   `j' = 𝟙 X` using the open-extension identity isomorphisms. Those comparisons
   come from the specified adjunctions, not arbitrary equivalences. Both equations
   quantify over every Cartesian witness. Verdict: both identity cases are retained.
8. **Pasting.** `horizontal_pasting` compares the exchange for `h ≫ g` and
   `hU ≫ gU` with applying the `g` exchange and then the `h` exchange, using the
   correct pullback composition isomorphisms at both ends. `vertical_pasting` expands
   `(i ≫ j)_!`, applies the `j` exchange followed by the `i` exchange, and contracts
   `(i' ≫ j')_!`. `sfIntrinsicOpenComp` is defined by uniqueness of left adjoints
   with the composite units, just as the proof specifies. The explicit `outer`
   witnesses are implied by the two inner Cartesian squares; quantifying over them
   omits no pasted square and makes no extra geometric assumption. Verdict: both
   pasting clauses, with the prescribed identifications and order.

Dependency repair (H13): I read the full existing operations interface. Its
`finiteCoefficientDerivedPullback` acts on `FiniteCoefficientDerivedCategory`, whose
coefficients are the sheafified continuous-function ring, at scalar universe `u+1`.
It cannot directly be used as an end point in the intrinsic categories of the recorded
extension-by-zero dependency. The delivered operations module publicly retains the old
interface and constructs exactly the missing intrinsic specialization. In particular,
`sfIntrinsicTransportComp` inserts the middle realization unit and
`sfIntrinsicPullbackId` uses the realization counit. All data are actual composites of
the recorded functors and equivalence maps. There is no hollow definition, arbitrary
coefficient isomorphism, altered ring, or postponed helper theorem. The dependency node
changes only `lean` and explains this interface repair in `lean.note`. No independent
missing notion requires a new definition node.

Independent H4 searches used different terminology from the first worker:

- LeanFinder through `msearch.py`: "Beck Chevalley base change for shriek of an open
  subtopos and inverse image, including coherence". Eight hits, all general sheaf
  pullback/adjunction or sheafification APIs; no matching theorem.
- Loogle through `msearch.py`: `CategoryTheory.Adjunction.leftAdjointUniq` returned
  twelve generic uniqueness/compatibility results. I opened the actual API; it supplies
  the composition helper but does not state this node. A query for the project's
  `CategoryTheory.Functor.mapDerivedCategoryNatIso` was unknown to that search index;
  I instead read its imported upstream source directly.
- LeanSearch through `msearch.py`: inverse image of extension by zero in a Cartesian
  square. The service returned Internal Server Error; this is not evidence of absence.
- `msearch.py` grep for `Beck.Chevalley|shriek.*[Ee]xchange|[Ee]xchange.*shriek` found
  only the three generic Mathlib mates/comma-category files. Independent `rg` on
  Mathlib, the slopmaster2 project, shared `lean/Sheaf`, and the newer shared
  `lean/WeilConjectures` also used base-change, Beck-Chevalley and lower-shriek terms.
  Searches for every new `sfIntrinsic` name and `SfOpenSquareExchangeData` found no
  pre-existing declaration in those libraries.

The broader shared-source search found a **partial match omitted from the worker's
description**: `ProEtale.openImmersionLowerShriekBaseChangeMap` and
`ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso` in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange`.
I opened that entire module and its weakly-etale-base-change dependency. It gives the
same exchange clause on fixed-scalar sheaves, but neither the restriction-normalization
equation nor either identity or pasting clause. Thus it is not an exact existing
declaration of this node. Its imports also use the legacy pro-etale definitions rather
than the finite-coefficient modules used by the intrinsic dependency. The delivered
mate is the intrinsic transport expressed using the existing finite-coefficient
adjunction/composition APIs, not a replacement definition of extension by zero or
inverse image. The module-object lower-shriek exchange in the 51-module framework was
also inspected: it is over condensed rings on bounded constructible categories with
finite-type/field hypotheses, and is not this node's coefficient category or scope.

Proof imports: every recorded proof-dependency module is imported, directly or publicly
through a statement dependency. The abstract adjunction, conjugation, Yoneda and
localization dependencies are Mathlib leaves. The open-unit record lists its upstream
declaration without a module record; I inspected the legacy `FullyFaithful` source rather
than importing the conflicting legacy definitions into this finite-coefficient module.
The proof docstring records its use and all six steps, including scalar linearity,
both Hom-bijection pasting arguments, and exact descent on unbounded complexes.

Edge cases: empty schemes and empty opens are included by unrestricted `Scheme` and
open-immersion binders; zero and arbitrary unbounded complexes are included by the full
derived category. There is no index set or implicit nonemptiness assumption. Identity
maps and nested opens are explicitly included by the corresponding fields. `n = 1` is
allowed; `n = 0` is outside the recorded `A_{E,n}` convention (`n ≥ 1`), so it is not
silently discarded. There is no characteristic hypothesis on schemes and no assumption
that `l` be invertible on them. The generic helpers even admit the zero coefficient
ring. The site has object universe `u+1` and morphism universe `u`; modules use `u+1`
and the coefficient lift, without forcing those site universes equal. All declarations
bind their variables, and `autoImplicit false` is set. The recorded signatures occur
verbatim in their files. Lines are at most 100 characters. Exactly one new theorem is
postponed, `proEtale_openSquareExchange`; the dependency module contains no `sorry`.

Changes after second reading: expanded and corrected the search audit to disclose and
evaluate the legacy partial match, and added this hypothesis/clause/source/dependency
reading. No mathematical or Lean correction was necessary; the modules and their
verbatim `lean.statement` records are retained.

Validation after this reading: `scompile.py NJ lem-trf-open-square-exchange` compiled
both delivered sibling modules separately in dependency order, including sandbox and
library-name checks, with exit status 0 and no warnings or errors. The wrapper's normal
60-second Lean limits were used throughout; elapsed queue waits do not change those limits.
