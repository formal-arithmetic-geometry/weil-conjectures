## Worker report

`Sheaf.CategoryTheory.ExactFunctorCouple` states
`CategoryTheory.BigradedExactCouple.exactFunctor_couple`. Its only proof is `sorry`.
This completes the earlier attempt by replacing the retired side half-plane import with
published upstream imports, restoring the stated proof-dependency imports, updating the
proof docstring to the current four-step DAG proof, and repairing the exact-couple binding.
The natural-language statement, statement dependencies, proof, and proof dependencies are
unchanged. The independent second reading below is retained with the rejected filtration
rebinding discussion removed, as the return requests.

Hypothesis and clause correspondence:

- The abelian categories are `{C : Type u₁} [Category.{v₁} C] [Abelian C]` and
  `{B : Type u₂} [Category.{v₂} B] [Abelian B]`. All four universes are explicit and
  independent. The exact additive functor is `Φ : C ⥤ B` with `[Φ.Additive]`,
  `[PreservesFiniteLimits Φ]`, and `[PreservesFiniteColimits Φ]`. These are the equivalent
  finite-limit/finite-colimit conditions on exact additive functors of abelian categories.
- The initial couple is `X : BigradedExactCouple C 0`. This is the published upstream
  specialization with precisely the node's alpha/f/g bidegrees. `pageCouple r` denotes
  the mathematical page R = r + 2: its g degree is (r,-r), and its differential degree
  is (r+2,-r-1). Every R >= 2 occurs, including the initial page.
- Clause 1: `∃ Y : BigradedExactCouple B 0`, the object equalities `hD`, `hE`, and
  the initial alpha/f/g squares say that Y is exactly the datum obtained by applying Φ.
  Its exact-couple structure supplies the three zero composites and exactness assertions.
- Clause 2, D subobjects: `δ` compares all iterated D objects. `iX`, `iY` start at the
  identity and recursively compose `derivedDInclusion`; their `Mono` assertions and
  `(δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q)` identify the
  subobjects of the initial mapped D term, rather than just unrelated isomorphic objects.
- Clause 2, couple isomorphisms: `φ` compares all E objects; normalization at r = 0
  is `δ 0 = eqToIso hD`, `φ 0 = eqToIso hE`. The subsequent alpha/f/g squares,
  with their displayed shifted indices, give the isomorphisms of exact couples. The
  differential square explicitly expresses compatibility with d.
- Clause 2, next-page cohomology: `k` is the unique isomorphism of kernels determined
  by its equation with `kernel.ι`. The equation with `derivedEProjection` identifies
  `φ (r+1)` with the induced cohomology comparison; these projections are precisely
  the cokernel projections from cycles modulo boundaries. Thus the comparisons are
  canonical, rather than arbitrary isomorphisms at each page.
- Clause 3 hypotheses: inside `∀ (a : ℤ)`, the two hypotheses are exactly
  `q < a → IsZero (X.D p q)` and `(p < 0 ∨ q < a) → IsZero (X.E p q)`.
  The first two conclusions give the same bounds for Y with the same integer a.
- Clause 3 abutment: `AX`, `AY` are the alpha-diagonal colimits, normalized to
  `X.D 0 n`, `Y.D 0 n` by `hAX`, `hAY` and the identity-at-zero equations. The
  cocone square characterizes `eA` and identifies the abutment with Φ applied to A.
  `imageFiltration` is the image of each cocone map, hence the specified alpha-power
  image for p >= 0; the explicit `p ≤ 0 → step p = ⊤` clauses cover p <= 0.
  `IsFinite` and `ConvergesTo` supply the stated finite abutment and convergence.
- Clause 3 filtration and graded pieces: `τ` and its inclusion square express equality
  of filtration steps as subobjects under `eA`. `κ` and its cokernel-projection equation
  express the induced exact-functor isomorphism on their successive quotients.
- Clause 3 stabilization: the bound is `r + 2 > max (q - a + 1) p`. The two projection
  equations characterize `sX`, `sY`, and their square expresses compatibility with φ.
  `LX`, `LY` are limiting cycle/boundary subobjects; `φInfinity` compares their quotients.
  The stable-cycle equalities and projection equations characterize `eX`, `eY` as the
  canonical stable-page identifications. Their square says φ induces `φInfinity`.
  `ξX`, `ξY` commute with `toPageInfinity` and `toGradedPiece`, so their square is
  compatibility of the canonical infinite-page/associated-graded identifications.
- Clause 3 final square: the bound is `r + 2 ≥ max (p + 3) (q - a + 2)` and the shifted
  D index is `(p-r,q+r)`, exactly `(u,v)` after R = r+2. The inverse-cocone equations
  fix `lambdaX`, `lambdaY` as the stated inverse alpha-power maps. The inclusion
  equations fix `tX`, `tY` as the transported filtration-step identifications. The
  cokernel-projection equations characterize `ψX`, `ψY` as the quotient maps induced
  by g; exactness identifies their kernels with the incoming alpha images. The last
  equation is exactly Φ(ψX) followed by φ = κ followed by ψY, in Lean composition order.

Dependency declarations used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian` (def-sp-abelian).
- `WeilConjectures.CategoryTheory.ExactCouple`: `CategoryTheory.BigradedExactCouple`,
  `derived`, `pageCouple`, `d`, `derivedDInclusion`, `derivedEProjection`
  (def-sp-exact-couple, binding repaired below).
- `def-sp-filtration` retains its canonical recorded declaration
  `CategoryTheory.DecreasingFiltration` in
  `WeilConjectures.CategoryTheory.Abelian.Filtration`, with unrestricted `IsFinite`
  and the filtered-object API in `WeilConjectures.CategoryTheory.Filtration`.
  This theorem accesses its actual filtration steps, finiteness, and graded pieces
  through the already landed `def-sp-convergence` declaration `imageFiltration`.
  That declaration returns the upstream `PBCDecreasingFiltration` interface; its
  owning dependency supplies this interface without rebinding `def-sp-filtration`.
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`:
  `CategoryTheory.BigradedExactCouple.LimitSubobjects`, `AlphaColimit`,
  `imageFiltration`, `ConvergesTo`, `cycleBoundaryTower`, `pageInfinity`,
  `toPageInfinity`, `toGradedPiece`, `limitBoundary_le_cycle` (def-sp-convergence).
- `WeilConjectures.CategoryTheory.HalfPlaneConvergence`:
  `CategoryTheory.BigradedExactCouple.halfPlaneConvergence`
  (thm-sp-half-plane-convergence).
- Proof imports: `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`, supplying
  `CategoryTheory.Functor.preservesHomologyOfExact`, and
  `Sheaf.CategoryTheory.ExactFunctorHalfPlane`, supplying
  `CategoryTheory.BigradedExactCouple.exactFunctor_halfPlane`.

The recorded dependency signatures and docstrings were read, including the live sources
returned by `scompile.py --source` for ExactCouple, ExactCoupleConvergence,
HalfPlaneConvergence, PBCFiltration, Algebra.Homology.ExactCouple.Basic, and
CategoryTheory.Abelian.Filtration. Stacks `homology.tex`, section exact-couple, was read
for the exactness, derived quotient, induced-map, and shifted-couple conventions.

Edge cases: r = 0 gives page 2 and literal identity comparisons. The zero functor and zero
couple remain allowed; no faithfulness or nonzero condition occurs. Integers p,q,a,n are
unrestricted, including negative a and p < 0. Filtration definitions cover p = 0 from
both sides. For n < a the abutment and all graded pieces vanish, so finiteness is still
consistent. Both stable-page inequalities retain their strict/non-strict boundaries.
No infinite-limit existence or equality of category universes is assumed; colimits and
limiting subobjects are conclusions under the half-plane hypotheses.

Searches for an existing theorem:

- `msearch.py ... leanfinder`: "An exact additive functor between abelian categories
  preserves exact couples, their spectral sequence pages, and half plane abutment
  filtrations" returned generic exactness and homology functor results, including
  `Functor.exact_tfae`, `ShortComplex.Exact.map`, and `Ext.mapExactFunctor_hom`;
  no theorem with these exact-couple transport clauses.
- `msearch.py ... loogle`: `CategoryTheory.Functor.preservesHomologyOfExact` found the
  recorded homology-preservation ingredient and unrelated derived-functor results.
- `msearch.py ... grep`: `ExactCouple|exactFunctor_couple` under Mathlib CategoryTheory
  returned no hits. `rg` for `exactFunctor_couple|lem-sp-exact-functor-couple` in
  WeilConjectures and lean/Sheaf found only the withdrawn side declaration and its
  hypercohomology consumer. `grep -rn` for this node id in the old source checkout
  returned no hits. The old checkout lacks the current exact-couple modules, so their
  actual published declarations were read through `scompile.py --source` instead.
- `rg --files` in both named source roots located the general upstream exact-couple
  development; it supplies the general notion but does not replace the specialized
  half-plane transport theorem or its current dependency interfaces.

There is no mathematical statement correction, disputed statement, new definition,
or additional postponed theorem. All declaration variables and universes are explicit.

## Dependency modules

`def-sp-exact-couple`: lean-only repair to existing declaration
`CategoryTheory.BigradedExactCouple` in `WeilConjectures.CategoryTheory.ExactCouple`.
The former binding points to the general all-index `ExactCouple`, but the published
half-plane and convergence modules use this existing shifted-map, type-s specialization
and its own derived-page interface. Its full source signature and docstring match the
node's bidegrees and recursion. This delivery uses that published interface, introducing
no duplicate definition or new dependency module.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and complete Lean signature against Stacks
`homology.tex`, Definitions 12.21.1/12.21.3, Lemma 12.21.2 and the shifted-couple
Remark 12.21.5 (Tags 011Q, 011S, 011R, 0AMJ). The source assumes an abelian
category; it imposes no further finiteness, size, nonzero, or completeness hypothesis.
The source numbers its initial page 1; the node deliberately uses the truncation
convention with initial page 2. I also read Stacks Definition 12.19.1 (0121), the
statement-dependency nodes, and the actual declarations below. The live upstream
sources were read through `scompile.py --source`, since the old source checkout and
the shared side sources contain retired interfaces. There is no repair-note JSON
for this item.

My object/hypothesis/conclusion checklist, with Lean correspondence and verdict:

1. Two arbitrary abelian categories: `{C : Type u₁} [Category.{v₁} C] [Abelian C]`
   and the corresponding B binders. All four universes are independent. **Matches.**
2. An exact additive functor: `Φ : C ⥤ B`, `[Φ.Additive]`,
   `[PreservesFiniteLimits Φ]`, `[PreservesFiniteColimits Φ]`. I opened Mathlib
   `Functor.exact_tfae`: its fourth condition is equivalent to preservation of
   short exact sequences for an additive functor. These hypotheses neither weaken
   nor strengthen exactness. **Matches.**
3. The initial bigraded couple and all derived pages: `X : BigradedExactCouple C 0`
   and `X.pageCouple r`. The actual upstream structure has alpha degree (-1,+1),
   f degree (+2,-1), g degree (s,-s), three zero fields and three image/kernel
   equalities. `derivedD` is the incoming alpha image; `derivedE` is the cokernel
   of the incoming differential lifted to the outgoing kernel. `DerivedMaps`
   specifies all three induced maps by the source's restriction equations;
   `derived` uses their unique data. `pageCouple 0 = X` and successor is derived.
   Thus Lean r denotes node page R = r+2, and covers every R >= 2. **Matches.**
4. Applying Φ gives an exact couple: `∃ Y`, `∃ hD`, `∃ hE` and the first three
   structure-map squares specify precisely the mapped datum, including its
   exactness through Y's structure fields. Equalities of its initial objects are
   realizable by applying Φ literally; they add no condition on X or Φ. **Matches.**
5. Derived D terms equal as subobjects of ΦD: `δ`, the identity-at-zero and
   recursive equations for `iX`/`iY`, their `Mono` clauses, and
   `(δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q)`.
   These are the canonical iterated inclusions, so this states equality of the
   subobjects, not merely abstract isomorphism of their objects. **Matches.**
6. Page comparisons and exact-couple isomorphisms: `φ`, normalization by `eqToIso`
   at r=0, and the alpha/f/g squares. The g target is `(p+r,q-r)`, as required
   on node page R=r+2. The differential square has target
   `(p+2+r,q-1-r)`, hence degree (R,1-R). **Matches.**
7. Next-page comparison is the induced cohomology map: the existential `k` is an
   isomorphism uniquely characterized by its equation with `kernel.ι`.
   The `derivedEProjection` equation then uniquely fixes `φ (r+1)` because this
   projection is the cokernel projection from cycles. This is exactly the
   exact-functor comparison composed with the map on homology. **Matches.**
8. Half-plane assumptions occur only in conclusion clause 3: `∀ (a : ℤ)`,
   `q < a → IsZero (X.D p q)` and `(p < 0 ∨ q < a) → IsZero (X.E p q)`.
   The following two conclusions give exactly those bounds for Y and the same a.
   No such assumption restricts the preceding general transport result. **Matches.**
9. Abutments A^n=D^(0,n) and image filtrations: `AX`, `AY : AlphaColimit`,
   `hAX`, `hAY` and normalization of their zero cocone maps. I read `AlphaColimit`:
   its cocone equation identifies the nonnegative p map with alpha^p after
   normalization, and its universal property is the full diagonal colimit.
   `imageFiltration.step p` is `imageSubobject (A.ι p)`; the explicit top clauses
   cover p<=0, and `IsFinite` gives finite filtrations. `eA` commutes with every
   cocone map and therefore identifies the mapped abutment canonically. **Matches.**
10. Filtration equality and graded comparison: `τ` commutes with step inclusions
    under `eA`, giving equality as subobjects. `κ` commutes with the displayed
    `cokernel.π (Subobject.ofLE ...)`, so it is precisely the isomorphism induced
    on F^p/F^(p+1) by exactness. **Matches.**
11. Adjacent stable pages: `(r : ℤ)+2 > max (q-a+1) p` is exactly the node's
    strict bound in R. `sX`, `sY` satisfy the kernel/projection equations fixing
    the canonical cohomology identifications, and their square commutes with φ.
    **Matches, including the strict endpoint.**
12. Infinite page and its canonical graded identification: `LX`, `LY` are actual
    greatest-lower/least-upper bounds of the finite cycle/boundary subobjects;
    `pageInfinity` is their quotient. The stable-cycle equalities and projection
    equations fix `eX`, `eY`; their square identifies `φInfinity` with stable φ.
    Its equation with `toPageInfinity` and the equations for `ξX`, `ξY` identify
    the canonical weak-convergence maps. `ConvergesTo` includes regularity,
    abutting, and inverse-limit completeness of the image filtration. **Matches.**
13. The final large-page indices and maps: `(r : ℤ)+2 ≥ max (p+3) (q-a+2)`;
    `(p-r,q+r)=(p-R+2,q+R-2)`. The inverse-cocone equations fix `lambdaX/Y`
    as the inverse alpha-power isomorphisms; the `tX/Y` inclusion equations
    identify transported filtration steps with the iterated D images.
    Exactness of each page identifies the kernel of g with the incoming alpha
    image, so the quotient-projection equations for `ψX/Y` specify exactly the
    node's g-induced isomorphisms. The last equation is
    φ_R composed with Φ(ψ_R) = ψ_R^Φ composed with κ, in Lean composition order.
    **Matches, including the non-strict endpoint and all integer p.**

Dependency repairs were independently checked, not accepted from their names.
For `def-sp-exact-couple`, I opened both the former all-index
`CategoryTheory.ExactCouple` declaration and the recorded live
`CategoryTheory.BigradedExactCouple`, including derived/page definitions. The latter
is the same source notion in the exact shifted interface consumed by convergence;
the repair changes only `lean`, with an explanatory note and no private copy.
There are no new definition nodes or dependency modules to audit. The other
statement dependencies were opened: Mathlib `Abelian`, and the live
`LimitSubobjects`, `AlphaColimit`, `imageFiltration`, `ConvergesTo` and
`halfPlaneConvergence`. I also read the actual proof ingredients
`Functor.preservesHomologyOfExact` and the live `exactFunctor_halfPlane` signature;
the latter is only the limiting/large-page portion under already supplied finite
comparisons, so it does not duplicate this item.

Edge cases checked independently: r=0 is exactly page 2, with both comparisons and
inclusions normalized. The zero functor, zero couple and zero abutments are allowed.
For p<0, both adjacent filtration steps are top and the graded piece is zero;
the large-page formula still has its specified maps. For n<a all possible initial
E entries on that diagonal vanish, and the bounded filtration remains consistent.
The same formulas work at p=0 and n=0, for negative a,q,n and at equality in the
non-strict large-page bound. Neither an infinite-limit existence assumption nor a
faithfulness assumption is present. No ring or field, characteristic restriction,
scheme or extra index set is involved. No equation between category universes is
imposed; no smallness, countable completeness or cocompleteness is assumed.

Independent searches (different query from the first worker):

- `msearch.py Q126 lem-sp-exact-functor-couple leanfinder` with
  "Applying an exact functor to a derived exact couple commutes with images and
  homology and the finite abutment filtration": eight hits, including
  `Functor.exact_tfae`, `Functor.preservesHomology_of_map_exact` and Ext maps;
  these are ingredients, not this theorem.
- The same wrapper with `loogle '"BigradedExactCouple"'`: zero hits.
- The wrapper's `grep 'preservesHomologyOfExact|exact_tfae'` found the expected
  Mathlib ingredients. Direct `rg` for `exact couple`, `BigradedExactCouple`,
  `mapTriangulatedSpectralObject`, `mapTriangulatedFunctor` in Mathlib,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`
  found the spectral-object framework, specific consumers and the retired side
  version of this very module. I opened the latter: it uses withdrawn imports,
  and the node records its upstream-sync elaboration failure; it is not a usable
  existing binding. The published general exact-couple framework was searched as
  well; it does not supply this exact transport/filtration statement.

No mathematical mismatch was found in this completed worker delivery. I changed
only this report by adding the independent reading; the correct Lean signature and
the justified exact-couple dependency repair was retained. The module has one theorem,
`exactFunctor_couple`, with exactly `sorry`; it introduces no definitions or axioms.
The source/blueprint docstrings include all four current DAG proof steps and their
named dependencies. Imports have the required statement/proof visibility, there
are no file-local notations or instances, all lines are at most 100 characters, and
`autoImplicit false` leaves no variable or universe unbound. A parsed comparison
confirmed that `lean.statement` is verbatim the full source signature, and only
`lean` changes on each delivered node. The prescribed `scompile.py Q126
lem-sp-exact-functor-couple lean/Sheaf/CategoryTheory/ExactFunctorCouple.lean`
passed both sandbox and library compilation cleanly (1.9 s and 1.8 s), without
errors or warnings. No statement correction or citer audit is required.

## Returned-delivery repair

The return for immutable head `dc95a2036c97` identified H13 (with H4/H2):
`def-sp-filtration` already has the usable canonical `DecreasingFiltration` binding,
including unrestricted `IsFinite` and `FilteredObject`. Removed its sandbox node
from this delivery, so its binding on `newtargets-dag` is preserved, and removed
the rebinding paragraphs from Dependency modules and the retained second reading.
The theorem reaches the PBC interface only through the landed `imageFiltration`
of `def-sp-convergence`; the accepted Lean module and signature are unchanged.
The accepted `def-sp-exact-couple` specialization repair remains.

Repair validation on 2026-10-17: compared both retained sandbox node files with
the current shared repository; each differs only in `lean`. No sandbox node file
for `def-sp-filtration` remains. The canonical binding on the current base is
`CategoryTheory.DecreasingFiltration`, and neither Dependency modules nor Second
reading contains the rejected rebinding argument. Rechecked that `lean.statement`
matches the full theorem signature verbatim. A fresh prescribed `scompile.py`
run passed both sandbox and library compilation (1.6 s and 1.8 s), with no errors
or warnings. The dry run below rebuilds the repaired delivery on the current base.

Repair retry: rechecked the retained work against the current base on 2026-10-17.
The sandbox contains exactly the item node and the accepted exact-couple dependency
node; neither changes any field outside `lean`. Read the canonical filtration
structure and its `IsFinite` and `FilteredObject` extensions directly: `IsFinite`
allows arbitrary integer top and bottom endpoints. The rejected replacement is
absent, and the earlier second reading contains no argument for it. The accepted
Lean module remains unchanged, as explicitly requested in the return.

## Second reading by Q126

Fresh independent reading on 2026-10-17. I read the current sandbox node and full
Lean declaration against Stacks `homology.tex`, section `section-exact-couple`,
Definitions 12.21.1/12.21.3, Lemma 12.21.2 and the shifted variant 12.21.5
(Tags 011Q, 011S, 011R, 0AMJ), and Definition 12.19.1 (0121).
These places assume abelian categories and no ambient infinite limits or extra
size hypotheses. The node uses initial page 2 rather than Stacks' initial page 1.
There is no `statement_change` and no repair-note JSON for this item.

Object, hypothesis and conclusion checklist:

1. Arbitrary abelian source and target: `{C : Type u₁} [Category.{v₁} C]
   [Abelian C]` and the corresponding B binders. All four universes are bound
   independently. Mathlib's `Abelian` supplies exactly the required structure.
   Verdict: matches; no size equality, smallness or completeness assumption.
2. Exact additive functor: `(Φ : C ⥤ B) [Φ.Additive]
   [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]`. I opened Mathlib
   `Functor.exact_tfae`: these conditions are equivalent to preservation of short
   exact sequences for an additive functor. Verdict: matches, without faithfulness.
3. Initial couple and iterates: `(X : BigradedExactCouple C 0)`,
   `X.pageCouple r`. I opened the live upstream structure, its zero and exactness
   fields, `derivedD`, `derivedE`, `DerivedMaps`, its subsingleton instance,
   `derived`, and `pageCouple`. The initial degrees are (-1,1), (2,-1), (0,0);
   each derivation increases the g degree by (1,-1). The maps are uniquely fixed
   by their restriction/projection equations, not arbitrary chosen data.
   Verdict: matches with mathematical page R = r+2, including R=2.
4. Clause 1: `∃ Y`, object equalities `hD`, `hE`, and the initial alpha/f/g
   squares specify applying Φ to all entries and maps; Y's fields assert the
   resulting datum is exact. These existential equalities can be realized by
   taking the literal mapped objects. Verdict: matches, no extra hypothesis.
5. Clause 2, equality of D subobjects: `δ`, `iX`, `iY`, their initial identity,
   successor inclusion equations, monicity, and the square with `eqToHom hD`.
   The recursive inclusions are exactly the iterated images inside the initial
   D terms. Verdict: matches equality as subobjects, beyond abstract isomorphism.
6. Clause 2, all page comparisons: `φ`, normalization by `eqToIso hE` at r=0,
   and the alpha/f/g squares give the isomorphisms of exact couples. Targets
   `(p+r,q-r)` for g and `(p+2+r,q-1-r)` for d are the node's degrees under
   R=r+2. Verdict: matches each structure map and the differential square.
7. Clause 2, induced cohomology comparison: `k`, `IsIso k`, the `kernel.ι`
   equation and the `derivedEProjection` equation specify precisely the induced
   next-page map. The first equation uniquely fixes k by the monic inclusion;
   the second fixes the successor comparison by the epimorphic cokernel
   projection from cycles. Verdict: matches canonicality, not just existence.
8. Clause 3 assumptions: `∀ (a : ℤ)`, followed by
   `q < a → IsZero (X.D p q)` and
   `(p < 0 ∨ q < a) → IsZero (X.E p q)`. The next two conjuncts give exactly
   these bounds for Y at the same a. Verdict: matches; the half-plane conditions
   restrict only clause 3, not the general transport in clauses 1 and 2.
9. Clause 3 abutments: `AX`, `AY : AlphaColimit`, `hAX`, `hAY` and the equations
   for `ι 0` normalize their objects and maps to D(0,n). I opened `AlphaColimit`:
   its consecutive-arrow universal property is the full diagonal colimit.
   `eA` commutes with every cocone map. `imageFiltration.step` is precisely the
   image of that map, hence alpha^p for p>=0 after normalization. Explicit
   p<=0 top clauses and `IsFinite` give the prescribed finite filtration;
   `ConvergesTo` gives regularity, weak convergence, separatedness,
   exhaustiveness and the inverse-limit condition. Verdict: matches.
10. Clause 3 filtration/graded transport: `τ` and its square with subobject
    arrows identify steps inside the abutment; `κ` and the equation with
    `cokernel.π (Subobject.ofLE ...)` identify the induced maps of successive
    quotients. Verdict: matches both the subobjects and canonical quotient maps.
11. Clause 3 stabilization: `(r : ℤ)+2 > max (q-a+1) p`, `sX`, `sY`, their
    kernel/projection equations, and the square with φ give the exact canonical
    adjacent-page identifications. Verdict: matches the strict endpoint.
12. Clause 3 infinite page: `LX`, `LY : LimitSubobjects` are actual greatest
    lower/least upper bounds of the cycle/boundary towers. `pageInfinity` is
    their quotient. `φInfinity`, the stable-cycle equalities `hZX/hZY`, and
    projection equations for `eX/eY` identify it with stable finite-page φ.
    `ξX/ξY` commute with `toPageInfinity` and `toGradedPiece`, and their last
    square gives compatibility with κ. Verdict: matches the canonical limit
    and associated-graded identifications.
13. Clause 3 final comparison: `(r : ℤ)+2 ≥ max (p+3) (q-a+2)` has exactly the
    non-strict endpoint; `(p-r,q+r)` is node `(u,v)` after R=r+2. The inverse
    cocone equations characterize `lambdaX/Y`; the equations with `iX/iY`
    characterize `tX/tY` as the transported image identifications. The equations
    with the graded cokernel projections characterize `ψX/ψY` as induced by g.
    Their last square is Φ(ψX) followed by φ = κ followed by ψY, the node's
    equality in Lean composition order. Verdict: matches.

Dependency and return audit: I obtained live sources using `scompile.py --source`
for ExactCouple, the general Algebra.Homology.ExactCouple.Basic,
ExactCoupleConvergence, HalfPlaneConvergence, PBCFiltration,
CategoryTheory.Abelian.Filtration, CategoryTheory.Filtration and
Sheaf.CategoryTheory.ExactFunctorHalfPlane. I read the actual signatures of
`LimitSubobjects`, `AlphaColimit`, `imageFiltration`, `ConvergesTo`,
`halfPlaneConvergence`, and `exactFunctor_halfPlane`, not merely their names.
The last theorem assumes the finite-page and filtration comparisons, so does
not supply this whole theorem. The exact-couple lean-only dependency repair
uses the published shifted/type-s interface consumed by convergence; it states
the dependency's actual notion and adds no new definition or module.

The current return for head dc95a2036c97 requests removal of the filtration-node
rebinding and explicitly accepts the module and exact-couple dependency repair.
The sandbox has no def-sp-filtration node: the canonical DecreasingFiltration
binding remains untouched. Its unrestricted IsFinite and FilteredObject are
present in CategoryTheory.Filtration; there is no unusability claim or proposed
replacement. This item's imageFiltration already returns the PBC interface via
the landed convergence dependency. There are no new definition nodes or sibling
dependency modules. Comparison with the current shared base shows only `lean`
changes in the two retained node files.

Edge cases: r=0 is mathematical page 2 with identity comparisons. Zero couples,
zero objects and the zero exact functor are allowed. Every integer p,q,n,a is
unrestricted, including n=0 and negative bounds. At p=0 the two filtration
conventions agree; for p<0 adjacent steps are top and the graded piece is zero.
For n<a the abutment is zero. Both strict and non-strict stabilization endpoints
are retained. No independent indexing set, scheme, characteristic or coefficient
ring occurs. There are no extra infinite-limit or universe restrictions.

Independent searches in this reading:

- `msearch.py ... leanfinder` with "Exact functors commute with the derived
  couple of a spectral sequence and its abutment image filtration": eight hits,
  concerning Ext maps, localization and preservation of homology. None states
  the transport of exact couples and their canonical filtration comparisons.
- `msearch.py ... loogle '\"BigradedExactCouple\"'`: zero hits.
- `msearch.py ... grep 'preservesHomologyOfExact|exact_tfae'`: sixteen hits,
  including the two actual Mathlib ingredients, whose declarations I opened.
- Direct rg for exact-couple transport and spectral-sequence map terminology in
  Mathlib's SpectralObject framework, the named upstream checkout, and shared
  lean/Sheaf found ingredients, consumers and the retired version of this very
  module. I opened that version: it imports the withdrawn side interfaces and
  has the older six-step proof documentation. It is not a usable existing
  replacement for the repaired declaration. No duplicate theorem was introduced.

No mathematical mismatch was found, so I retained the Lean source and both node
records unchanged and appended this reading only. There is one theorem with
exactly `sorry`, no definitions or added axioms, and no file-local notation or
instance. The module and theorem docstrings cite the source and blueprint and
carry all four current proof steps. All lines are <=100 characters, all variables
and universes are explicitly bound, and a literal comparison confirmed that
`lean.statement` equals the complete source signature verbatim.

Current validation: a fresh prescribed scompile run reached an infrastructure
failure (exit 75): the published live build predates or lacks the matching live
ExactCouple module. The precise import error is that
Sheaf.CategoryTheory.ExactCoupleShifted introduces
`CategoryTheory.BigradedExactCouple.mk.noConfusion` already present from
WeilConjectures.CategoryTheory.ExactCouple. A second run through the wrapper's
supported local route failed identically, and its server confirmation reproduced
the same error. This is a mixed published dependency environment; the accepted
statement is unchanged. No live files or artifacts were edited.

The subsequent `deliver2.py --no-push` compilation passed: it compiled the item
and the existing-declaration probe together, each separately in sandbox and library
positions, then advanced to worktree allocation. Thus the delivery wrapper's full
overlay resolves the standalone mixed-artifact failure above; no Lean edit was
needed. Its existing-declaration probe checks the rebound exact-couple interface.
