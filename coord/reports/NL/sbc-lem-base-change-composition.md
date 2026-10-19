## Worker report

The module Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition states both clauses of
sbc-lem-base-change-composition, with sorry proofs and the four-step natural-language
proof in the declaration docstrings. The source was read at etale-cohomology.tex,
lemma-base-change-compose (Stacks 0EZS), together with the node's expanded 0E47 argument.
No statement correction, new node, or dependency repair is needed.

Hypothesis and conclusion correspondence:

- The six schemes W, Z, X, Y, S, T and seven arrows j, k, i, h, e, f, g are explicitly
  bound, with exactly the displayed sources and targets.
- `lower : ChosenCartesianSquare h e f g` and
  `upper : ChosenCartesianSquare j k i h` give the two Cartesian diagrams, including
  their chosen Cartesian identifications. This uses the definition underlying the recorded
  `ChosenCartesianSquare.baseChangeInverseImageIso` of sbc-def-base-change-square.
- `K : DerivedCategoryModule (ULift ℤ) T` is the full unbounded D(T_et), in the integer
  module encoding specified by sbc-def-base-change-map's record. Lifted-integer modules
  are canonically equivalent to abelian groups: restrict scalars along the ring equivalence
  ULift ℤ ≃+* ℤ and use the unique integer action of an abelian group. These equivalences
  act on sheaves and complexes and preserve quasi-isomorphisms; they carry the adjunctions
  and their mates to the abelian-sheaf ones. No finiteness, torsion or boundedness condition
  is introduced. The lift is necessary for the source exchange API's coefficient universe
  and monoidal instances, as the dependency record explains.
- The first theorem's `hLower` is IsIso of the lower exchange at K; `hUpper` is IsIso
  of the upper exchange at the exact derived inverse image of K along e.
- The conclusion is IsIso of the exchange for
  `upper.toCommSq.flip.horiz_comp lower.toCommSq.flip`. Its top arrow is k ≫ e,
  left arrow j, right arrow g, bottom arrow i ≫ f: precisely the exchanged outer
  rectangle. The derived map only needs its commutativity; its Cartesian property follows
  from the two supplied Cartesian squares, and is not an additional hypothesis.
- In the second theorem `F` is an arbitrary abelian sheaf in the same integer-module
  encoding, and `q : ℕ` ranges over exactly the requested nonnegative degrees.
- `hLower` is H^q of the lower exchange at `singleFunctor _ 0 |>.obj F`.
  `hUpper` is H^q of the upper exchange at the degree-zero complex of
  `(upperStar _ e).obj F`, exactly the second degreewise map at e-inverse-image F.
  The conclusion is H^q of the outer exchange at F[0]. These are the degreewise maps
  by sbc-def-base-change-map's definition; exactness identifies their domains and targets
  with the displayed higher-direct-image sheaves. There is no assumption in other degrees,
  nor an assumption that either full derived exchange is invertible.

Dependency interfaces read and used:

- Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso:
  AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso; its imported
  Sheaf.AlgebraicGeometry.ChosenCartesianSquare supplies ChosenCartesianSquare and toCommSq.
- Sheaf.AlgebraicGeometry.DerivedCategories and its imported
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule, the derived-category encoding.
- WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded:
  AlgebraicGeometry.Etale.derivedBaseChangeMap (both def-kun-unbounded-exchange and
  sbc-def-base-change-map), with its full ambient coefficient assumptions and mate docstring.
  The upstream UpperLowerStar file supplies upperStar and leftDerivedUpperStar;
  leftDerivedUpperStarIsoMapDerivedCategory identifies the latter with exact inverse image.
- DerivedCategory.singleFunctor and DerivedCategory.homologyFunctor are the existing
  degree-zero inclusion and cohomology functors. No private definition of any map is made.

Proof-dependency imports include DerivedSquareIsoPasting, EtaleInverseImageExact,
MorphismDefs, adjunction Mates and Localization.Predicate. The remaining proof interfaces
are supplied transitively by these or by the public statement imports. The bounded-below
pasting interface is useful to the existing bounded-below portion, while the unbounded
proof must implement the termwise/localization argument in the node; it has not been
silently replaced with a bounded-below theorem.

Edge cases: no nonemptiness or reducedness is imposed, so empty schemes are included;
identity arrows and arbitrary Cartesian identifications are allowed; K and F may be zero;
q = 0 is included and no argument assumes q > 0. The scheme universe u and coefficient
universe u+1 are explicit, matching the small-etale-site API. Every binder is explicit;
there are no auto-bound universes or variables.

Searches:

- msearch.py leanfinder: "For two Cartesian squares of schemes, if the unbounded derived
  exchange maps are isomorphisms then the outer base change map is an isomorphism";
  eight hits about stability of geometric properties and pullback isomorphisms, none about
  the specified exchange components.
- msearch.py loogle: "CategoryTheory.mateEquiv_hcomp,
  AlgebraicGeometry.Etale.derivedBaseChangeMap"; no hit (the second identifier is not in
  the Mathlib search index).
- msearch.py grep: "baseChange.*paste|derivedBaseChange.*comp", CategoryTheory;
  no hits. Direct Mathlib Mates source search has no concrete etale composition theorem.
- rg of WeilConjectures and lean/Sheaf for the node id, derivedBaseChange composition,
  and base-change pasting: upstream SmoothBaseChange.Locality contains
  isIso_baseChange_app_of_paste_horiz and the independent degreewise version, but its
  K lives in DerivedCategory.Plus, so it cannot supply the unbounded node. Full signatures
  and docstrings were read. The project's other matches are unrelated unit compatibility
  and module-sheaf comparison statements. No existing unbounded statement was found.
- Inspected ModuleCat.ChangeOfRings.restrictScalarsEquivalenceOfRingEquiv and
  Grp.ZModuleEquivalence.forget₂AddCommGroupIsEquivalence for the coefficient encoding.

Validation: single-file compilation uses only scompile.py on the server, at nice 19,
two threads and a 60-second per-file limit. The first compile caught reversed arguments
in CommSq.horiz_comp; reading its full signature fixed the order to upper then lower.

## Second reading by NL

I read the node, Stacks etale-cohomology.tex lemma-base-change-compose (0EZS),
and sites-cohomology.tex remark-compose-base-change-horizontal (0E47), then the
Lean and the dependency interfaces. The source lemma concerns arbitrary schemes
and the full unbounded derived category; it assumes no properness, smoothness,
finiteness, torsion, or boundedness. Its second assertion is independent at each q.
No statement_change or new/dependency node is present or needed.

Object, hypothesis and conclusion checklist:

1. Six schemes W,Z,X,Y,S,T: `{W Z X Y S T : Scheme.{u}}` in both theorems.
   Verdict: exact, with arbitrary scheme universe u.
2. Seven arrows Z -> W, Z -> Y, W -> X, Y -> X, Y -> T, X -> S, T -> S:
   the binders j,k,i,h,e,f,g have precisely these types. Verdict: exact.
3. Both squares Cartesian: `lower : ChosenCartesianSquare h e f g` and
   `upper : ChosenCartesianSquare j k i h`. I opened ChosenCartesianSquare:
   it extends CommSq and supplies an iso to the pullback respecting both projections.
   This is the chosen Cartesian identification of sbc-def-base-change-square,
   not merely an abstract iso of schemes. Verdict: exact dependency datum.
4. K in D(T_et), with no boundedness: `DerivedCategoryModule (ULift.{u+1} ℤ) T`.
   I opened DerivedCategories and upstream Derived/Coefficients: this is the full
   DerivedCategory of small-etale sheaves of modules, not DerivedCategory.Plus.
   The integer-module encoding is expressly specified by sbc-def-base-change-map.
   Restriction along the ring equivalence ULift ℤ ≃+* ℤ and the equivalence of
   integer modules with AddCommGrpCat identify it with abelian sheaves. I checked
   ModuleCat.restrictScalarsEquivalenceOfRingEquiv and
   ModuleCat.forget₂AddCommGroupIsEquivalence in Mathlib. The equivalences extend
   pointwise to sheaves and complexes, preserve cohomology and quasi-isomorphisms,
   and carry the inverse-image adjunctions and their canonical mates across.
   Verdict: same objects and canonical maps, with no coefficient restriction.
5. Lower derived exchange invertible at K: `hLower` is IsIso of
   `(derivedBaseChangeMap _ lower.toCommSq.flip).app K`.
   In the source signature the exchanged square has (g',f',f,g)=(e,h,g,f),
   giving f-inverse-image Rg_* -> Rh_* e-inverse-image. Verdict: exact.
6. Upper derived exchange invertible at e-inverse-image K: `hUpper` uses
   `upper.toCommSq.flip` at `(L((e)^*[_])).obj K`.
   The upstream leftDerivedUpperStarIsoMapDerivedCategory identifies this with
   exact termwise inverse image; derivedSquareUpperStarIso uses its canonical
   composition comparison and derivedBaseChangeSquare is its mate. I read those
   bodies and all ambient assumptions: the specialized module category supplies
   the required instances, without additional assumptions on schemes or K.
   Verdict: exact.
7. Outer derived exchange invertible: the conclusion uses
   `upper.toCommSq.flip.horiz_comp lower.toCommSq.flip`.
   CommSq.horiz_comp composes the top and bottom arrows in that order; the result
   has (g',f',f,g)=(k ≫ e,j,g,i ≫ f), hence exactly the outer map.
   Its Cartesian property follows by pasting and need not be assumed separately.
   Verdict: exact, including the specified canonical map rather than an arbitrary map.
8. Abelian sheaf F and one nonnegative degree q: the second theorem binds
   `F : Sheaf T.smallEtaleTopology (ModuleCat.{u+1} (ULift.{u+1} ℤ))`
   and `q : ℕ`. Verdict: same abelian-sheaf encoding, all q >= 0.
9. Lower degree-q map invertible: `hLower` is IsIso of H^q applied to the
   lower exchange at `(DerivedCategory.singleFunctor _ 0).obj F`.
   This is exactly the degreewise definition recorded by sbc-def-base-change-map.
   Verdict: exact; no assumption about the full exchange or other degrees.
10. Upper degree-q map invertible: `hUpper` applies the same construction to
    the upper square and the degree-zero complex of `(upperStar _ e).obj F`.
    Exact inverse image identifies this with e-inverse-image F in the source.
    Verdict: exact; it does not assume base change at arbitrary sheaves on Y.
11. Outer degree-q conclusion: H^q of the outer exchange at F[0]. Exact inverse
    image and the canonical single-complex comparison identify the endpoints with
    (fi)^-1 R^q g_* F and R^q j_* (ek)^-1 F. Verdict: exactly the second clause.

Edge cases: empty schemes, zero complexes/sheaves, identity arrows, and any chosen
Cartesian identification are allowed. q=0 is included. There is no index family,
characteristic constraint, or field assumption. Scheme universe u and coefficient
universe u+1 agree with the recorded small-etale size convention; any finite diagram
of schemes and sheaves can be placed in such a common universe. All variables are
explicitly bound. In particular neither theorem restricts K to D+.

Independent searches (different wording from the worker):

- msearch leanfinder: "Isomorphism of exchange transformations for an unbounded
  derived etale sheaf is preserved by pasting Cartesian squares" returned eight
  gluing/sheaf-composition hits; none states this theorem.
- msearch loogle: `CategoryTheory.mateEquiv_hcomp` returned the generic mate
  composition theorem, not the concrete unbounded etale statement.
- msearch grep: `mateEquiv_hcomp|baseChange.*composition` in CategoryTheory
  returned generic mate and morphism-property infrastructure, no exact match.
- Direct rg on Mathlib, WeilConjectures and lean/Sheaf used
  `derivedBaseChangeMap.*(comp|paste)`,
  `IsIso.*(exchange|baseChange).*([Cc]omp|paste)`, and `cartesian_tower`.
  I opened SmoothBaseChange/Locality.lean, including
  isIso_baseChange_app_of_paste_horiz and the two degreewise forms. Its derived
  theorem quantifies over DerivedCategory.Plus and uses the bounded-below baseChange.
  The degreewise sheaf theorem is also expressed through that bounded-below API;
  it does not supply the full unbounded clause. No existing declaration covers
  the complete node, so dropping this module would lose its first assertion.

No mismatch found; no Lean or node change. No definition or private map is added,
and both named theorem proofs remain solely sorry. The source/blueprint docstrings
contain the node's four proof steps across the two assertions: Cartesian pasting,
termwise descent, mate pasting/whiskering and inversion, and the independent
cohomology calculation. Public imports supply the statement dependencies; proof
imports supply the recorded pasting, exactness, mate and localization interfaces.
The bounded-below proof interface is not being asserted to prove the unbounded law.

Validation: scompile.py compiled the sole delivered module on the server cleanly
(4.6 seconds for its library compilation), within the required limit. The first
reader invocation used a repository-relative path from the wrong directory;
rerunning from the sandbox fixed that invocation without any source change.
I mechanically checked lean.statement equals the first signature verbatim,
and checked the second signature and all binders by eye. No warnings appeared.
