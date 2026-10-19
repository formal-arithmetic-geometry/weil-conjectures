## Worker report

The module `Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty`
defines `AlgebraicGeometry.Etale.UnboundedCumulativeUniversalBaseChangeProperty`.
This is a real Prop-valued definition, with no theorem, proof, or `sorry` added.
Only the item's `lean` field changes. No new nodes, dependency repairs, or statement
corrections are required.

The statement was checked against the full current DAG node and Stacks Project,
[Tag 0F02, Remark 59.88.1](https://stacks.math.columbia.edu/tag/0F02).
The latter has both successive fibre products, qcqs only on `g`, the common
annihilator, and every degree at most the bound. The module follows the node's
specified unbounded module exchange rather than the bounded-below presentation.

Clause-by-clause correspondence:

- Schemes and an arbitrary morphism `f:X → S` are `{X S : Scheme.{u}} (f : X ⟶ S)`.
  There are no smoothness, qcqs, properness, or finite-type assumptions on `f`.
- Positive integer `n` is `(n : ℕ) (_hn : 0 < n)`. Nonnegative integer `q₀` is
  `(q₀ : ℕ)`. These parameterize precisely the stated integer domains.
- The coefficient ring is `ULift.{u + 1} (ZMod n)`. The lift implements the
  recorded six-functor coefficient convention and preserves the ring operations.
- Every base change is `∀ (S' : Scheme.{u}) (a : S' ⟶ S)`.
  `X'` is the existing categorical scheme pullback `pullback f a`, and its
  projection `f'` is `pullback.snd f a`.
- Every horizontal morphism is `(T : Scheme.{u}) (g : T ⟶ S')`, with exactly
  `[QuasiCompact g] [QuasiSeparated g]`. No condition is imposed on `a` or its
  composite with `g`.
- The second fibre product is `pullback (pullback.snd f a) g`. Its projections
  are `h = pullback.fst (pullback.snd f a) g` and
  `e = pullback.snd (pullback.snd f a) g`. The canonical `IsPullback` supplies
  their commutativity and Cartesian identification; no arbitrary square or map
  is an extra input.
- The sheaf quantifier is
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))`.
  This is exactly the dependency's module encoding of abelian sheaves killed by
  `n`: integer multiplication descends uniquely to Z/nZ when n kills the group,
  and every Z/nZ action on a unital module has this multiplication action.
  Restrictions are automatically linear. No redundant annihilator hypothesis is
  added to a type whose every object already satisfies it.
- The degree-zero object is `(DerivedCategory.singleFunctor _ 0).obj F`.
  This existing functor places the sheaf in degree zero with all other terms
  and all differentials zero, and localizes the resulting cochain complex.
- The unbounded exchange is `exactDerivedBaseChangeMap` from the recorded
  `def-kun-unbounded-exchange` module, applied to
  `(IsPullback.of_hasPullback (pullback.snd f a) g).flip.toCommSq`.
  The flip is essential: in that declaration the variables become
  `(f,f',g,g') = (g,h,pullback.snd f a,e)`. Thus its component is precisely
  `D(f') (Rg_* F[0]) → Rh_* (D(e) F[0])`.
  This is the dependency's canonical mate of exact, termwise-derived inverse
  image with total right derived direct image, as the node specifies.
- `(q : ℤ), q ≤ (q₀ : ℤ) → ...` includes every negative degree and the upper
  endpoint. `(DerivedCategory.homologyFunctor ... q).map` takes exactly the
  indicated cohomology sheaf morphism on `X'`, and `IsIso` asserts that it is
  an isomorphism in the category of module sheaves.
- There is no `IsUnit (n : Γ(S, ⊤))` parameter. The comparison paragraph with
  `sbc-def-base-change-property` is explanatory, not another conjunct or
  assumption. That dependency's module is imported without redefining its
  fixed-degree, universal, or cumulative predicates.

Dependencies read and used:

- `def-weil-pbc-scheme-conventions` is a convention record, with no declaration
  to import. It supplies Mathlib `AlgebraicGeometry.Scheme`, `QuasiCompact`,
  and `QuasiSeparated`; scheme pullbacks are the existing `Limits.pullback`.
- `def-weil-pbc-etale-sheaves` records
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; its source was read with
  `scompile.py --source`. For this item the relevant recorded notions are
  `CategoryTheory.Sheaf` and the module encoding in the record's note, rather
  than its locally-constant or torsion predicates. This module is imported
  transitively by `BaseChangeMapAbelianAndSets`.
- `def-weil-pbc-derived-categories`: imported
  `Sheaf.AlgebraicGeometry.DerivedCategories`, using the recorded unbounded
  `DerivedCategory` of `Sheaf ... (ModuleCat ...)` and
  `DerivedCategory.homologyFunctor`; this is the expansion of
  `AlgebraicGeometry.Etale.DerivedCategoryModule`. The source signatures and
  docstrings of `singleFunctor` and `homologyFunctor` were also read.
- `sbc-def-base-change-square`: imported
  `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso` and read
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso` plus
  its underlying `ChosenCartesianSquare` structure. Canonical pullbacks
  already carry the Cartesian identification, so no duplicate square
  structure or square comparison is defined.
- `sbc-def-base-change-map`: imported its recorded
  `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`. Its retained module
  map is `AlgebraicGeometry.Etale.derivedBaseChangeMap`, and the record also
  supplies the abelian variant. The present item uses the exact inverse-image
  presentation explicitly recorded by the next dependency, rather than
  inventing a new exchange or using an arbitrary natural transformation.
- `def-kun-unbounded-exchange`: imported
  `Sheaf.AlgebraicGeometry.ExactUnboundedExchange` and used the recorded
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`, with its canonical
  `exactDerivedSquareUpperStarIso` and mate construction. The full current
  module was checked using `scompile.py --source`.
- `sbc-def-base-change-property`: imported
  `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty` and read
  `AlgebraicGeometry.Etale.CumulativeUniversalBaseChangeProperty` and its
  upstream `BaseChangeProperty` / `UniversalBaseChangeProperty`. They use
  the bounded-below degreewise map and the cumulative record has an
  invertibility binder and nonnegative-degree quantifier. They cannot be
  recorded as an exact existing definition of this broader node.

Edge cases checked: `n = 1` is allowed (the zero coefficient ring and zero
module sheaves); `n = 0` is outside the stated positive domain; `q₀ = 0`
retains degree zero and every negative degree. Empty schemes, zero sheaves,
identity base changes, arbitrary non-qcqs base changes `a`, and `n` divisible
by a residue characteristic are not excluded. All test schemes share the
scheme universe, and the site-value/coefficient universe is `u+1`, following
the existing recorded framework. There are no unbound implicit variables.
The two pullback squares and the source/target of the exchange were checked
explicitly; an initial unflipped orientation was caught and corrected by
compilation before this delivery.

Searches for an existing declaration (2026-10-16):

- `msearch.py`, LeanFinder: “cumulative universal cohomological base change
  property for etale sheaves of Z/nZ modules through every integer degree
  at most q after arbitrary base change”. Eight hits concern formal etaleness,
  geometric stability, or unrelated complex factorizations; none defines this
  predicate.
- `msearch.py`, Loogle: `"BaseChangeProperty"`. Zero hits.
- `msearch.py`, Mathlib grep:
  `UniversalBaseChangeProperty|CumulativeUniversalBaseChangeProperty|exactDerivedBaseChangeMap`.
  Zero hits.
- `msearch.py`, LeanSearch: “universal cohomological base change for etale
  sheaves of Z/nZ modules through degree q”. Service returned Internal Server
  Error; recorded as unavailable, with no absence conclusion drawn from it.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for
  `BaseChangeProperty|UniversalBaseChangeProperty|baseChangeHomologyMap|exactDerivedBaseChangeMap`
  found the signatures read above. `CumulativeUniversalBaseChangeProperty`
  in the project is the restricted predicate just discussed; no exact match.
- `rg` of upstream `WeilConjectures` for `def-kun-bc-property` and of
  `dag/lean_names_upstream.json` for the proposed full declaration name found
  no attachment or collision. No new notion besides the assigned definition
  was introduced, so no new definition-node search is required.

Validation: the final module passed `scompile.py NK def-kun-bc-property`
without errors or warnings, both as the sandbox file and under its library
module name (about five seconds per file). No global build was run.
The required `deliver2.py NK def-kun-bc-property --no-push` is the final
mechanical gate. The independent second reader will write their own section
and deliver; this worker does not claim an independent second reading.

No node faults or disputed statements remain.

## Second reading by NK

I independently opened the item record in
`dag/nodes/sec-smooth-purity/def-kun-bc-property.json`, the source cited there
(Stacks Project Tag 0F02, Remark 59.88.1), and
`lean/Sheaf/AlgebraicGeometry/UnboundedCumulativeUniversalBaseChangeProperty.lean`.
The source remark states that, for a morphism (f:X\to S) and an integer (n),
`BC(f,n,q₀)` is tested for every diagram with (X'=X\times_S S'),
(Y=X'\times_{S'}T), and qcqs (g:T\to S'), for every abelian sheaf on
(T_{\acute et}) annihilated by (n), and in every degree (q\le q_0).  The
item node makes this explicit with the module-sheaf and unbounded-derived
category conventions.  The following is the item-by-item correspondence.

* The morphism (f:X\to S) is the implicit `{X S : Scheme.{u}}` and explicit
  `(f : X ⟶ S)` in `UnboundedCumulativeUniversalBaseChangeProperty`.  No
  smoothness, separatedness, properness, finite type, qc, or qs hypothesis on
  (f) is present.
* The node's integers (n\ge1) and (q_0\ge0) are `(n : ℕ) (_hn : 0 < n)` and
  `(q₀ : ℕ)`.  Thus exactly the nonnegative representatives are parameters,
  while the degree variable below is an arbitrary integer.  The coefficient
  ring is rendered by `ULift.{u + 1} (ZMod n)`, the recorded module-category
  universe convention for \(\mathbf Z/n\mathbf Z\).
* The universal base change is the binders
  `(S' : Scheme.{u}) (a : S' ⟶ S)`.  The scheme (X') and its map (f') are
  `pullback f a` and `pullback.snd f a`, so they are the node's canonical
  fibre product and projection.
* The second test scheme and its horizontal morphism are
  `(T : Scheme.{u}) (g : T ⟶ S')`, followed by exactly
  `[QuasiCompact g] [QuasiSeparated g]`.  There is no condition on (a), on
  (f'), or on (g\) composed with (a\).
* The canonical square is represented by
  `IsPullback.of_hasPullback (pullback.snd f a) g`.  Before the `.flip`, its
  projections are `pullback.fst (pullback.snd f a) g : Y ⟶ X'` and
  `pullback.snd (pullback.snd f a) g : Y ⟶ T`; these are the node's (h) and
  (e), and the pullback condition gives (f'\circ h=g\circ e).  The flip
  supplies `CommSq e h g f'`, exactly the substitution
  `(f,f',g,g')=(g,h,f',e)` required by the node.
* The node's abelian sheaf (F) annihilated by (n) is represented by the
  binder
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1}
  (ULift.{u + 1} (ZMod n)))`.  This is the recorded equivalent encoding: a
  module over `ZMod n` has additive (n)-torsion, and an (n)-annihilated
  abelian sheaf has the unique scalar action `[m]s = ms`; restrictions remain
  linear.  No extra annihilator, finiteness, or invertibility hypothesis is
  introduced.
* The node's (F[0]) is
  `(DerivedCategory.singleFunctor (...) 0).obj F`, with the category filled in
  as `Sheaf T.smallEtaleTopology (ModuleCat ... (ULift (ZMod n)))`.
  This is the degree-zero complex with zero other terms and differentials.
* `exactDerivedBaseChangeMap (ModuleCat ...)
  (IsPullback.of_hasPullback ...).flip.toCommSq` is the recorded unbounded
  module exchange.  Its component at that single object has source
  (D(f')Rg_*F[0]) and target (Rh_*D(e)F[0]), so its direction agrees with
  the displayed map in the node.  The `.flip` is necessary because
  `exactDerivedBaseChangeMap` takes a square `CommSq g' f' f g`.
* The final binders `(q : ℤ), q ≤ (q₀ : ℤ)` quantify every negative degree,
  degree zero, and the upper endpoint.  The conclusion is
  `IsIso ((DerivedCategory.homologyFunctor (...) q).map (...))`, i.e. the
  (q)-th cohomology-sheaf morphism is an isomorphism of the required module
  sheaves on (X'_{\acute et}).  The node's comparison with the smooth
  base-change predicate is explanatory; it is not an additional conjunct, and
  the Lean definition adds no `IsUnit` assumption.

I also read every recorded dependency used by the module.  The scheme
conventions supply `Scheme`, `QuasiCompact`, and `QuasiSeparated`; the etale
sheaf and derived-category records supply the sheaf and homology categories;
the chosen-square module supplies the canonical `IsPullback`; the base-change
map and unbounded-exchange modules supply the canonical mate (not an arbitrary
natural transformation); and the existing cumulative smooth-base-change
predicate is only used for the node's comparison paragraph.  No dependency
module is duplicated or silently replaced.

Edge cases checked against both the node and the signature are: (n=1) (the
zero coefficient ring and zero module sheaves), exclusion of (n=0),
(q_0=0) (all negative degrees and degree zero remain), negative (q), empty
schemes, zero sheaves, identity base changes, arbitrary non-qcqs (a), and
residue characteristics dividing (n).  All schemes use the same universe
and the coefficient category has the prescribed `u + 1` value universe.  No
variable is left auto-implicit, and the Lean file has no line over 100
characters.

For the independent existing-definition check I ran `msearch.py` with
LeanFinder and Loogle queries for cumulative/universal cohomological base
change, `rg` over Mathlib, this repository's `lean/Sheaf`, and the upstream
`WeilConjectures` tree, and inspected the source declaration
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty`.  The latter is the
bounded-below, fixed-coefficient, degreewise predicate; it does not define
this node's unbounded exchange property through all integer degrees.  No exact
`UnboundedCumulativeUniversalBaseChangeProperty` declaration exists.  The
LeanSearch service returned an internal error, so it was not used as evidence
of absence.  These searches agree with the worker's recorded searches.

No mismatch was found between the node and the Lean signature, so no module or
node statement was changed.  The only delivery change in this second reading
is this independent audit section; the module was recompiled with
`scompile.py` and emitted only the permitted `sorry`-free result.
