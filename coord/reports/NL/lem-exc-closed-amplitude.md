## Worker report

The main module `Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude` states
`AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_amplitude`, with `sorry`.
It states both clauses of lem-exc-closed-amplitude, without modifying the node's
statement, proof, statement dependencies, or proof dependencies. The previous
worker's stage-1 completion issue does not apply: this is a stage-2 attachment,
not another split. The initially empty sandbox contained only dispatcher markers.

Hypothesis and clause correspondence:

- The schemes are `{Z T U : Scheme.{u}}`; `i : Z ⟶ T` and
  `[IsClosedImmersion i]` give the arbitrary closed immersion. `j : U ⟶ T`,
  `[IsOpenImmersion j]` and `hij : Set.range i.base = (Set.range j.base)ᶜ`
  say precisely that j is its open complement. There is no quasi-compactness,
  finite-type, Noetherianity, invertibility, or Tor-amplitude assumption.
- `A : Type (u + 1)` with `[CommRing A] [Finite A]` is the finite coefficient
  ring, using the commutative coefficient convention of the recorded
  def-weil-pbc-derived-categories. This is the existing six-functor encoding
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)`; no ring-sheaf encoding or
  alternate derived category is introduced.
- `(a b c : ℤ) (hc : 0 ≤ c)` binds both endpoints and the nonnegative bound.
  An integer with this hypothesis is precisely a nonnegative integer; empty
  input intervals are allowed.
- `hcd` quantifies over EVERY module sheaf M on U and EVERY integer q > c.
  Its `IsZero` is the q-th `DerivedCategory.homologyFunctor` of the actual
  derived `lowerStar` applied to `DerivedCategory.singleFunctor _ 0` of M.
  This is R^q j_* M, rather than a bound imposed directly on complexes.
- The first conjunct quantifies over every `K : DerivedCategoryModule A T`.
  `DerivedCategory.homologyConcentratedIn a b K` is the standard t-structure
  interval D^[a,b]. Its conclusion is the same predicate for `[a,b+c+1]`
  on `(R(lowerStar ... i)).rightAdjoint.obj K`. The dependency module proves
  existence as a statement, registered as an instance. Thus this is Ri^! of
  i_* on the ordinary unbounded derived categories, not an additional
  existence hypothesis and not a placeholder arbitrary functor.
- The second conjunct is conditional on every R^q j_* F being constructible
  for every constructible F and every integer q. It quantifies again over K
  with the same interval bound and with every H^q(K) constructible. It concludes
  both the SAME output bound and constructibility of every H^q(Ri^! K).
  Constructibility everywhere is exactly the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf`, with global finite constructible
  locally closed stratifications and finite constant module values. The
  upstream stalk-generation predicate is not substituted for it.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: the coefficient/category
  convention, exposing `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; H^q is
  `DerivedCategory.homologyFunctor`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`, specialized to `ModuleCat A`. These are
  the recorded direct and inverse images, not private copies.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  the actual unbounded `CategoryTheory.Functor.rightDerivedFunctor` of
  lowerStar, written with its established R notation. The server source was
  read using `scompile.py --source` and agrees with the local declaration.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `isGE_iff`, `isLE_iff`; the existing interval
  wrapper is `DerivedCategory.homologyConcentratedIn`, in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, with the
  exact recorded global constructibility definition from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Functor.IsLeftAdjoint`,
  `Functor.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`. The chosen right
  adjoint has its defining adjunction, which determines it up to the unique
  adjunction-compatible natural isomorphism.

All recorded proof-dependency modules are imported privately (Mathlib matches
by their recorded file). The absent closed-support-triangle dependency has no
module to import; its full triangle is included in the proof docstring, and
stage 3 will use its node when stated. All eight proof steps of the item are
recorded in the theorem's docstring. There are no new definitions or nodes,
no proof supplied, and no statement correction or statement dispute.

Searches:

- `msearch.py NL lem-exc-closed-amplitude leanfinder` with the query
  "Exceptional inverse image for a closed immersion has cohomology in degrees
  a to b+c+1 if its open complement has cohomological dimension at most c"
  returned eight ordinary cohomology-bound and injective-vanishing lemmas,
  including `DerivedCategory.isGE_iff`, `isLE_iff`, and `isZero_of_isGE`.
  None states the closed exceptional inverse-image theorem.
- `msearch.py ... loogle '"rightDerived", "IsLE"'` returned three generic
  Kan-extension descriptions of right derived functors. None is this item.
- `msearch.py ... grep 'closed.*amplitude|closed.*[Aa]dj|cohomologicalDimension'`
  returned 25 unrelated closure/monoidal-adjunction hits; no matching theorem.
- `rg` of the source, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the two proposed declaration names, closed-amplitude phrases and
  cohomologicalDimension found no existing declaration. Searching the exact
  item id in the source also found none. The upstream
  `constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar`
  in `SixFunctors/Etale/Derived/Stability/ClosedImmersion.lean` was read in full:
  it assumes Tor amplitude, a derived-complex bound for the complement, and
  a projection formula. It cannot represent this unconditional ordinary
  amplitude statement or its exact constructibility predicate.
- The published server node of lem-exc-closed-ambient has no Lean record.
  The delivery branch `deliver/Q38/lem-exc-closed-ambient` was inspected: it
  contains only stage-1 JSON and report changes, no declaration. No delivered
  stage-2 interface was discarded or replaced.

Edge cases checked before writing: empty Z (zero supported image); empty U
(identity closed immersion); zero ring and zero complex; c = 0, yielding
[a,b+1]; a = b (a sheaf in one degree); a > b (zero input). All are included.
The geometric complement relation excludes no choice of a presentation of the
open complement. No a ≤ b binder is imposed. The +1 at the upper endpoint
agrees with H^(n-1)(Rj_*j^*K) in the closed-support triangle.

## Dependency modules

`lem-exc-closed-ambient` is an existing DAG prerequisite with no Lean declaration,
not a reason to wait or split the node again. Under the human's 2026-10-16
"unstated dependencies are yours to state" instruction, the delivery includes
`Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` and a lean-only copy of its
node. Its theorem
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`
states existence of a right adjoint for the actual ordinary derived direct
image for every closed immersion and finite ring, with `[Ring A]` rather than
restricting to commutative rings. `Functor.IsLeftAdjoint` means exactly
existence of a functor together with an adjunction. The open complement is
canonical for every closed immersion and is not a necessary parameter to this
existence proposition. No constructibility or boundedness is assumed. The
proof docstring contains both steps of this node: supported-section kernel and
sheaf adjunction, then K-injective resolutions and the induced ordinary-derived
adjunction. Its record explains the missing interface and use of the standard
adjunction-determined right-adjoint construction. Every other node field is
preserved, including the prerequisite's current stage-1 status.


## Second reading by NL

I independently read the item statement in `dag/nodes/sec-smooth-purity/lem-exc-closed-amplitude.json`, the blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-exc-closed-amplitude.md`, and the Lean signature in `lean/Sheaf/AlgebraicGeometry/EtaleClosedSupportAmplitude.lean`. The source file's displayed statement is the complete source statement; its proof uses the ordinary closed-support triangle and the finite hypercohomology spectral sequence.

Statement list and verdict:

1. A closed immersion `i : Z ⟶ T` is rendered by `{Z T : Scheme.{u}}`, `(i : Z ⟶ T)` and `[IsClosedImmersion i]`; this is the node's arbitrary closed immersion.
2. Its open complement `j : U ⟶ T` is rendered by `(j : U ⟶ T)`, `[IsOpenImmersion j]`, and `hij : Set.range i.base = (Set.range j.base)ᶜ`. This is the explicit scheme-level encoding of “open complement”, with no quasi-compactness, Noetherianity, finite-type, or Tor hypothesis added.
3. The finite coefficient ring is rendered by `A : Type (u + 1)`, `[CommRing A]`, and `[Finite A]`, matching the recorded ordinary étale coefficient convention.
4. The integer interval endpoints and nonnegative bound are rendered by `(a b c : ℤ)` and `hc : 0 ≤ c`; no order `a ≤ b` is silently added.
5. The direct-image bound for every module sheaf and every `q > c` is rendered by `hcd`, whose `homologyFunctor` of `R lowerStar` applied to `singleFunctor` is exactly `R^q j_* M`.
6. The first conclusion is rendered as `∀ K`, `homologyConcentratedIn a b K` implying `homologyConcentratedIn a (b + c + 1)` of `(R (lowerStar ... i)).rightAdjoint.obj K`. The imported ambient-adjoint module supplies the actual ordinary derived right adjoint; this is not an arbitrary functor parameter.
7. The additional constructibility premise is rendered for every constructible `F` and every `q` by `Scheme.IsConstructibleEtaleModuleSheaf` on the same `R^q j_*F` expression.
8. Under that premise, the second conclusion quantifies over every `K` with the same interval and all constructible cohomology sheaves, and returns both the identical interval bound and constructibility of every output cohomology sheaf. Thus “constructible cohomology on both sides” is neither weakened nor strengthened.

No mismatch was found in the item's statement or signature, so no statement correction was made. The dependency module `EtaleClosedAmbientAdjoint.lean` was checked against the separate node `lem-exc-closed-ambient`: it supplies `IsLeftAdjoint` for the actual derived closed direct image, with no constructibility or boundedness assumption. No existing declaration was found in Mathlib, the source repository, the shared `lean/Sheaf`, or the current server source; the module is therefore the authorized dependency-module repair for the recorded missing interface.

Edge cases checked: `Z = ∅`, `U = ∅`, identity closed immersion, zero coefficient ring and zero complex, `c = 0` (giving `[a,b+1]`), `a = b`, and `a > b` (where the interval premise is vacuous except for the zero object). No universe is left unbound: the scheme universe is `u` and the module coefficient universe is `u + 1`, as required by the étale-site encoding.

Searches were repeated with `msearch.py` (`leanfinder`, `loogle`, and `grep`), `rg` over Mathlib, `WeilConjectures`, and shared `lean/Sheaf`, and the upstream declaration-name index. The hits were generic t-structure, right-derived-functor, or local-cohomology APIs; none states this closed-support amplitude theorem. The exact source search also found no pre-existing declaration.

Both delivery modules compile cleanly with `scompile.py`; the only expected diagnostic is the theorem `sorry` warning.
