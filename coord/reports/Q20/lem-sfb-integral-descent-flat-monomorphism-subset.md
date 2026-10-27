## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralDescentFlatMonomorphismSubset` states
`AlgebraicGeometry.integral_descent_flat_monomorphism_subset`. Its sole theorem has proof
`by sorry`; there are no definitions, helper theorems, new nodes, or dependency repairs.
The node is unchanged except for `lean`.

Source read: Raynaud, *Un critère d'effectivité de descente*, §3, Theorem 3.3(ii)
(heading 3.4 in the scan), printed pp.12–13, with §1 Proposition 1.2, Corollary 1.3,
and Definition 1.4 (printed pp.2–3). Primary scan:
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf . The source case (ii)
requires Noetherian local rings; the assigned node states the locally Noetherian
specialization, which is retained exactly. No source-based correction is needed.
The eight-step natural-language proof is included in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause reading:

| Node text | Lean rendering |
| --- | --- |
| Z, Y, F' are schemes | `{Z Y F' : Scheme.{u}}` |
| Z locally Noetherian | `[IsLocallyNoetherian Z]` |
| integral morphism q : Y → Z | `(q : Y ⟶ Z) [IsIntegralHom q]` |
| q surjective on underlying points | `[Surjective q]` |
| any subset H of the underlying space of Z | `(H : Set Z)` |
| given morphism j' : F' → Y | `(j' : F' ⟶ Y)` |
| j' quasi-compact | `[QuasiCompact j']` |
| j' flat in the stalkwise sense | `[Flat j']`, using `Flat.iff_flat_stalkMap` |
| j' monic on Hom from every test scheme | `[Mono j']`, whose `right_cancellation` quantifies over every object of `Scheme.{u}` |
| image of j' equals q⁻¹(H) | `(himage : Set.range j' = q ⁻¹' H)` |
| existence of scheme F and morphism j : F → Z | `∃ (F : Scheme.{u}) (j : F ⟶ Z), ...` |
| j quasi-compact, flat, monic | `QuasiCompact j ∧ Flat j ∧ Mono j` |
| image of j exactly H | `Set.range j = H` |
| morphism p : F' → F | `∃ (p : F' ⟶ F), ...` |
| square with j', p, q, j cartesian (including commutativity) | `IsPullback j' p q j` |
| isomorphism F' ≅ Y ×_Z F | `∃ (e : F' ≅ pullback q j), ...` |
| isomorphism over Y | `e.hom ≫ pullback.fst q j = j'` |
| its second projection is the displayed p | `e.hom ≫ pullback.snd q j = p` |
| no finite-fibre condition on q | no fibre-cardinality assumption |
| no flatness of q | no `Flat q` assumption |
| no Noetherianity of Y | no `IsLocallyNoetherian Y` assumption |

The last projection equation simply ties the explicitly requested morphism p to the
same cartesian identification. It imposes no further condition, since p is the second
projection under this isomorphism. The definition of `IsPullback` includes the
commutative-square equation and its limit universal property.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; the actual locally ringed-space scheme structure
  and its locally ringed-space morphisms are used.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`; the recorded Mathlib class requires
  Noetherian rings on affine opens and is equivalent to the cover definition.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsIntegralHom`,
  defined in `Mathlib.AlgebraicGeometry.Morphisms.Integral` and publicly imported by
  the node's recorded module `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
  It extends `IsAffineHom` and requires integral section maps on all affine opens.
  The finite-morphism part of that definition node is not assumed here.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; `Flat.iff_flat_stalkMap` is exactly
  the recorded equivalence with stalkwise flatness.
- `def-weil-pbc-scheme-conventions`: a convention record with no declaration/module.
  Its quasi-compactness is `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, with the exact affine-open
  equivalence `quasiCompact_iff_forall_isAffineOpen`. Its surjectivity is the class
  `AlgebraicGeometry.Surjective` in `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
  The monomorphism clause uses the standard `CategoryTheory.Mono` from
  `Mathlib.CategoryTheory.Category.Basic`, not a newly defined predicate.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd` from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Scheme pullbacks are supplied by Mathlib. The square is the standard
  `CategoryTheory.IsPullback` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.

Public imports expose all statement dependencies. Plain proof imports include the
recorded `Sheaf.AlgebraicGeometry.RingedSubspace`,
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`,
`WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget`,
`Mathlib.Topology.Sheaves.Functors`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. The integral closedness, integral/flat/
surjective/quasi-compact base-change facts are already exposed by the statement
imports. The ringed-image, affine-neighbourhood, affine-envelope, and
maximal-generalization proof nodes have no recorded Lean statements on the read
base, so no imports for those unstated proof nodes can yet be supplied. Their
mathematical uses remain fully documented in the proof docstring. None is needed
to type the statement, and none has been replaced by an assumption.

Edge cases checked before drafting:

- H empty: the range condition forces F' empty; the descended representative can be
  the empty scheme and both pullback formulations retain this case.
- H all of Z: j' is a surjective quasi-compact flat monomorphism, hence an
  isomorphism; take j to be the identity of Z. No proper-subset assumption appears.
- Z empty: any given morphism Y → Z forces Y empty. All the conclusions remain
  meaningful, and there is no nonempty-instance binder.
- Nonflat integral covers and covers with infinite fibres remain allowed: only
  `IsIntegralHom q` and `Surjective q` are assumed.
- Y need not be locally Noetherian, and Z need not be globally quasi-compact.
- All schemes live in one arbitrary explicitly bound universe u, as does the
  category's arbitrary test scheme for `Mono`. This is the usual ambient category
  of schemes; any finite collection of scheme sizes can be put in a common ambient
  universe. There is no quantifier over an independently smaller test universe.

Searches for an existing statement (2026-10-24):

- `msearch.py grep` query: `integral.*descent|flat.*monomorph|monomorph.*flat` in `AlgebraicGeometry`. Result: 2 hits; `Mathlib/AlgebraicGeometry/Morphisms/FlatMono.lean`, `Mathlib/AlgebraicGeometry/Morphisms/FlatMono.lean`.
- `msearch.py loogle` query: `"IsIntegralHom", "Mono"`. Result: 0 hits; .
- `msearch.py leanfinder` query: `Integral descent of a subset represented by a quasi-compact flat monomorphism along an integral surjective scheme morphism to a locally Noetherian scheme`. Result: 8 hits; `AlgebraicGeometry.IsIntegralHom`, `AlgebraicGeometry.IsIntegral`, `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomNormalizationDesc`, `AlgebraicGeometry.Scheme.Hom.instIsIntegralNormalization`, `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization`, `AlgebraicGeometry.isIntegral_of_isOpenImmersion`, `AlgebraicGeometry.IsFinite.instIsIntegralHom`, `AlgebraicGeometry.IsIntegralHom.hasAffineProperty`.
- `msearch.py leansearch` query: `A quasi-compact flat monomorphism representing the inverse image of a subset descends along an integral surjection to a locally Noetherian scheme`. Result: 8 hits; `AlgebraicGeometry.IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact`, `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`, `AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`, `AlgebraicGeometry.IsIntegralHom.instUniversallyClosed`, `AlgebraicGeometry.Scheme.Hom.isCompact_preimage`, `AlgebraicGeometry.IsIntegralHom.hasAffineProperty`, `AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact`, `AlgebraicGeometry.instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget`.

LeanFinder finds definitions of integral morphisms and normalization statements.
LeanSearch finds flat descent and the criterion that a surjective quasi-compact
flat monomorphism is an isomorphism. None asserts this integral descent of a subset.
The Mathlib grep hits concern flat monomorphisms locally of finite presentation,
which is an extra assumption absent here. Loogle finds no result.

Additional direct searches: `rg -n
'integral.*descent|flat.*monomorph|monomorph.*flat|integralDescent|integral_descent'`
in `lean/WeilConjectures` and `lean/Sheaf` finds unrelated integral-coefficient
constructions, flat descent, and the local structure of flat monomorphisms; none
gives the assigned statement. `grep -rn
'lem-sfb-integral-descent-flat-monomorphism-subset' lean/WeilConjectures` has no
hits. `rg` of `dag/lean_names_upstream.json` for integral descent with flat mono,
and a direct search for the proposed declaration name in Mathlib, WeilConjectures,
and Sheaf have no hits. No duplicate definition or statement is introduced.

No statement dispute or node fault was found.

## Second reading by Q20

Author self-check, as required by this dispatch's prohibition on starting agents;
the maintainer supplies independent review. With the complete original node and
finished module open, I checked the hypothesis and conclusion table above against
the Lean signature again. `Mono` is categorical cancellation on maps from schemes,
not just injectivity on underlying points. `Set.range` and preimage use the actual
underlying continuous maps. The pullback order is q first and j second, so its
first projection targets Y and its second projection targets F. `IsPullback j' p
q j` therefore has exactly the requested square orientation; both projection
equations use those same maps. Every requested hypothesis is present and none
of the expressly excluded assumptions was added. The arbitrary and empty subset
cases are preserved. No mismatch was found and no statement changes were made.

## Validation

The prescribed `scompile.py Q20 lem-sfb-integral-descent-flat-monomorphism-subset`
compiled the delivered file on the server successfully (exit 0), with no errors
or warnings. The library module check completed in 1.6 seconds after the queued
sandbox check. No local or global Lean build was run.
