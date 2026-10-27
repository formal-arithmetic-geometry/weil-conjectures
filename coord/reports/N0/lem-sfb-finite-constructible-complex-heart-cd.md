## Worker report

The module `Sheaf.Paper.FiniteConstructibleComplexHeartCd` states
`AlgebraicGeometry.ProEtale.finite_constructible_complex_heart_cohomology_vanishes`,
with its sole proof `sorry`. It introduces no definition and no auxiliary axiom.
The node's statement and accepted stage-1 proof split are unchanged. The preserved
sandbox contained no earlier Lean module or report, only dispatcher brief markers.
The assignment is stage 2, as confirmed by the live queue, and the live item has no
Lean binding. The previous unchanged-item failure concerned the already accepted
split; this delivery supplies its missing Lean statement.

Clause-by-clause rendering:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The condensed commutative coefficient ring
  is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj Λ` and
  `IsCommMonObj Λ`. The explicit six-way hypothesis `hΛ` follows the source order:
  finite discrete commutative ℓ-power-annihilated A; ℤ_ℓ; the valuation ring of a
  finite intermediate extension E; ℚ_ℓ; E; and the fixed algebraic closure.
  `PadicAlgCl.FiniteIntermediateField ℓ` implements finite extensions inside that
  fixed algebraic closure. Monoid-object isomorphisms identify coefficients as
  rings, retaining their additive and multiplicative structures. Quantifying over
  the finite discrete A in `Type 0` loses no finite ring up to isomorphism.
- `Profinite.continuousMapRingObj` and `Profinite.padicIntegersRingObj` use the given
  induced topologies. In particular the Omega clause uses
  `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`, all continuous functions, and
  deliberately does not use the distinct `Profinite.padicAlgClRingObj`.
  The recorded `IsLocalizingAdmissibleCoefficient` also admits that distinct
  finite-subextension-valued ring, so replacing these six clauses by that predicate
  would change this node. Its owning module is imported for the coefficient data;
  its broader predicate is not substituted.
- `(X : Scheme.{u}) [IsAffine X]` is exactly the affine ambient scheme.
  `Scheme.ProEt.topology X`, `X.ProEt`, and `condensedRingObj Λ X` are the existing
  small site and point-pulled-back coefficient. The category used throughout is
  precisely the internal module-object category `Mod (Sheaf ...) (condensedRingObj Λ X)`.
  Schemes and profinite tests have size u; the site's objects and module sections
  have size u+1, and site morphisms have size u. There is no extra equality of
  independent site universes and no additional smallness assumption.
- `K : CochainComplex (Mod ...) ℤ` supplies actual module maps satisfying d²=0.
  `hfinite : ∃ s : Finset ℤ, ∀ n : ℤ, n ∉ s → IsZero (K.X n)` means exactly
  that only finitely many terms are nonzero, with zero understood categorically.
  `hconstructible : ∀ n : ℤ, IsConstantModelConstructible Λ X (K.X n)` uses the
  dependency's finite constant scalar-model constructibility, term by term.
  There is no condition that the differential matrices be constant or share a model.
- `K.homology 0` is the abelian-category kernel modulo image defining N_K. In the
  cochain shape these are the differentials from -1 to 0 and from 0 to 1.
  No assumption at all is made on this module's constructibility or completeness.
- `(d : ℕ)` covers all nonnegative integers. `hcd` quantifies over every scheme V
  and every affine étale morphism `v : V ⟶ X`, using `[IsAffine V] [Etale v]`.
  `V.HasTorsionEtaleCohomologicalDimensionLE d` is the recorded local-section torsion
  definition: it quantifies over `F.IsTorsion`, with no uniform annihilator. Its
  natural-number degree convention is equivalent here to the node's integer
  convention because d is nonnegative and negative cohomology of a heart object
  is zero. No arithmetic restriction is imposed on V or on ℓ on X.
- `(U : X.ProEt) [IsAffine U.left]` supplies every affine pro-étale object, with
  `U.hom` its actual structure map. `CondensedRing.upperStar Λ U.hom` is the
  recorded module inverse image, applied to `K.homology 0` before inserting it
  by `DerivedCategory.singleFunctor _ 0` in the ordinary derived category.
- The displayed output is
  `IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj (...))`, for every
  integer q with `(d : ℤ) + 2 < q`. Inside it,
  `(condensedModuleSections Λ U.left).rightDerivedFunctor` derives the entire
  evaluation functor FROM MODULES to abelian groups, using the existing total
  K-injective right-derived construction. It is not derived evaluation after
  first forgetting the module action in the derived category. This is the stated
  ordinary, uncompleted RΓ on U of v* N_K[0]. There is no length in this bound.

Dependency declarations used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`: existing coefficient objects via
  its public imports; its broader admissibility predicate is read but not used as
  this node's hypothesis, for the reason above.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme maps.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, through the torsion-dimension definition.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`, and objects' structure maps.
- `def-weil-size-convention`: the explicit universe parameter u and the existing
  site and section universes implement this metatheoretic convention.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback` expose the existing total derived construction;
  its public upstream interface supplies `CondensedRing.upperStar` and
  `CategoryTheory.Functor.rightDerivedFunctor` used in the displayed statement.
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` (and its actual
  `HasFiniteConstantLocalModel` / `IsFiniteConstantStratified` definitions, read in full).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `HomologicalComplex.homology` gives N_K without any private copy.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `AlgebraicGeometry.ProEtale.condensedModuleSections`, the exact existing terminal
  evaluation from module objects to abelian groups. Its already landed definition
  owner is `def-sfb-condensed-module-sections` (Q03, `existing: true`), which is added
  to `stmt_deps`. The statement does not use the pushforward-continuity theorem's
  conclusion. No replacement section functor is defined.

Every currently stated proof dependency's module is imported privately, including
point-pullback composition, exact inverse image, homology preservation, finite
open-closed refinement, ringed localization, internal/section-module equivalence,
open lower shriek, lower star, K-injective resolutions, enough injectives, the
right-derived delta-functor, and bounded-below injectives being K-injective.
`lem-sfb-supported-three-term-scalar-cd` has no Lean binding yet, so there is no
module to import for that proof dependency. It is not needed to type the statement;
its future module can be added by the maintainer's proof-import bookkeeping.
The declaration docstring gives all four accepted proof steps and identifies this
still pending analytical leaf, without claiming that HRS proves its full generality.

Edge cases checked before writing: the empty support s is permitted, hence the
zero complex; arbitrary finite supports may miss -1, 0 or 1, and may extend far
beyond them. Zero modules are allowed in every degree, as are zero coefficient
rings (including ℓ^0-annihilated zero rings). The empty scheme and empty pro-étale
objects are not excluded. The identity pro-étale object U=X is included. d=0 gives
exactly q>2. There are no Noetherian, field, finite-type, invertibility, Tor-amplitude,
completeness, common-annihilator or finite-subextension-valued hypotheses. Negative
complex degrees and all integer output degrees remain available. No statement
correction and no new node were needed. No counterexample or new statement fault
was found; the node's existing full-generality reference-WANTED status is retained.

Searches made (2026-10-23 UTC):

1. `msearch.py ... leanfinder`: “On an affine scheme torsion etale cohomological
   dimension bounds pro etale cohomology of zeroth homology of bounded complexes
   with constructible scalar model terms”. Eight results, including
   `Algebra.etaleLocus_eq_compl_support`, `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`,
   `DerivedCategory.isLE_iff`, `DerivedCategory.isGE_iff`, and projective-dimension
   results. None states this finite scalar-model pro-étale theorem.
2. `msearch.py ... loogle 'CondensedMod, CochainComplex'`: zero hits.
3. `msearch.py ... grep 'constructible.*cohomolog|cohomolog.*constructible|torsion.*dimension'`:
   two irrelevant lines in `Mathlib/Algebra/Polynomial/Module/FiniteDimensional.lean`.
4. `msearch.py ... leansearch`: “Cohomology modules of finite complexes of
   constructible pro etale sheaves have cohomological dimension at most torsion
   etale dimension plus two”. Eight results on group cohomology, formal étale
   cotangent homology, sheaf finite presentation, cochain modules, and condensed
   discrete colimits. None matches this statement.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for finite constructible
   complex hearts/cohomology, and `grep -rn` for the item id in `lean/WeilConjectures`:
   no exact theorem. The consumer `TorsionCdTopologicalSerreTransfer.lean` cites the
   item only in its proof plan and concerns the different weak Serre coproduct hull.
   `QcqsProperSerreHeartBound.lean` concerns proper pushforward rather than this
   affine finite-complex estimate. These supplied matching coefficient conventions,
   not an existing declaration for this node.
6. `rg` in project sources for module sections and derived evaluation found the
   already recorded `condensedModuleSections`; its full definition was read and reused.
   `dag/lean_names_upstream.json` has no competing declaration with the chosen name.

Validation: `scompile.py N0 lem-sfb-finite-constructible-complex-heart-cd` compiled
this file separately both as sandbox module (2.5 s) and under its library module
name (2.7 s), with no errors or non-sorry warnings. All lines are at most 100 columns.
The live repository was only read; all authored files are in the assigned sandbox.

## Second reading by N0

A second in-thread reading reopened the node and the completed module and checked
all clauses above. The finite condition is on TERMS, rather than bounded
cohomology; constructibility is imposed on terms, not on N_K. The homology is
computed in the module category before actual module pullback. Derived sections
are derived from modules, rather than from underlying abelian sheaves. The six-way
coefficient list omits the extra finite-subextension-valued clause of the broader
admissibility predicate. The bound is q>d+2, with arbitrary differentials, arbitrary
finite length and every affine pro-étale object. The hcd condition uses locally
torsion sheaves, not common-annihilator torsion. All these match the node; this
reading found no mismatch requiring a change. This was an in-thread rereading by
the assigned sole worker, not an independent agent review: the dispatch brief
forbids starting other agents, and the maintainer's independent delivery review
is the external check.

## Repair of return e55dbe055025

H2 and the mechanical finding are repaired: replaced the added statement dependency
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` with the existing definition
node `def-sfb-condensed-module-sections`. Read that node's statement and Lean record
and the actual abbreviation at
`Sheaf.Paper.CondensedQcqsPushforwardContinuity:127–135`: its body forgets the module
action and evaluates at the terminal pro-étale object, exactly the sections functor
used here through its total right derived functor. The theorem's continuity
conclusion is not a premise of this statement. Updated the dependency list above.
The Lean module, its signature record, the mathematical statement and all other
node fields are unchanged. Compared the retained packet with current main by
reading the files: before repair only `lean` and the one added `stmt_deps` entry
differed; after repair only `lean` and the definition-node addition differ.
The initial saved-packet dry run passed as commit `0a253d6ba61`; the explicit
review finding still required this dependency-ownership repair.

The repair self-check reread the definition owner and the unchanged theorem's use
of `condensedModuleSections Λ U.left`, and confirmed that the existing public
import still supplies the exact declaration. No new node, dependency module or
statement correction is involved. The maintainer's accepted clause-by-clause
review remains applicable to the unchanged Lean file.

Repair validation: the prescribed `scompile.py` compiled the unchanged module
cleanly in sandbox mode (2.5 s) and library mode (2.7 s). The self-check confirmed
that relative to current main the node differs only in `lean` and the addition of
`def-sfb-condensed-module-sections`, that `lean.statement` is the verbatim theorem
signature, and that JSON formatting, line width and the sole sorry proof conform.
