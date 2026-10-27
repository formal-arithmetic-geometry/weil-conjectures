## Worker report

The module `Sheaf.Paper.CompletedProperIndependentOrigins` states
`AlgebraicGeometry.Scheme.completedProperIndependentOrigins` with one `sorry`.
It uses the published map `d.completedExchange sq H`; no definition or canonical
map is copied. No original natural-language statement or proof is changed.

Hypothesis and clause correspondence:

- `(A,I)` is `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`.
  Its inherited fields provide Noetherianity, a finitely generated ideal, additive
  torsion of A/I, and perfectness and finiteness of every positive quotient.
  `n : ℕ` represents the paper's exponent n+1, so no positive quotient is omitted.
- The four schemes and four morphisms are the explicit `Scheme.{t}` and hom binders.
  `sq : ChosenCartesianSquare g' f' f g` retains the chosen fiber product and
  projection equations. `[IsProper f]` is properness of p. There is no condition
  on g and no extra properness assumption on f'.
- `d.derived X` is the actual unbounded derived category of modules over the
  inverse-limit coefficient sheaf `d.completedRing X`. It is not the derived
  category for the discrete constant coefficient ring.
- On all ambient inputs, `d.completedPull` is definitionally strict reduction,
  strict termwise derived tower pullback, then `completedRlim`. Its values and
  its maps give exactly the stated source and target functors P_g Rp_* and
  Rp'_* P_g'. On complete inputs this is completed pullback.
- The specified three factors are already the entire defining body of
  `AdicCoefficientDatum.completedExchange` in `CompletedBaseChangeMap.lean`:
  Rlim of `towerH.hom`, Rlim of `towerV'`, then `directImageRlimIso.inv.app`.
  `towerH.hom` is `towerPull g` applied to `towerProjection f H`.
  `towerV'` in `CompletedTowerCorners.lean` is the prescribed conjugate of
  reduction of the ambient mate by the projection and tensor comparisons.
  Thus the statement concerns the specified map, not an unspecified isomorphism
  or a lift chosen from finite evaluations. Endpoint identifications are those
  already in these definitions.
- The first conjunct quantifies `∀ (H H' : d.derived X) (a : H ⟶ H')`.
  Its equality is exactly Rp'_*P_g'(a) gamma_H = gamma_H' P_g Rp_*(a), using
  Lean's left-to-right composition `≫`. There is no completeness or origin
  hypothesis on either endpoint. This is the naturality condition for the
  existing family of components on the entire ambient category.
- In the second conjunct, `hH : PbcIsIntrinsicallyComplete X d H` is the
  published existential Koszul-unit predicate from
  `BoundedConstructibleComplete.lean:420`. This predicate alone imposes neither
  boundedness nor constructibility, despite its owning module's name. Its
  definition uses the recorded `IsCompletedIntrinsicallyDerivedComplete` and
  the normalized completed-ring coefficient transport.
- `W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n+1))
  ((d.reduction X n).obj H)` retains one bounded-below etale antecedent and its
  comparison isomorphism for each quotient. `RingedEtaleOriginWitness.lean`
  transports the same recorded retained origin pair along the canonical
  constants-to-functions coefficient isomorphism. No transition between the
  W n, no common lower bound, and no constructibility condition is present.
- `IsIso (d.completedExchange sq H)` states invertibility of this same map.
  The final equality identifies it with `d.completedBaseChangeMap sq H ... W`.
  Its completion argument is the published theorem
  `pbcIntrinsicComplete_towerComplete d X H hH`, not an added assumption and
  not an arbitrary identification H with a limit. This supplies invertibility
  of the specified quotient-tower completion unit.

Recorded dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, `AdicCoefficientDatum.derived`, `.reduction`,
  `.completedRing`, and the quotient-finiteness instance.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `completedCompactSupportExchange`, whose proper factor is exactly the same
  `completedExchange` used here. Its open-extension and compactification inputs
  belong to that definition, not to this proper-only result.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, invertibility of the explicit
  completed-coefficient Koszul completion unit.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `FixedEtaleOriginWitness`, reexporting the retained ringed-coordinate
  `FiniteEtaleOriginWitness` in `Sheaf.Paper.RingedEtaleOriginWitness`.
- `Sheaf.Paper.CompletedBaseChangeMap`:
  `AdicCoefficientDatum.completedExchange` and `.completedBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.completedPull`;
  the live Q99 record and all four of its declarations are retained unchanged.
- `Sheaf.Paper.CompletedDirectImageLimits`:
  `AdicCoefficientDatum.directImageRlimIso` and `.towerProjection`.
- `Sheaf.Paper.CompletedRlimFunctor`: `completedRlim`, the actual total right
  derivation of strict inverse limit, and `completedRlim_computation`.
- The already landed nodes `def-weil-pbc-bounded-constructible-complete` and
  `lem-weil-pbc-intrinsic-to-tower-complete` are added to stmt_deps to cite
  `PbcIsIntrinsicallyComplete` from the former's supporting module
  `Sheaf.Paper.BoundedConstructibleComplete`, and
  `pbcIntrinsicComplete_towerComplete` from `Sheaf.Paper.PbcIntrinsicTowerComplete`.
  No new DAG notion or mathematical hypothesis is introduced.

All recorded stated proof dependencies are imported without `public` when
needed only for the proof. Mathlib's `Abelian.functorCategoryAbelian` and
`DerivedCategory.isIso_iff` supply the two proof-dependency leaves.
The declaration docstring carries all six steps of the node's proof, including
strict naturality before evaluation and independent finite-level isomorphism
checks. All theorem proofs in the delivery are `sorry`.

Edge cases checked before writing: zero complexes, empty schemes, zero coefficient
ring, zero and unit ideals when the datum hypotheses hold, empty generating tuples,
identity and arbitrary base-change morphisms, and n=0 (the positive exponent 1).
No nonemptiness, nonzero-ring, nonzero-ideal, chosen generator length, common
cohomological bound, or compatibility assumption is imposed. The ambient
naturality equality also applies when neither object is intrinsically complete.
The small site's object/coefficient universe is t+1 and morphism universe is t;
no additional equality of site universes is required.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "Completed proper base change for derived
  complete proetale modules with independent bounded below etale origins at each
  finite quotient and naturality on all ambient complexes" returned eight
  ordinary adic-completion and etale-base-change declarations, including
  `AdicCompletion.ofTensorProduct_naturality`; none states this derived sheaf result.
- `msearch.py ... loogle '"baseChange", "IsProper"'` returned only
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`.
- `msearch.py ... leansearch` with query "Proper base change for derived complete
  proetale sheaves with independent etale origin at each quotient and naturality
  for arbitrary complexes" returned generic etale/proper base-change results and
  `Condensed.lanPresheafNatIso`; no match.
- `msearch.py ... grep 'completed.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Cc]omplete|[Tt]owerComplete'`
  returned no Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, including the exact node id,
  `completedExchange`, and `independent.*origin`, found the existing map and its
  supporting strict constructions. `CompletedExchangeCoherence.lean:304`
  restricts naturality to complete witnessed endpoints; it is not this statement.
  `CompleteProetale.lean:119` has a private isomorphism lemma for independent
  origins; its public theorem requires compatible origins, so neither supplies
  this public ambient-naturality-plus-independent-origins statement.
- Exact new declaration-name search in the project, upstream and
  `dag/lean_names_upstream.json` found no collision.

Validation of the saved packet before repair: the prescribed
`deliver2.py --no-push` passed server preflight and compilation, reporting
`OK (dry run): commit b3e0b000aa1 passes the preflight and compiles; nothing pushed`.
The corrected packet is compiled and dry-run again before delivery.

No statement correction or mathematical dispute is needed.

## Return repairs

H13: restored `dag/nodes/sec-proper-base-change/def-weil-pbc-completed-pullback.json`
byte for byte from the live read clone. In particular its Q99 lean record still
names `Sheaf.Paper.PbcQbarCompletedPullback`, primary declaration
`AlgebraicGeometry.Scheme.pbcQbarCompletedPull`, and all four declarations:
`pbcQbarIntegralPull_mem`, `pbcQbarPullFamily_existsUnique`, `pbcQbarPullFamily`,
and `pbcQbarCompletedPull`. The public-import chain retains the integral ambient
`AdicCoefficientDatum.completedPull`, also used by the published
`CompletedBaseChangeMap`. No dependency record repair or dependency module is
part of this corrected delivery. The item module and its signature are unchanged.
The earlier dependency-rebinding rationale was incorrect and has been removed.

H11: replaced the former second-reading paragraph with the fresh detailed reading
below, checking the node text against the final file and the actual definitions.

## Second reading by Q23

I opened the node statement and `CompletedProperIndependentOrigins.lean` afresh,
then read `CompletedBaseChangeMap`, `CompletedPullback`, `CompletedTowerCorners`,
the intrinsic predicate and its tower-completeness implication, and the retained
finite-origin structure. I checked each hypothesis and conclusion as follows.

1. The node's adic datum `(A,I)` is the binder
   `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`.
   This uses the published datum with its Noetherian, finite-generation,
   additive-torsion, finite-quotient and perfect-quotient conditions. The ring
   and ideal have not been specialized to a field or a nonzero ideal.
2. The proper morphism `p : V → Y` is `{f : X ⟶ Y}` with `[IsProper f]`.
   The arbitrary `g : Y' → Y` has no additional class assumption. The binders
   for `X'`, `g'`, `f'` and `sq : ChosenCartesianSquare g' f' f g` retain the
   chosen fiber product and both projection equations. No Noetherianity or
   dimension condition is added to the schemes.
3. The ambient category is `d.derived X`, the derived module category over the
   inverse-limit ring sheaf `d.completedRing X`. I checked that `completedPull`
   is defined on that entire category as strict reduction, `towerPull`, then
   `completedRlim`. Thus the two functors in the equality are the node's
   `P_g Rp_*` and `Rp'_* P_g'`, including on noncomplete inputs.
4. The map `d.completedExchange sq H` is precisely the specified ordered
   composite: Rlim of `towerH.hom`, Rlim of `towerV'`, then
   `directImageRlimIso.inv.app`. `towerH` is tower pullback of the projection
   isomorphism. `towerV'` is `towerH.inv ≫ towerV ≫ towerH'.hom`, where
   `towerV` is normalized strict reduction of the ambient exchange. These are
   actual strict-tower arrows; no arbitrary evaluated lift is substituted.
5. The first conjunct binds `∀ (H H' : d.derived X) (a : H ⟶ H')` before
   any completeness or witness premise. Its left side is
   `gamma_H ≫ (d.push f').map ((d.completedPull g').map a)`; its right side is
   `(d.completedPull g).map ((d.push f).map a) ≫ gamma_H'`. In Lean's
   composition order this is exactly the displayed naturality equation in
   the node, from `P_g Rp_* H` to `Rp'_* P_g' H'`. Both endpoints may be
   noncomplete and have no origins.
6. Only the second conjunct binds
   `hH : PbcIsIntrinsicallyComplete X d H`. I read its definition: it is
   intrinsic Koszul-unit completeness transported by the normalized completed
   coefficient comparison, with existential generator/representative witnesses.
   It does not require the bounded-constructible predicate. The term
   `pbcIntrinsicComplete_towerComplete d X H hH` is the proved implication
   used to supply `completedBaseChangeMap`'s Prop argument, not another premise.
7. The same second conjunct binds
   `W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
   ((d.reduction X n).obj H)`. The structure retains a specific object of
   `DerivedCategory.Plus` on the small etale site and a specific comparison
   isomorphism after the canonical finite constants/functions transport.
   Thus it retains the node's pair `(L_n, nu* L_n ≅ H_n)`, and `n = 0`
   covers the positive exponent 1. There is no relation between `W n` and
   `W (n+1)`, and no quantified common lower bound. This agrees with the
   separate choices of `L_n` in Stacks 09C9's proof.
8. The second conclusion is exactly
   `IsIso (d.completedExchange sq H) ∧ d.completedExchange sq H =
   d.completedBaseChangeMap sq H (pbcIntrinsicComplete_towerComplete d X H hH) W`.
   It asserts invertibility of the very same map and equality with the
   specified completed proper exchange. The equality is definitionally
   reflexive because `completedBaseChangeMap` is defined to be
   `completedExchange`; this introduces no additional mathematical claim.
9. I checked zero complexes, empty schemes, the zero coefficient ring, admissible
   zero/unit ideals and empty generator lists, identity/arbitrary `g`, and
   witnesses whose lower bounds vary with `n`. None is excluded by a new
   hypothesis. The site object and coefficient universes are `t+1`, and the
   morphism universe is `t`, as in the dependencies.
10. For H13 I compared the restored node bytes with the live node: identical,
    including the whole lean record and the four Q99 declarations. The integral
    completed-pullback interface remains available under that record's public
    imports. The rejected rebinding is unnecessary and has been removed.

Findings: the theorem matches every hypothesis and clause of the node. No Lean
statement change was necessary. The changes in this repair are restoration of
the live dependency record and replacement of the second-reading report.
