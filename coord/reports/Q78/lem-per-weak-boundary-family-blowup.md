## Worker report

The delivery states `AlgebraicGeometry.BoundaryFamily.weak_boundary_family_blowup` in
`Sheaf.AlgebraicGeometry.WeakBoundaryFamilyBlowup`. Its proof is `sorry`; its docstring
contains all ten proof steps of the current node, including their dependency citations.
The construction it uses is supplied by the new definition node
`def-per-weak-boundary-family`, module `Sheaf.AlgebraicGeometry.WeakBoundaryFamily`.
All definitions have actual data and there are no other postponed theorems.
The item's statement, proof, proof dependencies, existing correction, and other fields
are unchanged. Only `lean` and the addition of this new definition to `stmt_deps` change.

Read the current item, every statement dependency's statement and Lean record, and
the recorded source declarations and docstrings. Read ILO VIII 4.2.4--4.2.13,
printed pp.119--122, from the local PDF, including all of 4.2.8, 4.2.9 and 4.2.11.
The stage-1 accepted correction of exact length to an upper bound remains intact.
`blueprint_refs.py ancestor` identifies `lem-per-artin-gabber-affine-curve`.
There is no released repair note for this item in the read clone.

The hypothesis and clause mapping is as follows.

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Finite indexed family on the given scheme | `{I : Type v} [Fintype I]`, `S : BoundaryFamily.{u} I`, with `S.scheme`, `S.boundary`, `S.family`. The index universe is independent of the scheme universe. |
| Noetherian regular ambient scheme | The first two conjuncts of `hS : S.IsWeak` are `IsNoetherian S.scheme` and `IsRegularScheme S.scheme`. Mathlib's former class includes local Noetherianity and compactness. |
| Strict normal crossings boundary | The next conjunct is the dependency predicate `IsStrictNormalCrossingsBoundary S.boundary`. |
| Nowhere dense closed subschemes | `∀ i, IsNowhereDense ((S.family i).support : Set S.scheme)`. Each ideal defines the actual closed immersion `(S.family i).subschemeι`; ideal sheaves encode closed subschemes without choosing a presentation. |
| Every nonempty-index scheme-theoretic intersection | `intersection J := ⨆ i ∈ J, S.family i`, the sum of ideals; every geometric clause quantifies `J.Nonempty`. |
| Regularity and boundary-compatible parameters of those intersections | The last conjunct of `IsWeak` is `∀ J, J.Nonempty → IsRegularWithBoundary S.boundary (S.intersection J)`. This predicate includes `IsRegularScheme L.subscheme` and pointed étale affine neighbourhoods with one regular parameter system, injective coordinate selections for center equations and boundary factors, exact affine ideal equalities, and germ equalities. It imposes no containment in the boundary. |
| Deduplicated nonempty inclusion-minimal intersections | `IsMember L` uses existence of a nonempty index subset and equality of ideal sheaves; `IsMinimal L` adds `L ≠ ⊤` and maximality for ideal inclusion. Ideal order reverses subscheme inclusion. |
| Their union and pairwise disjointness | `center := ⨅ L : {L // IsMinimal L}, L.val`; the first conclusion says distinct such ideals have `V ⊔ W = ⊤`, so their scheme-theoretic intersection is empty. |
| Center regular and with normal crossings with B | `IsRegularWithBoundary S.boundary S.center`. The predicate allows the empty center. |
| Actual blowup and exceptional divisor | `S.step.scheme` is exactly `S.center.blowup`, with projection `S.center.blowupMap`; the exceptional ideal is `S.center.comap S.center.blowupMap`. It has a regular subscheme and is invertible. |
| Reduced inverse image of B union C, SNC and divisorial fs log regular | `step.boundary := ((S.boundary ⊓ S.center).comap S.center.blowupMap).radical`; `S.step.IsWeak` includes its SNC property and regular ambient scheme. `S.step.HasLogRegularBoundary` uses the existing divisorial log regular pair on exactly its dense complement, with local Noetherianity explicitly existentially supplied. |
| Strict transforms and all their intersections | `transform L` is the kernel of the existing `strictTransformMap L.subschemeι S.center.blowupMap S.center.support.compl`, so uses scheme-theoretic closure. `step.family i := transform (family i)`. The displayed equality is `step.intersection J = transform (intersection J)`. |
| All new intersections regular and boundary compatible | The last conjunct of `S.step.IsWeak`. It also retains nowhere density for iteration. |
| Exact exceptional ideal factor | `exceptionalPart L` pulls back the intersection of precisely those minimal ideals V for which `L ≤ V`. These are exactly the center members contained in V(L); pulling them back gives the union of the exceptional components whose images lie in V(L). Its invertibility and `L.comap p = transform L * exceptionalPart L` are stated for every nonempty J. The ideal, including its multiplicity one, is prescribed, not chosen by an existential. |
| Iteration of this very operation | `level 0 = S`, `level (k+1) = (level k).step`. `toBase` is the actual composite of blowup maps; `iteratedTransform` repeatedly uses the actual closure construction. |
| Termination and general upper bound | `∃ n, n ≤ S.height ∧ ... ∧ (S.level n).Done`. `height` is the supremum of lengths counted in members of strict chains of distinct proper intersection ideals. The collection is finite; reversing ideal order preserves chain length. The zero chain is allowed. |
| At most the number of indices in the intersection-closed, cardinal-bounded case | `Nat.card {L // S.IsMember L} ≤ Fintype.card I → n ≤ Fintype.card I`. The collection of nonempty-index intersections is automatically closed under intersection: use the union of index subsets. Thus no separate, tautological closure hypothesis is added. Counting all distinct intersection ideals, including the unit ideal if it occurs, follows the node's distinct-members convention. |
| Early stopping, including empty family | `∀ k < n, ¬ (S.level k).Done`, and `S.Done → n = 0`. Only the prefix through n belongs to the finite tower; the auxiliary recursion beyond n asserts no extra blowups of the construction. Empty I makes `Done` vacuous, hence gives exactly length zero. |
| All intermediate stages are valid | `∀ k ≤ n, (S.level k).IsWeak`, with regular boundary-compatible centers, regular exceptional divisors and log regular new boundaries for each retained blowup. |
| Compatibility with all original intersections through the tower | `(S.level k).intersection J = S.iteratedTransform (S.intersection J) k` for k ≤ n and nonempty J. |
| Empty final strict transforms and invertible original total ideals | `iteratedTransform (intersection J) n = ⊤` and `((intersection J).comap (toBase n)).IsInvertible`. Unit ideal means the empty closed subscheme. |
| Isomorphisms, including permutations | Quantify over any finite K, a family T, an equivalence `σ : K ≃ I` and an isomorphism e. `PreservesFamily` requires only that e identify the ideals after σ. It imposes no boundary-preservation premise. The same n is the first terminating level for T. The unique family E of level isomorphisms starts at e, commutes with all maps to the input and adjacent projections, and preserves the indexed ideals. If e also preserves B, E preserves all new boundaries. Uniqueness pins down the canonical comparisons and entails identity and composition compatibility. |

Dependency declarations reused, with their owning modules:

- `AlgebraicGeometry.IsRegularScheme`, `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  locally Noetherian plus the existing stalkwise `IsRegular` class.
- `AlgebraicGeometry.IsLocallyNoetherian` and `IsNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`,
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`.
- `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, used through ideal-subsheme inclusions.
- `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`,
  `WeilConjectures.Blowup.Gluing`.
- `AlgebraicGeometry.strictTransform`, `strictTransformMap`, and its closed-immersion instance,
  `WeilConjectures.Compactification.StrictTransform`. The node's old line number is stale;
  the current declarations were read at lines 143ff and 425ff.
- `AlgebraicGeometry.EtaleLogStructure`, `FineSaturatedLogScheme.IsLogRegular`,
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; no private log structure is substituted.
- `AlgebraicGeometry.Scheme.nilradical` and `IdealSheafData.radical`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; `subscheme` and `subschemeι`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `IsLocalRing.IsRegularSystemOfParameters`,
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`.
- `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`,
  `Sheaf.AlgebraicGeometry.LogRegularPair`, cited by the new definition node.
- `IdealSheafData.IsInvertible`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, uses regular principal
  ideals, so retains the effective Cartier condition, not just abstract local freeness.

Recorded proof modules are imported privately, including both new parameter lemmas and
`WeilConjectures.Blowup.FlatBaseChange` from the closed upstream audit records. The existing
Mathlib finite-type-over-Noetherian input is provided by Noetherian and quasi-compactness
imports. The three proof nodes without usable declarations on this snapshot are
`lem-per-regular-boundary-divisorial-chart`, `lem-sfb-transverse-prime-ideal-parameters`, and
`lem-trf-labelled-coordinate-boundary-globalization`; no import is invented for them.
They are proof inputs only and do not prevent this stage-2 statement.

Edge cases checked before and during the reading:

- Empty I: no nonempty J, no minimal ideals, center is the unit ideal, height zero,
  and the chosen finite prefix has length zero. No `Nonempty I` instance is imposed.
- All Y_i empty: every intersection ideal is unit; the same stopping case applies.
- Empty ambient scheme: regularity is vacuous and unit ideals represent the empty subschemes;
  no nonempty geometric point or dimension hypothesis is introduced.
- Duplicate Y_i or duplicate intersections: `IsMember` is a set of actual ideals,
  and the center and height deduplicate by equality of ideals.
- Empty boundary: r=0 is allowed and the boundary product is 1; centers need not lie in B.
- Codimension-one center: its blowup may be an isomorphism but it still removes the
  centered strict transform; the exceptional ideal retains the original Cartier ideal.
- Originally empty intersections and the unit exceptional factor: all factorization
  assertions include them. An empty selected set of minimal strata has unit ideal.
- Disconnected strata: no equality between n and height is asserted. The already-reviewed
  example on A^1 with V(t(t-1)), V(t), V(t-1) has height two but stops after one stage.
- Universes: u, v and w are explicitly bound; coefficients and schemes are not restricted
  to a field or characteristic, and no separation assumption is added.

Searches actually run using msearch.py (the exact logged records are in the new node):

- LeanFinder: "Blowing up minimal intersections of a weak normal crossings finite family
  preserves regularity strict transforms and gives a canonical terminating principalization
  tower". Eight normalization/standard-smooth hits; none is the statement.
- Loogle: "AlgebraicGeometry.strictTransform, AlgebraicGeometry.Scheme.IdealSheafData.blowup".
  No hits; the service reports unknown identifier for the upstream strict transform.
- Mathlib grep: "WeakBoundary|weakBoundary|NormalCrossings|BlowupTower" in AlgebraicGeometry.
  No hits.
- LeanSearch: "finite weak normal crossings family minimal intersection center canonical
  iterated blowup". Eight hits, including set finite-intersection closure and ideal-sheaf
  support_iSup; none defines the weak family, coordinate condition or canonical procedure.
- LeanFinder: "regular closed subscheme has normal crossings with a strict normal crossings
  boundary regular parameters finite intersection family minimal center blowup iteration".
  Eight normalization hits; no exact match.
- Mathlib grep: "WeakBoundary|weakBoundary|NormalCrossingsWith|normalCrossingsWith|BlowupTower".
  No hits. Local rg of WeilConjectures and Sheaf for these notions and the proposed names
  found no exact match. The node-id grep in WeilConjectures found no existing statement.
- DAG and blueprint searches: the related nodes concern theorems, the ordinary arbitrary
  resolution tower, the adapted labelled-coordinate condition, or permissible centers.
  `blueprint_refs.py search` found no blueprint definition for weakly snc or minimal strata.
  The existing `IsPermissibleCenter` additionally requires containment in B and m>0;
  `HasAdaptedNormalCrossingsCenter` is a different labelled Zariski condition.

No statement dispute or new statement correction is claimed. Server compilation through
scompile.py passes for each file separately in dependency order, with no errors or
non-sorry warnings. No local/global build and no direct Git mutation were run.

## New nodes

`def-per-weak-boundary-family` defines the missing weak finite boundary family and the
specific canonical minimal-center operation, its intersection-poset height, iterated
levels/maps/strict transforms, and predicates for stopping and preserving the family.
It also gives the exact étale coordinate meaning of regularity with the boundary and
wraps the existing divisorial log-regular-pair predicate on the prescribed complement.
Its source is ILO VIII 4.2.4--4.2.11 and VI 1.7. Its real constructions reuse ideal-sheaf
sums/intersections, blowups, scheme-theoretic strict transforms, radical ideals and the
existing parameter predicate. The searches above distinguish it from the stricter
permissible-center notion and the arbitrary `OrdinaryBlowupTower`. This is a definition
node only: it claims neither preservation nor termination, which remain in the item.
All supporting functions are listed in its `lean.declarations` with source docstrings.

## Second reading by Q78

This is a second clause-by-clause check by the same dispatched worker; the dispatcher
forbids starting another agent and the maintainer supplies the independent review.
I reopened the current node, the definition module and the theorem signature.

The key checks were the reversed ideal order in `IsMinimal`, sum versus intersection
of ideals, the exclusion of empty index subsets, scheme-theoretic rather than
support-only strict transforms, the exact exceptional factor, the count of members
rather than edges in `height`, and the first terminating prefix rather than an
unconditionally continued tower. Those agree with the node. `exceptionalPart` selects
whole minimal strata contained in Y_J: any other minimal stratum is disjoint from Y_J,
so this is precisely the union of exceptional components in the node.

One mismatch found and corrected during this reading: the first draft of the comparison
clause required preserving B. The node requires family-preserving isomorphisms without
that additional hypothesis. The final clause uses `PreservesFamily` alone; preservation
of the transported boundaries is a conditional additional normalization when B is also
preserved. Thus the underlying tower comparison covers arbitrary family isomorphisms,
including all index permutations. The new definition's statement was updated to record
both preservation notions. The Lean node record was regenerated verbatim afterwards.

The comparison is uniquely characterized by its base and transition equations. Any two
such maps agree off the centers, and regularity gives reducedness while blowups have
separated projections, hence the maps agree everywhere. Therefore uniqueness expresses
the canonical, composition-compatible comparisons of the construction rather than a
choice of arbitrary maps. There is no claim that the disconnected-stratum upper bound
must be attained. All center and boundary definitions are independent of the theorem's
postponed proof. The sole compiler repair was making `Scheme.Opens.toScheme` explicit
for the boundary complement. No dependency statement was changed.

Delivery preflight initially requested the current schema field `import_flags` on the new
definition node. Added the empty list; no mathematical field changed. The route-pivot
advisory concerns the shared SNCBoundaryParameterCriterion module, imported for the
item's accepted proof dependency `lem-sfb-snc-boundary-parameter-criterion`; it does not
introduce a dependency on the retired perverse alias.
