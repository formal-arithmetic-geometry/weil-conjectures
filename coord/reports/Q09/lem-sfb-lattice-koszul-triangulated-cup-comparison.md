## Worker report

The delivery states `Profinite.DiscreteLattice.TriangulatedCup.lattice_koszul_triangulated_cup_comparison`
in `Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison`, importing the new
`Sheaf.CategoryTheory.LatticeAlgebraDerivedCup` definition module and its normalized
`Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor` infrastructure. It uses the existing
`DiscreteLattice.KoszulModel`, `Comparison`, invariant limit, and total right derived functor.
Its total is a construction: apply the existing Koszul functor degreewise, flip the
bicomplex so Koszul degree is first, and apply Mathlib's signed total functor. Definitions
have real data. Every new theorem is postponed with `sorry`; each helper theorem
has a source and the corresponding part of the node's proof in its docstring.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring on the coherent profinite site | `R : Profinite.CondensedRing.{u}`, `[IsCommMonObj R.X]`; these are the recorded ring and internal-module tensor, with explicit universe `u`. |
| All ranks including zero; discrete lattice and equivariant internal modules | `r : ℕ`, recorded `Group r = Multiplicative (Fin r → ℤ)`, recorded `Equivariant R r = Action (Modules R) (Group r)`. |
| Existing finite Koszul complex, ordered signs and invariant inclusion | `K : KoszulModel R r`; its recorded `coordinates`, `differential`, `maps`, `augmentation`, `augmentation_zero` are retained. |
| Bounded-below complex and differential `d_K + (-1)^a d_P` | `CochainComplex.Plus`, `total`, `bicomplex`, `totalPlus`; the Koszul-first flip puts `a` in the first index of Mathlib's standard signs `(1, (-1)^a)`. |
| Induced functor on ordinary `D⁺` | `TriangulatedModel.functor` has source and target `DerivedCategory.Plus`; `factor` identifies its localization with the constructed total. |
| Triangulated functor | `totalShiftIsoApp` composes `mapCochainComplexShiftIso`, flip and total with `totalShift₂Iso`, giving sign `(-1)^(a*n)` on Koszul degree a. `totalCommShift` uses exactly this family. `TriangulatedModel.factorShiftCompatibility` requires the descent to preserve it, while `triangulated` requires preservation of distinguished triangles. |
| Isomorphism of triangulated functors to the actual derived invariants | `TriangulatedModel.iso` and `shiftCompatibility`; the target is the recorded `derivedInvariants`, with the inclusion of `D⁺` into the ordinary derived category. The isomorphism itself implies that the derived invariants lie in `D⁺`. |
| Simultaneous extension of the natural comparisons on modules | The same existential `c r : Comparison R r (K r)` is used everywhere; `ComparisonProperties.extendsModules` identifies it with `onComplex` through the coordinate-normalized `singleIso`. |
| Connecting arrows of every equivariant SES and termwise exact Koszul SES | `ComparisonProperties.connecting` quantifies over `ShortComplex` and `ShortExact`, asserts exactness of its Koszul and single-complex images, and equates the two actual `DerivedCategory.triangleOfSESδ` arrows after the specified shift comparison. |
| Invariant-inclusion normalization | `Comparison.normalization`, and `ComparisonProperties.normalization` on all bounded-below complexes. `totalInclusion` uses the recorded augmentation in Koszul degree zero. |
| Identity at rank zero, including complexes | `IsRankZero`; the invariants identification has degreewise map exactly the limit inclusion, the total identification is exactly the empty-subset coordinate, and `onComplex` equals their composite with the ordinary derived unit. These are the canonical identifications with the original underlying complex. |
| Commutative internal R-algebra with commuting R-algebra automorphisms | `DerivedCup.Algebra R r = Mon (Equivariant R r)` together with `IsCommMonObj B.X` in the final theorem, for Mathlib's diagonal action tensor. A monoid object in internal R-modules is an internal R-algebra; the existing commutativity class gives exactly the commutative ones. Its multiplication and unit are equivariant, and group actions are automatically automorphisms. |
| B flat over R, without flatness of R as an external hypothesis | `ObjectProperty.flat B.X.V`, only in the final implication for B. This is exactness of left and right tensor; symmetry identifies the two, so it is exactly the node's flatness condition. |
| K-flatness against every acyclic complex | `CupComparison.kflat` quantifies over all cochain complexes, with `X.Acyclic → (K(B) ⊗ X).Acyclic`. |
| Chain pairing, including the twisted Leibniz equation | `CupComparison.star` is an actual morphism of cochain complexes. |
| Full signed sum over ordered disjoint partitions | `CupComparison.coordinates` tests every input summand A,C and output summand I; its entry is zero unless A,C are disjoint and their union is I. The nonzero entry is the specified integer sign times `(identity ⊗ action(T_A))` followed by equivariant multiplication. Finite biproduct and tensor universal properties make this matrix exactly the stated sum. |
| Inversion count and empty operator product | `(A.val.product C.val).filter (fun ac ↦ ac.2 < ac.1)` counts the inversions. `∏ i ∈ A.val, generator i` is the empty-group product when A is empty; applying the action gives the identity. |
| Invariant algebra unit in degree zero | `CupComparison.unit` has source the actual regular tensor unit in degree zero; `unitCoordinates` is `MonObj.one` on every degree-zero coordinate. Equivariance of the algebra unit makes it invariant. |
| Ordinary tensor of the K-flat complex represents derived tensor | `CupComparison.tensorModel` makes the existing localization tensorator invertible. No separate or arbitrary derived tensor is introduced. |
| Same lambda identifies star with the canonical cup in the derived category | `CupComparison.cupEquation` is the node's equality precomposed with that invertible tensorator. The helper `cup` is the lax pairing of the normalized derived adjunction followed by the localized equivariant multiplication of B. |
| Canonical derived cup, including trivial B=R | `trivialAdjunction` is uniquely determined by the invariant inclusion; `ordinaryDerivedIso` preserves the computation unit, and `derivedCore` is normalized on flat K-flat representatives and the localized ordinary unit. For trivial B=R, the theorem now asserts `∀ r, ∃ E : RestrictionCup.Bridge R r, RestrictionCup.Compatible R r E`. `Compatible` explicitly equates binary cups and units through the pinned `cohomologyIso`, retaining both localization universes. |
| Comparison sends the invariant unit to the canonical derived unit | `CupComparison.unitEquation`, with `cupUnit` defined from the normalized derived adjunction unit and B's original equivariant unit. Its source is R[0] directly. |
| No nonzero-ring or characteristic restriction | There are no `Nontrivial`, characteristic, invertibility, averaging, or division hypotheses. |

The generic `derivedTensorNormalization` elaborates the representative and unit equations
over abstract coefficient categories with independent localization universes, then specializes
them to the existing lattice category. Exported priorities for existing instances prefer the canonical generic K-flat constructions over
definitionally equal shortcut instances, so specialization uses one tensor consistently.

The tensor infrastructure theorems are conclusions, not extra assumptions on R. The
closed structure uses a universal right adjoint. In `Profinite.DiscreteLattice.DerivedCup`, all chosen non-propositional helper
data (`trivialAdjunction`, `ordinaryDerivedIso`, `trivialCore`, `derivedCore`, and
`singleMultiplication`, via `singleMultiplicationExists`) are determined by explicit uniqueness and normalization equations.
The theorem's models are existential conclusions with specified coordinates and maps.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and `ModObj`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`
  and its sectionwise action/invariant-inclusion interpretation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`:
  `Modules`, `Group`, `Equivariant`, `generator`, `invariants`, `derivedInvariants`,
  `Subsets`, `KoszulModel`, `Comparison`, `derivedUnit`, and their recorded instances.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` and its public cup
  infrastructure: the canonical pairing is the right-adjoint lax pairing using the
  normalized invariant adjunction and the K-flat tensor comparison. The lattice module
  records ordinary `Action` objects in localization universe u+2, while the general
  sectionwise calculus uses `ActionModule` and universe u+1. The delivery retains the
  lattice objects and writes their canonical adjunction and tensor normalizations
  explicitly; it imposes no equality of universes and no topological presentation of R.
- The metatheoretic size dependency is rendered by explicit universes and the recorded
  standard localization universe u+2, without an invented coefficient object.
- Every already stated proof dependency is imported without `public`; the imports
  retain the entire fourteen-step proof plan for stage 3.

Searches actually run:

- `msearch.py ... leanfinder "Koszul complex discrete lattice actions derived invariants triangulated comparison twisted cup product"`:
  eight generic connecting-map/homological-functor hits, including `DerivedCategory.triangleOfSESδ`;
  no lattice triangulated cup comparison.
- `msearch.py ... loogle "Action, CochainComplex, DerivedCategory, Functor.IsTriangulated"`:
  zero hits; diagnostic `unknown identifier 'Functor.IsTriangulated'` (the fully qualified
  class is found in the source). This is recorded as an unsuccessful query, not an exact match.
- `msearch.py ... grep "Koszul|koszul" CategoryTheory`: zero hits.
- `rg` of `WeilConjectures/` and `Sheaf/CategoryTheory/` for `Koszul`, `koszul`,
  the exact item id, and `DiscreteLattice|lattice.*(cup|Koszul)|Koszul.*triangulat`:
  the existing lattice module supplies only the finite module comparison; ringed Koszul
  towers and derived completion modules concern other objects. No existing declaration
  states this item. Exact item-id search of `WeilConjectures/` has no hits.

Edge cases checked: rank zero (only the empty subset), degrees outside [0,r] (empty
subset index), rank-one mixed products `xy` and `xT(y)`, zero algebra/module and zero ring,
and characteristic two. An executable finite coefficient check tested the twisted
Leibniz equation on functions on `(Z/3)^r` with coordinate shifts, over F2 and F5,
for ranks 0 through 3, all homogeneous degree pairs, and three random samples per pair:
180 checks passed. This is a sign sanity check, not a Lean proof.

The node statement, proof and existing metadata are unchanged. Its `stmt_deps` gains
the new algebra-valued canonical cup definition and the pinned regular-cup bridge described below. There is no statement
dispute or correction.

## Second reading by Q09

Self-check of the node and delivered signature, with the maintainer's independent
reading still required as specified in the dispatcher brief. No other agent was started.
The clause table above was checked against the original full statement, including the
connecting-arrow, same-lambda, invariant-unit, K-flatness, and r=0 clauses. The cup equation
uses the same module comparison whose extension is the triangulated comparison; the
canonical cup is specified independently from star. The repaired descent preserves the
constructed total shift, and the regular-cup identification is now a Lean equation. The rank-zero clause covers every
bounded-below complex. The unit is kept as a morphism from R[0], avoiding unnecessary
identification of separate localization-universe tensor units. All input coefficients,
actions, and finite subset coordinates are the recorded dependency definitions.

## New nodes

`def-sfb-lattice-algebra-derived-cup` defines the missing canonical derived cup for
arbitrary equivariant algebra coefficients in the recorded ordinary lattice action category.
Its module is `Sheaf.CategoryTheory.LatticeAlgebraDerivedCup`, with main declaration
`Profinite.DiscreteLattice.DerivedCup.cup`, and it also defines the canonical `cupUnit`.
The existing `CondensedDerivedCup` uses sectionwise `ActionModule` objects, localization
universe u+1, and regular coefficients. The new definition retains the lattice dependency's
ordinary `Action` objects and localization universe u+2, and allows all equivariant B.
It reuses the recorded invariant limit and derived functor, Mathlib's monoid/commutativity,
the generic K-flat tensor construction, and the existing right-adjoint lax tensor mate.
The ordinary and derived adjunctions and strong tensor comparison are fixed by explicit
uniqueness/normalization equations; no arbitrary cup or arbitrary natural isomorphism is chosen.
All proof-only inputs needed to construct these data are named postponed theorems with
complete proof plans. The new node's statement records their mathematical role.

The cup node cites the seven original input nodes and the new normalized tensor node.
The main item adds the cup definition to `stmt_deps`, so both new nodes are reachable. Blueprint ancestry was checked with `blueprint_refs.py
ancestor`: it returns null for this agent-expanded chain, and the new node records null
and the full via chain with the item prepended. `blueprint_refs.py search lattice cup`
found two unrelated imported nodes. The new node records the exact search queries and
results: LeanSearch returned eight representation-adjunction/counit hits; LeanFinder
returned eight Tor/coinvariant hits; Mathlib grep returned five generic right-adjoint
lax tensor hits. Direct DAG and project searches found only the sectionwise regular cup
and the consuming lattice lemmas, so no existing declaration duplicates this definition.

The derived multiplication uses `DerivedCategory.Q_obj_single_obj` through the canonical
`singleQIso`. Its two presentations are identified explicitly around localization of the
original single-complex multiplication; the map itself is unchanged mathematically.
The generic normalizer is partially applied, so Lean infers its already determined
comparison domain. All localization universes in the specialization are explicitly u+2.

The canonical cochain tensor is identified with its signed total construction by
`cochainTensor_eq`. The single-complex multiplication is uniquely specified on that
raw total tensor and transported along this canonical equality. The unit uses the
original equivariant algebra unit directly. No file-local instances or notation occur.

`def-sfb-lattice-derived-invariants-tensor` defines the normalized ordinary and derived
trivial-action/invariants adjunction, its strong tensor comparison on flat K-flat
representatives, and the adjoint lax tensor structure. Its module is
`Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor`, primary declaration
`Profinite.DiscreteLattice.DerivedCup.derivedLax`. It separates the independently reusable
adjunction/tensor data from the algebra cup and keeps each file within the standard
compiler budget. Its source is paragraph (3), proof steps 9 and 13 of the lattice input.
LeanSearch found the generic `Adjunction.rightAdjointLaxMonoidal`, action functor tensor,
and representation invariants adjunction; LeanFinder found eight Tor, coinvariant or
homological tensor hits. Grep found the sectionwise regular cup and generic mate APIs,
which are reused, but no normalized derived tensor for the recorded ordinary internal
lattice actions. Blueprint search `derived invariants tensor` found no nodes. The new
node records these actual searches, and its seven statement dependencies are precisely
the original input nodes. Both new nodes have null blueprint ancestor as the original
agent-expanded item does. All their definitions and theorem interfaces were included
in the Q09 second reading above.

Named aliases of the existing cochain, homotopy and derived tensor structures and
localization lax structures let elaboration reuse those exact canonical instances.
The aliases introduce no alternate tensor. The empty-colimit preservation proofs use
the existing tensor adjunctions in the explicit size (0,0), avoiding an undetermined
auxiliary size universe in the generic module-object instance. All aliases are public,
listed in the cup node's declaration record, with source and blueprint docstrings.

The repair also adds `def-sfb-lattice-restriction-cup-comparison`, primary declaration
`Profinite.DiscreteLattice.RestrictionCup.Bridge`. It defines the all-ranks action,
invariant-inclusion, derived-unit and regular-coefficient comparison and its explicit
binary cup/unit compatibility predicate, as detailed point by point below. Source:
paragraph (3), the item's agent-expanded steps 9 and 13. This is not a replacement for
the existing rank-one relative bridge, which has another domain and no all-ranks regular
cup equation. Its searches and why existing declarations do not state it are given below
and in its node record. The main item cites the new node directly.

## Repair of return L (immutable head bdc4ce08b4f8)

The initial prescribed dry run of the saved three-module packet returned OK, commit
11c97a60724. Inspection confirmed that this mechanically valid packet still contained
both mathematical defects identified in the return, so it was retained and repaired.
Current read-only main source and the retained packet were compared through their node
records and module interfaces; delivery tooling refreshes the base at dry run and push.

1. H3(1): `totalShiftIsoApp` constructs the shift comparison by applying flip and total
   to `K.functor.mapCochainComplexShiftIso`, then composing with Mathlib's
   `HomologicalComplex₂.totalShift₂Iso`. Its component sign is `(-1)^(a*n)`, hence
   `(-1)^a` for the generating shift. `totalShiftNaturality` and
   `totalShiftCoherence` are named postponed proof obligations with complete proof
   docstrings, covered by proof step 3 of the item. `totalCommShift` has this actual
   data; it is independent of the derived-invariants isomorphism.
   `plusQCommShift` exposes the existing quotient/Qh shift on bounded-below localization.
   The new field `TriangulatedModel.factorShiftCompatibility` requires
   `NatTrans.CommShift factor.hom ℤ`. Consequently the descended shift is pinned through
   the total, and `shiftCompatibility` can no longer make triangulatedness vacuous by
   transporting an unrelated shift from derived invariants.
2. H3(2): the new definition node `def-sfb-lattice-restriction-cup-comparison` and module
   `Sheaf.CategoryTheory.LatticeRestrictionCupComparison` specify `RestrictionCup.Bridge`
   and `Compatible`. The theorem asserts existence of a compatible bridge for every rank.
   The bridge uses precisely the restriction-calculus ring bundled from the same R and
   its group `ULift (Group r)`, with the usual discrete topology (the group in the
   downstream exterior-cup module), and the recorded ordinary lattice action category.
   Its exact additive equivalence is pinned on every constant action section and
   underlying-module map. For a nonconstant section the finite clopen fibres determine
   its action by sheaf gluing, including the empty test object. Its invariant isomorphism
   is fixed by the two inclusions. The derived natural isomorphism is fixed on EVERY
   complex by both computation units and the exact localization factorization maps.
   The regular-object isomorphism has exactly the underlying-module comparison.
   The base universe transport is the existing exact identity `mapDerivedCategory`,
   explicitly from localization universe u+1 to u+2. `smallModulesDerived` reuses the
   existing K-injective localization; `SmallDerived`, `smallQ`, `raiseFactors`,
   `sectionUnit`, and `smallQLax` supply its datum explicitly at each API boundary,
   avoiding the instance search that fixes a localization universe too early. Its tensorator is normalized by
   `BaseTensorNormalized`, the identity specialization of `derivedTensorNormalization`,
   on flat-term K-flat representatives and the ordinary localized unit; no universe equality is imposed. `cohomologyIso` is built from these
   data. `Compatible` equates the two actual binary cups and both units using that
   isomorphism and tensorator. The unit equation retains the localization isomorphism
   from the derived tensor unit to R[0]. This supplies the identification needed by
   steps 3--4 of `lem-sfb-discrete-lattice-cup-exterior`, including empty products.

The new bridge node defines data and a predicate; it does not assume their existence.
Existence is part of the assigned theorem's conclusion and is explained in its proof
step 13. No definition chooses unspecified objects from an unproved existence theorem.
No old statement, proof step or proof dependency is changed.

Additional source and duplicate checks: read `RelativeLatticeBridge.DiscreteBridge` and
`DiscreteDerivedBridge`, which only cover rank one and do not identify the regular cup;
read the actual full `CondensedDerivedCup.cohomology`, `coefficient`, `cup`, `cupUnit`,
`localizedUnit`, and the restriction calculus, as well as its `CondensedBar.Ring`,
`CondensedAction.ActionModule` and invariant inclusion. The generic Mathlib
`Functor.mapDerivedCategory` already supports the two independent localization universes,
so no separate localization is invented. The new node's search records list actual
LeanSearch, LeanFinder and Mathlib grep queries from this repair. LeanSearch returned
discrete condensed objects and continuous action/invariant APIs, LeanFinder returned
locally constant/discrete condensed module comparisons, and Mathlib CategoryTheory grep
returned zero hits. Direct DAG, upstream WeilConjectures and Sheaf searches found only
the rank-one bridge and existing generic localization interfaces; blueprint search
`discrete action derived invariants comparison` returned zero matches.

Additional self-reading: the signed total is fixed before the triangulated model, and
factor compatibility uses that instance. The two cup equations have the same coefficient
ring and group, with the explicit canonical transport between the recorded universes.
The cohomology comparison is not a free field, and its source, target and regular unit
are all fixed by actual localized maps. Rank zero, empty profinite tests, zero rings,
zero modules and characteristic two add no assumptions or exceptions. No new theorem
proof is filled in this stage.

## Validation

The initial saved packet passed the prescribed preflight and per-file compiles. The
repaired packet is checked below with the prescribed scompile.py and deliver2.py wrappers;
all delivered files are compiled separately, in dependency order, at the standard limit.
The isolated repaired shift interface compiled cleanly (27.0 s sandbox, 25.8 s library),
and the new regular-cup bridge compiled cleanly (47.3 s sandbox, 37.9 s library).
Structure-generation options avoid unused size/injectivity lemmas; the shift definitions
are opaque to ordinary reduction after construction. No compiler limit was changed.
Both localization data are explicit at each API boundary; the smaller one is a named
definition of the existing K-injective localization, not a competing global instance.
All diagnostic commands and tracing options were removed from the four delivered modules.
The combined four-module check exited 0 without errors or warnings: the final theorem
compiled in 26.0 s in the sandbox and 28.3 s under its library module name. The two
unchanged infrastructure modules also passed (45.6 s and 44.1 s library checks).
The prescribed final delivery preflight follows this clean combined check.
