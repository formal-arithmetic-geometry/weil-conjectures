## Worker report

The exact statement already exists in the live module
`Sheaf.CategoryTheory.DiscreteLatticeCupExterior`, declaration
`Profinite.DiscreteLatticeCup.discrete_lattice_cup_exterior` (line 152).
The attempted `existing: true` reuse failed server validation: the unchanged live module
timed out after 60 seconds both in the server overlay and in server confirmation.
Therefore this delivery repairs its existing owning module, preserving all mathematical
statements and canonical morphisms. It adds the two backward-elaboration transparency
options already used by the recorded condensed cup and character dependency modules.
Profiling then identified expensive kernel checks for `splitShift` (27.8 seconds)
and the generated `orderedCup._sunfold` equation (15.4 seconds). The repair names the
unchanged `DerivedCategory.shiftTensorShiftIso` as `shiftedRegularTensorIso` and
expresses the same empty/successor recursion using the explicit dependent `List.rec`.
This avoids repeated checking of a large shifted-tensor composite and the redundant
generated recursive equation. The added helper belongs to this node's canonical map,
has real data, and is listed in `lean.declarations` with its source docstring.
There is no duplicate declaration, new definition node, or change of mathematical interface.
The recorded declarations retain the constructions and the separate rank-zero identity.
The existing theorem has a `sorry` proof, as required for stage 2; this delivery does not
claim that it has been proved. Its signature verbatim is:

```lean
theorem discrete_lattice_cup_exterior (r : ℕ) : IsIso (cupMap A r)
```

I read the local module in full and independently obtained the current live module with
`scompile.py --source Sheaf.CategoryTheory.DiscreteLatticeCupExterior`; its construction
and statement agree. There is no repair note for this item in `coord/repair-notes`.
The node already has a reviewed binding to this same module. Only `lean` is changed in the node. The Lean file changes author attribution,
elaboration options, the named shifted-tensor helper and the implementation of the
identical ordered recursion. The theorem statements and every `sorry` proof stay intact.
No profiler or timing commands appear in the delivered module.

Clause-by-clause correspondence:

- Any commutative condensed ring: `A : CategoryTheory.CondensedBar.Ring.{u}`.
  The abbreviation in `Sheaf.CategoryTheory.CondensedEquivariantBarData` is exactly
  `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})`.
  Its `toMon` is the dependency's `Profinite.CondensedRing`, and `ringComm` supplies
  precisely commutativity. This admits every internal commutative ring, without a
  topological presentation, nonzero, characteristic, completeness or flatness binder.
- The small coherent profinite site and size convention are the explicit `u` on
  `Profinite`, `u + 1` on abelian coefficients and the ordinary derived morphisms.
  `Modules A` is transparently `Profinite.CondensedAction.Modules A.toMon`, hence
  Mathlib's category of internal module objects, not a replacement module category.
  The objects live in `DerivedCategory.{u + 1} (Modules A)`.
- Every rank, including zero: `(r : ℕ)`; the integer lattice with discrete topology is
  `Lattice.{u} r = ULift.{u} (Multiplicative (Fin r → ℤ))`. The multiplicative wrapper
  permits the existing group-action interface; it changes neither group nor topology.
- Trivial action on the regular ring: `cohomology A (Lattice r)` expands to
  `(derived A (Lattice r)).obj (coefficient A (Lattice r))`; `coefficient` is the single
  complex of the image of `Mod.regular A.X` under `Profinite.CondensedAction.trivial`.
- Coordinate maps: `coordinateCharacter A r i : Character A (Lattice r)` is specified
  uniquely by `coordinateCharacter_exists`. For every profinite S and continuous g
  whose ith coordinate is the constant integer n, it evaluates to
  `(n : sectionRing A S)`. This determines the requested map on all sections:
  the discrete integer coordinate has finitely many clopen fibres, restriction gives
  n times 1 on each fibre and the sheaf condition determines their gluing. In particular
  the condition is not merely a normalization on global points. The empty test object
  has its unique section. The definition chooses from a unique-existence theorem,
  which determines the map, rather than an unspecified existence assertion.
- Connecting class: `coordinateClass A r i = characterClass (coordinateCharacter A r i)`.
  I read `CondensedUnipotentClass.characterClass`, `classShifted`, `extension` and
  `extensionPositive`: this is the shifted actual short-exact-sequence boundary for
  the action `(x,y) ↦ (x+a(g)y,y)`, applied to the derived invariant unit. The positive
  splitting `(0,1)` has cocycle a; no sign or arbitrary cohomology-class representative
  is substituted.
- Exterior source: `exteriorSummand A I` is the single regular-module complex shifted
  by `-(I.card : ℤ)`. `exteriorComplex A r` is its finite biproduct over all
  `I : Finset (Fin r)`; `exteriorObject` is its localization by `DerivedCategory.Q`.
  Each summand has zero differential, hence the biproduct has zero differential,
  with one copy of R in degree q for each q-element subset, exactly as in the node.
- Unit and ordered cups: `orderedCup` on the empty list uses `cupUnit`, through
  `baseUnitIso` and the shift-zero comparison. Its `List.rec` successor uses the coordinate
  class tensor the recursive cup, followed by the dependency's `cup`.
  `subsetCup` uses `I.sort (· ≤ ·)`, so the indices occur in increasing order.
  `regularSplit` and `DerivedCategory.shiftTensorShiftIso` identify the tensor of
  single-term shifts without a permutation. This is the node's canonical ordered
  shift identification, retaining its cup normalization.
- Actual derived morphism: `cupMap` uses `Functor.biproductComparison Q`, then
  `biproduct.desc` of the localized shift comparisons followed by `subsetCup`.
  Thus its restriction on each summand is exactly the specified ordered cup, and
  its empty-subset restriction is the specified unit. No arbitrary comparison map
  or only per-degree cohomology is substituted.
- Conclusion: `IsIso (cupMap A r)` is invertibility of that actual morphism in the
  ordinary derived category.
- Rank zero: the same module's `rank_zero_identity` states existence of the unit-normalized
  isomorphism `e : cohomology A (Lattice 0) ≅ regular A`, with
  `cupUnit ≫ e.hom = (baseUnitIso A).hom` and
  `rankZeroInclusion A ≫ cupMap A 0 ≫ e.hom = 𝟙 (regular A)`.
  Both identifications are retained, rather than calling two distinct model objects
  definitionally identical.
- Zero ring and arbitrary characteristic: no nontriviality or characteristic instance
  is imposed. All section rings, regular modules and complexes become zero for the
  zero ring; the unique map is the zero object's identity. No integer is inverted.

Dependency declarations read and used by the existing construction:

- `sk-def-sfb-module-objects`: `CategoryTheory.Mod` and `Mod.regular`,
  `Mathlib.CategoryTheory.Monoidal.Mod` (structure at 227, regular at 336).
- `def-sfb-condensed-action-module`: `Profinite.CondensedAction.ActionModule`,
  `Modules`, `trivial`, `FixedAll`, `Invariants` in
  `Sheaf.CategoryTheory.CondensedActionModule`. The bundled-ring notation is a
  transparent specialization of these same declarations.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, `Q`
  in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, signatures and docstrings at
  70–98; localization is at quasi-isomorphisms of integer cochain complexes.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing`, the general monoid-object abbreviation.
  The extra commutativity required here is bundled by `CondensedBar.Ring`.
- `def-weil-size-convention`: a metatheoretic convention, with no declaration;
  explicit universe levels above implement it.
- `lem-sfb-condensed-derived-restriction-calculus`:
  `CategoryTheory.CondensedDerivedRestriction.cupLaws` and the public definitions
  `cohomology`, `cup`, `cupUnit`, `characterClass` reexported by
  `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`. I read the recorded
  primary theorem `coefficientSquare` and its full signature/docstring, and the
  defining cup and character interfaces in `CondensedDerivedCup` and
  `CondensedUnipotentClass`. The cup is the right-adjoint lax pairing followed by
  regular multiplication; it uses the ordinary derived module tensor.

The existing module imports the stated Koszul proof dependency and the upstream
`DerivedCategory.triangleOfSESδ_eq_degreewiseSplit` module. The additional
`lem-sfb-lattice-koszul-triangulated-cup-comparison` is currently unstated (no lean
record); the existing theorem docstring names it as the remaining multiplicative
proof input. It is not needed to type this statement, and no copy is introduced.
I read the source blueprint direct-images proof paragraph (3), which gives the
ordinary open/proper-image route but not this lattice calculation. The node correctly
labels the detailed proof as an agent expansion and requests an exact internal-module
reference. The existing docstring retains all five node proof steps.

Edge cases checked: rank zero has only the empty subset and its unit normalization
is separately asserted; rank one has exactly the empty and singleton summands;
negative degrees and degrees above r have zero terms; the zero ring and positive
characteristic require no division; empty test profinite sets are covered by the
character specification and the sheaf condition. No statement correction or
STATEMENT-DISPUTED finding is needed.

Searches actually run:

- `msearch.py ... leanfinder`: “Coordinate cup products compute derived invariants of
  the trivial action of a discrete integer lattice on condensed ring modules”.
  Eight hits, including `CondensedMod.LocallyConstant.functorIsoDiscreteAux₂` and
  ordinary `continuousCohomology`; none is this internal derived cup isomorphism.
- `msearch.py ... loogle`: `"groupCohomology", "cup"`: zero hits.
- `msearch.py ... grep`: `(exterior|cup|koszul).*(cohomology|invariant)|(cohomology|invariant).*(exterior|cup|koszul)`
  in Mathlib/RepresentationTheory: zero hits.
- `rg` for `discrete_lattice_cup_exterior|DiscreteLatticeCup|coordinateCharacter|cupMap`
  in both `lean/WeilConjectures` and `lean/Sheaf`: the exact existing module above
  was found in `lean/Sheaf`; no upstream replacement was found.
- `grep -rn` for the node id in `lean/WeilConjectures`: no hits.
- `rg` for the exact declaration/namespace in `dag/lean_names_upstream.json`: no hits.
- Read the live module using the authorized `scompile.py --source` interface.

Validation uses `scompile.py` for the repaired owning module, then the prescribed
`deliver2.py --no-push` server preflight and compilation before delivery. The initial
existing-declaration probe is recorded above as a failed attempt, not a passing check.

The final delivered module passed `scompile.py` without errors or warnings:
sandbox mode 51.4 seconds, library-module mode 50.6 seconds, both within the
unchanged 60-second per-file limit. Every theorem remains `sorry`; definitions
contain actual constructions. The scratch profiler and timing files are outside
`lean/` and are not included in the delivery.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
