## What changed

Proved `AlgebraicGeometry.IsCurve.filteredFiniteCoverLowerShriekTransfer_retract` with its
signature unchanged. The proof applies extension by zero and the forgetful sheaf functor to
the supplied retraction, then descends all eight fields of `Assertions`. Four proved private
helpers give the cohomology retraction, injectivity of its section, and descent of surjectivity
and bijectivity of every cohomology comparison map. Naturality uses the existing, proved
`Etale.cohomologyMap_map`; composition uses the existing `Sheaf.H.map_comp_apply`.

Added one proof-only import and one module,
`Sheaf.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility`, for the
geometric coefficient step. Its theorem supplies constructibility of the larger sheaf and
transfer of invertible-order and primary torsion. It has no cohomology hypothesis or
conclusion and assumes no retraction. Updated the item's DAG proof and dependencies to match
these actual calculations. The curve-calculation and trace-splitting unit route is retained.

Both delivered modules compile locally without warnings through `lcompile.py --all`.
The new statement was checked on zero G, empty U, empty V, unequal primes p and r, and
characteristic r: zero cases yield zero coefficient sheaves, and unequal primes force the
original primary sheaf to vanish. No statement or definition was changed.

## Proved and sorry left

Proved the item's one original sorry:
`AlgebraicGeometry.IsCurve.filteredFiniteCoverLowerShriekTransfer_retract`
(node `k1-filtered-finite-cover-lower-shriek-transfer-retract`). There is no sorry left in
that module; all four private helper theorems are proved.

One new sorry remains:
`AlgebraicGeometry.IsCurve.finiteCoverLowerShriek_coefficient_compatibility`
(node `v1-finite-cover-lower-shriek-coefficient-compatibility`). This is exactly the
coefficient step; its complete proof in words is in its declaration docstring and node.
The assembled retract proof still depends on this theorem's sorry, so this is a reduction,
not a claim that the target's axiom closure is sorry-free.

## No longer needed

No original imports were removed: both public imports are needed by the unchanged signature.
The new import is proof-only.

The item's former dependency `lem-weil-pbc-curve-assertions-retract`, module
`Sheaf.AlgebraicGeometry.Curve.RetractAssertions`, is not needed on this edge: its general
integer-coefficient theorem is replaced by explicit, proved cohomology calculations for the
actual coefficient ring. No import of that module was added.

The former dependency `lem-weil-pbc-finite-pushforward-constructible-noetherian`, module
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian`, is not needed on this
edge: the new coefficient proof uses the stronger finite-etale hypothesis and local
trivialization with finite sums to obtain finite local constancy, then extension by zero.
It does not require general finite-pushforward constructibility. No import was added.
These are removals from this proof route, not claims that these modules are globally
unreachable. The two other former direct dependencies, `def-weil-pbc-primary-torsion` and
`def-weil-pbc-constructible-torsion`, no longer appear as direct edges of this node.
Their definitions remain used through `Assertions` and the coefficient lemma; this is
edge relocation, not pruning of either definition module.

## Where the brief, the DAG or earlier work was wrong

The item's file did not import the planned proof dependencies. Reading them also showed
interface mismatches: the generic retract theorem accepts abelian sheaves converted to
`ULift ℤ` modules, whereas the item uses `ULift (ZMod r)`; the Noetherian finite-pushforward
theorem concludes constructibility of the underlying set sheaf of an abelian sheaf, whereas
the assertion fields require `Scheme.IsConstructibleSheaf` of the actual module sheaf.
The new coefficient theorem isolates this missing geometric step. The remaining descent
is proved directly from already proved functoriality and naturality lemmas.

The informal statement of `lem-fet-locally-trivial` asks for a single finite set S for all
of a possibly disconnected base; varying degrees make that global wording too strong.
The attached, proved Lean declaration `Scheme.FiniteEtale.exists_etale_isPullback_sigma`
is correctly local at each point and allows its finite set to vary by neighborhood.
The new coefficient proof uses that local declaration, explicitly allowing varying rank.
The discrepancy is reported here; no declaration or other node was changed.

The Stacks source was read at Tag 03SD (`lemma-vanishing-easier`), first paragraph, and
at `lemma-pushforward-constructible` / Tag 095R (`lemma-finite-pushforward-constructible`).
The local source copy `/home/ubuntu/c1-stacks-review/etale-cohomology.tex` was available;
the project's advertised `literature/stacks-project/etale-cohomology.tex` was absent here.

## New nodes

`v1-finite-cover-lower-shriek-coefficient-compatibility`:
`dag/nodes/sec-proper-base-change/v1-finite-cover-lower-shriek-coefficient-compatibility.json`,
stated in `lean/Sheaf/AlgebraicGeometry/Curve/FiniteCoverLowerShriekCoefficientCompatibility.lean`.
It collects the strictly geometric part of the original docstring: constructibility and the
two conditional torsion transfers, with no cohomology assertions. Its proof uses local
finite-etale splitting and finite sums, then stalk annihilation by r and Bezout, including
the zero-sheaf case. No change records are required because existing signatures,
definitions, and public imports remain unchanged.

## Second reading by V1

1. PASS: compared the delivered item with the repository using `diff -u`; its original
   theorem signature and docstring are byte for byte unchanged. The only existing-module
   additions are four private proved helpers, one ordinary proof-only import, and the proof.
   No definition, target, or public import changed; no change record is required.
2. PASS: compiled both modules in import order with `lcompile.py --all`, without errors or
   warnings. Inspected every proof and all eight assertion fields. The item has no sorry;
   the sole delivered sorry is the public coefficient theorem listed above. No prohibited
   declaration or hollow definition occurs. The axiom probe for both public theorems gives
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is expected
   for this reduction, so the target's full axiom closure remains open.
3. PASS: checked the new coefficient statement against the actual constructibility,
   primary-torsion, and invertible-order definitions and the Stacks local source. For zero G,
   empty U, or empty V the resulting zero sheaves satisfy the conclusions. When p differs
   from r, coprime annihilators force F and hence G to be zero. In characteristic r,
   invertible-order torsion likewise forces F zero; otherwise a nonzero stalk forces r to
   be invertible. Disconnected bases cause no problem because finite-sheet trivializations
   are local. Independent LeanFinder, Loogle, Mathlib grep, and library/upstream searches
   found no theorem proving the entire coefficient conjunction. Found the already stated
   finite-etale module pushforward theorem: it handles one part, remains sorry itself,
   and is now used in the new node's plan. The coefficient lemma is strictly a geometric
   part of the argument, with no retraction or cohomology assumption or conclusion.
4. PASS after report correction: the four cohomology helpers give a direct functoriality
   and naturality proof rather than another open retract theorem. Both public imports are
   needed for signatures and the added import is proof-only. All four former direct DAG
   dependencies are now accounted for under No longer needed, distinguishing the two
   pruned theorem edges from relocated definition edges. `sk-thm-p1.realized` was read;
   curve calculations, filtration, and trace splitting remain on the unit route.
5. PASS after plan correction: the item's proof steps and dependency union match the Lean
   retraction calculation. The new node has its source, full natural-language proof,
   search records, creation/blueprint/chapter/unit fields, and verbatim Lean signature.
   Its finite-local-constancy step now refers to the existing specialized pushforward node
   instead of planning to reconstruct that theorem from local splitting and biproducts.

Changed only the new coefficient theorem's proof explanation, its DAG proof plan and
search note, and this report's complete pruning accounting. No Lean proof or signature
needed repair. The remaining geometric conjunction is not a few-minute proof with the
available interfaces, so its documented sorry remains.
