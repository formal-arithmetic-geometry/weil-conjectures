## What changed

Proved `AlgebraicGeometry.constant_root_trivialization_baseChange` in
`Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange`, with its signature unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.Curve.PowerMapPullback`.
Its theorem `AlgebraicGeometry.Scheme.constantZModToGmSheaf_pullback` is fully proved
for arbitrary scheme morphisms and compatible global units. It uses the two adjunctions,
uniqueness of left adjoints, sheafification, and an explicit calculation on ZMod representatives.
The main proof verifies compatibility of the two field-induced global units, uses the
supplied first short-complex square, and cancels the kernel inclusion.
Updated the item's proof route and added the node for the general power-map lemma.
Both modules compile locally without warnings. No declaration or definition was changed.

## Proved and sorry left

- `AlgebraicGeometry.constant_root_trivialization_baseChange`
  (`lem-sc-root-trivialization-base-change`): proved; the original one sorry is removed.
- `AlgebraicGeometry.Scheme.constantZModToGmSheaf_pullback`
  (`lem-sc-power-map-pullback`): proved; no sorry introduced.

No sorry remains in either delivered module. The argument works for n = 1 and empty
schemes, and uses neither connectedness nor smoothness nor algebraic closedness.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility`,
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The latter two are already publicly
available through RootsOfUnity and ConstructibleSheaf.Defs respectively. Both original
public imports remain required by the unchanged signature.
The proof does not need the theorem `lem-sc-kummer-base-change-compatibility` or its module
`Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility`: the morphism and its
middle component are already hypotheses. Removed this node from the item's proof dependencies;
its statement dependency is preserved. Sheafification is used through the fully proved
power-map lemma, so `def-weil-pbc-sheafification` is no longer a direct proof dependency
of the item, but remains a dependency of the new node. Kummer, RootsOfUnity, and inverse-image
notions remain used. No unit statement or step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan cited Kummer base-change compatibility to use data already supplied as hypotheses.
Its sheafification step was correct, and is now a complete general theorem in Lean.
The blueprint source markdown is absent from this clone; the unit record and the existing
node and docstring carry its proper-case compatibility argument, which the proof realizes.
LeanSearch returned Internal Server Error (recorded as unavailable); LeanFinder, Loogle,
and Mathlib grep ran successfully. No matching power-map theorem was found.

## New nodes

`lem-sc-power-map-pullback`, at
`dag/nodes/sec-curve-estimates/lem-sc-power-map-pullback.json`, records the fully proved
arbitrary-scheme global-unit precursor. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/PowerMapPullback.lean`. It has no remaining proof obligation.
There are no change records: the added module exposes only a new theorem, while the original
module's signature and public imports are unchanged.


## Second reading by P1

1. Compared the complete existing module with the repository version using diff, and
   checked the theorem signature byte for byte: unchanged. No existing definition,
   declaration docstring, public import, or target statement changed. The only new
   declaration is the global-unit precursor in PowerMapPullback; no change record is needed.
   No open change record names these modules or the original theorem. Verdict: pass.
2. Compiled both modules locally in import order, without errors or warnings. Inspected
   every proof and searched for forbidden constructs: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition. A scratch copy with #print axioms for
   both delivered theorems reports exactly propext, Classical.choice, and Quot.sound.
   The main proof checks the field-induced units using the pullback square, uses the
   supplied short-complex square, and cancels a genuine kernel monomorphism. Verdict: pass.
3. No unproved statement is split off. The new, fully proved precursor is precisely the
   power-map square needed after composing with the roots-of-unity inclusion, not a
   renamed copy of the item. Read its adjunction and terminal-section calculation against
   the upstream definitions. For n = 1 its cyclic group is trivial; for an empty scheme
   the global unit calculation and adjunction still apply. No primitivity is needed for
   this precursor; n = 0 is excluded explicitly by NeZero. Repeated LeanFinder with
   "inverse image naturality morphism constant cyclic group sheaf to units induced by
   torsion section", Loogle for homEquiv_leftAdjointUniq_hom_app, Mathlib grep with
   "zmodToGm|GmSheaf.*constant|constant.*GmSheaf", and rg over both library roots.
   The search hits supply generic adjunction facts already used, not this square.
   Verdict: pass.
4. Read top down. The proof takes the direct kernel reduction and uses proved upstream
   definitions and Mathlib adjunction identities. Both public imports in the new module
   provide objects appearing in its signature; its sole importer uses a plain proof-only
   import. Corrected No longer needed to enumerate all three removed proof-only imports.
   The two old proof dependencies removed are Kummer base-change compatibility (already
   supplied as hypotheses) and direct sheafification (now used through the new node).
   The proper-case compatible-root step of sk-prop-ext-invariance is preserved, with no
   alternate unit route. Its existing realized.statement and realized.steps arrays are
   empty in the repository: this pre-existing unit-index gap is reported here; no unit
   record is part of this proof delivery or changed by it. Verdict: proof route passes;
   unit-index metadata needs maintainer attention.
5. Read both node records alongside the Lean proofs: proof steps and their union
   proof_deps agree, proof_origin identifies the argument, and the new node has source,
   self-contained statement, searches, blueprint provenance, chapter/unit, creation and
   verbatim Lean signature. The original node changes only stage-3-owned fields.
   Verdict: pass.

Second reading changed only this report: repaired the inaccurate import-pruning claim,
recorded independent checks, and flagged the pre-existing empty unit realization index.
The Lean proofs and node records needed no repair.
