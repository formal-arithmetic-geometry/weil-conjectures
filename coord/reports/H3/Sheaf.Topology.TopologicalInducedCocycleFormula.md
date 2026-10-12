## What changed

Corrected `CategoryTheory.topological_induced_cocycle_formula` to construct a compatible
`edge` for the supplied generator map `a`, rather than assert its formula for any edge.
The old Lean theorem was false. The repaired theorem has a complete Lean proof from two
strict parts of the original resolution argument: existence of objectwise additive maps,
and naturality in the coefficient sheaf. The proof uses function extensionality to
eliminate the functor equalities, assembles a `NatTrans` using the naturality square,
and applies the objectwise cocycle computation. No `sorry` occurs in this assembly.

Added proof imports `Sheaf.Topology.TopologicalCocycleObjectwise` and
`Sheaf.Topology.TopologicalCocycleNaturality`, with one public theorem and node each.
No definitions were introduced and no data were chosen in a public definition.
The generator equation uniquely determines `a`; the objectwise cocycle condition
uniquely determines each additive map, using cocycle representatives and the
terminal-section bijection. The proof chooses witnesses only to prove an existential.

Adapted only the necessary three proof lines of
`Sheaf.Topology.TopologicalInducedCohomologyCocycle`. Its signature and visibility
are unchanged. Updated both existing nodes' proof records and the corrected item's
Lean signature and statement-change record. The unit's statement and route remain
unchanged: neither helper realizes a blueprint unit statement or step.

The four delivered modules compile in import order without warnings except the expected
warnings that the two explicitly deferred public theorems use `sorry`.

## Proved and sorry left

The corrected `CategoryTheory.topological_induced_cocycle_formula` contains no direct
`sorry`, and is reduced to the following two named, strictly smaller statements:

- `CategoryTheory.exists_topological_cocycle_objectwise`, node
  `lem-sc-topological-cocycle-objectwise`: `sorry`; existence and comparison-independent
  cocycle calculation for one degree and one coefficient sheaf, without naturality.
- `CategoryTheory.topological_cocycle_naturality`, node
  `lem-sc-topological-cocycle-naturality`: `sorry`; naturality of supplied objectwise
  comparison maps satisfying the cocycle formula, without constructing any maps.

This is a decomposition, not a sorry-free proof of the mathematics: one corrected upper
hole is closed and two lower holes are added. The old false universal-edge statement
is not claimed to have been proved unchanged. The adapted
`CategoryTheory.exists_topological_induced_cohomology_cocycle` remains proved with the
same signature, and adds no hole. No other delivered theorem has a direct `sorry`.

## No longer needed

No existing imports were removed. No module is claimed globally pruned.
The item's former direct proof dependencies
`def-sc-topological-abelian-cohomology`,
`def-weil-pbc-topological-inverse-image`, and
`lem-sc-topological-pushforward-injective` now belong to the two lower comparison
statements, so are still needed there. The caller still uses
`Sheaf.Topology.TopologicalInducedEdgeAndMap` to obtain `a` and its generator equation;
its unconstrained edge witness is discarded.

## Where the brief, the DAG or earlier work was wrong

The previous worker correctly identified the false arbitrary-edge Lean statement but
stopped before repairing it. The DAG/source construct an edge; they do not say that
all natural transformations have its cocycle formula. The repair corrects this
intermediate statement and adapts its only caller. The parent existential theorem,
including all of its binders and conclusions, remains identical.

Stacks Tag 01F2 is the Leray spectral sequence, rather than the injective-resolution
comparison lemma. The new proof docstrings and nodes cite Section 20.2, Tag 01DZ,
and Derived Categories Section 13.18, Lemmas 13.18.6 and 13.18.7, whose construction
and homotopy uniqueness were read. The terminal-section composition appears in
Tag 01EZ. The original node's source field is preserved under the field rules.

LeanSearch returned Internal Server Error; this is recorded as unavailable, not as an
absence result. LeanFinder and local source searches found the general Ext and
injective-resolution APIs but no single declaration with the topological comparison
or the needed naturality specialization. The free/sheafification/Yoneda identification
and comparison into the termwise injective, generally non-exact complex `f_*I`
remain explicitly described in the lower nodes rather than asserted silently.

## New nodes

`lem-sc-topological-cocycle-objectwise`, in
`lean/Sheaf/Topology/TopologicalCocycleObjectwise.lean`, states only the objectwise
additive comparison and its resolution-cocycle computation. Its proof describes
comparison existence, the terminal-section bijection, preservation of cycles and
boundaries, and homotopy independence. Edge cases: zero coefficients/cycles give
zero, degree zero is the ordinary section map, and identity-on-a-point gives identity.

`lem-sc-topological-cocycle-naturality`, in
`lean/Sheaf/Topology/TopologicalCocycleNaturality.lean`, states only the coefficient-map
square for supplied objectwise maps. Its proof lifts coefficient maps, uses homotopy
uniqueness for the comparison square, and uses Ext cocycle surjectivity. Zero maps and
degree zero are included. Both new modules have exactly one public theorem with
`:= by sorry`, its source, proof in words, and blueprint id.

Interface change record: `coord/changes/topological-induced-cocycle-formula.md`.

## Forced adaptations

`Sheaf.Topology.TopologicalInducedCohomologyCocycle` is unclaimed in the local claim table.
The original compiles against the original dependency and fails against the corrected
one at line 106: `Application type mismatch`, because `edge` is passed where `a` is
now expected. Against the corrected dependency, the changed proof compiles.

Only original lines 103-106 change: discard the unconstrained edge when obtaining `a`,
obtain a compatible edge and formula from the repaired theorem, and package the same
existential conclusion. This is necessary to use the corrected interface. Every existing
signature and visibility, all imports, and every other proof line stay identical.
The change record includes the argument types from the compiler error.

## Second reading by H3

1. **Visible declarations and accidental changes.** Compared all four delivered Lean modules with
   the repository versions. The caller's theorem signature is byte-for-byte unchanged. The item
   theorem intentionally has the recorded statement change: its arbitrary `edge` argument is
   replaced by an existentially constructed compatible edge. The two helper modules are new, and
   the only other edit is the forced proof adaptation in the caller. Verdict: pass.

2. **Compilation and trust.** Compiled all four modules with `lcompile.py --all`; each compiled
   successfully. The only remaining `sorry`s are the two named helper theorems listed above; no
   definition contains `sorry`, and no forbidden declaration or construct occurs. The item proof
   and adapted caller have no `sorry`. Verdict: pass, with the two explicitly recorded lower
   obligations remaining.

3. **Statements, searches, and nodes.** Read both new statements and their docstrings, checked
   their edge-case notes, and checked their JSON nodes, declarations, sources, proof steps,
   dependencies, search records, and `status: split`. The helpers are strict objectwise and
   naturality parts rather than restatements of the repaired item. Existing declarations and
   Mathlib searches were checked, including `freeYonedaHomEquiv`, global-section equivalences,
   Ext cocycle APIs, and local source searches. Verdict: pass.

4. **Shortest route and pruning.** The repaired proof substitutes the specified functor
   equalities, obtains the objectwise maps, proves their coefficient naturality, and assembles
   natural transformations; it uses no redundant public proof imports. The old dependencies remain
   required by the two lower nodes, and no unit statement or step is bypassed. Verdict: pass;
   no additional pruning found.

5. **DAG and unit agreement.** The item's node records the corrected statement, statement-change
   record, exact proof steps and proof dependencies. The two new nodes carry their Lean records and
   complete proof-origin/source metadata. The caller node records the forced adaptation. The unit's
   `realized` statement and route are unchanged. Verdict: pass.

I changed only this report section. No Lean proof, declaration, node, import, or change record was
altered during second reading.

## Forced adaptations

### Sheaf.Topology.TopologicalInducedCohomologyCocycle
Original against changed dependencies failed:
```
/tmp/forced-adaptation-17ono_vk/lean/Sheaf/Topology/TopologicalInducedCohomologyCocycle.lean:106:54: error: Application type mismatch: The argument
  edge
has type
  (p : ℕ) → TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p
of sort `Type (u + 1)` but is expected to have type
  (presheafToSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj (yoneda.obj ⊤ ⋙ AddCommGrpCat.free) ⟶
    (TopCat.Sheaf.pushforwardAb f).obj
      ((presheafToSheaf (Opens.grothendieckTopology ↑Z) AddCommGrpCat).obj (yoneda.obj ⊤ ⋙ AddCommGrpCat.free))
of sort `Type u` in the application
  topological_induced_cocycle_formula f HX HZ hX hZ edge

(with the modules compiled into /tmp/forced-adaptation-17ono_vk/.lbuild) [6.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
