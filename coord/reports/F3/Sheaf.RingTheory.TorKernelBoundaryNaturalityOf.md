## What changed

Repaired reviewer X-75668's E2 / point 4 and G1. Replaced the false arbitrary-family
signature of `CategoryTheory.tor_kernel_boundary_naturality_of` with naturality
of the explicitly constructed `CategoryTheory.torKernelBoundary`. The new module
`Sheaf.RingTheory.TorKernelBoundaryConstruction` constructs the map by lifting a
projective-resolution augmentation through q, factoring the differential into
ker(q), tensoring, restricting to cycles, and descending to H₁. Every definition
and supporting theorem in that module is complete. No unproved existence theorem
is used to choose data.

The item's naturality proof is complete: a difference of augmentation lifts
factors through the target kernel and contributes a differential, which vanishes
on tensor cycles. Cancel the cycle-to-homology epimorphism and transport through
the resolution identification of Tor. It assumes no exactness of arbitrary maps.

Adapted only the proof imports and body of
`Sheaf.RingTheory.TorKernelBoundaryNaturality`: its existential witness is now
`torKernelBoundary M`; combine its exactness and naturality. Preserved the full
signature and visibility of `exists_tor_kernel_boundary_natural` and all target
statements. Updated both affected existing nodes and added construction and
fixed-map exactness nodes. Change record:
`coord/changes/tor-kernel-boundary-canonical.md`, with verbatim old/new signatures
and the complete direct user list.

## Proved and sorry left

The old false theorem is corrected, not proved as originally stated. Its
replacement `CategoryTheory.tor_kernel_boundary_naturality_of` is fully proved
(no sorry), as are all construction helpers:
`torKernelLift_comp`, `torKernelDifferential_boundary`, and
`torKernelTensor_boundary`. The construction contains no proof holes.

One new, strictly smaller obligation remains:
`CategoryTheory.tor_kernel_boundary_construction_exact`, node
`lem-sc-p1-tor-kernel-boundary-construction-exact`, module
`Sheaf.RingTheory.TorKernelBoundaryConstructionExact`. Its proof is exactly
`by sorry`. Its docstring explains the horseshoe construction and comparison
identifying its connecting map with our explicit boundary. It asserts only the
two exact pairs for the fixed constructed map, with no existential choice and
no naturality assertion. Thus this is one false auxiliary hole retired and one
true exactness hole added, not a proof of the old false assertion and not a
positive net hole reduction.

`CategoryTheory.exists_tor_kernel_boundary_natural` has a complete combining
proof from this exactness obligation and the proved naturality theorem; it
transitively depends on the one new exactness hole. No other sorry is delivered.

All four delivered modules compile together through lcompile. Explicit
`#print axioms` checks for `torKernelBoundary`, `torKernelHomologyBoundary`,
and `tor_kernel_boundary_naturality_of` report only `propext`,
`Classical.choice`, and `Quot.sound`. The proof route
uses Mathlib projective resolutions and cokernel descent directly. The construction
and naturality are independent of the remaining exactness obligation.

## No longer needed

Removed unused import Mathlib.Algebra.Homology.HomologicalComplexAbelian from TorKernelBoundaryConstruction; the construction compiles without it.

Removed proof-only imports `Sheaf.Paper.TorLongExactFirstVariable` and
`Sheaf.RingTheory.TorKernelBoundaryExact` from the adapted caller. Their arbitrary
existential boundary family is not used. Pruned the caller's former proof plan
through `lem-weil-pbc-tor-long-exact-first-variable` and its imports, and the
invalid inference from `exists_tor_kernel_boundary_exact` to naturality.

Naturality no longer needs horseshoe resolutions, homology-long-exact naturality,
or exactness assumptions: the degree-zero lift comparison suffices. The old
item's dependency on its caller, `lem-sc-p1-tor-kernel-boundary-natural`, is
removed. The caller now depends downward on the constructed map, exactness,
and naturality with no cycle. The exactness node still genuinely needs
`lem-weil-pbc-free-resolution-ses-split`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-tor-map-via-resolution-lift`, and
`lem-weil-pbc-tensor-right-exact`; these are not pruned from that argument.

No claim that these modules disappear from the whole targets' import closure:
other users may retain them. No realized unit step is bypassed;
`dag/units/sk-thm-picard-duality.json` has empty realized arrays.

Direct pruning inventory against the repository baseline: the item removes
`Sheaf.Paper.TorLongExactFirstVariable`; its old direct node dependency
`lem-sc-p1-tor-kernel-boundary-natural` is removed. The caller removes the two
proof imports listed above and all six old direct proof dependencies:
`lem-weil-pbc-free-resolution-ses-split`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-tor-map-via-resolution-lift`,
`lem-weil-pbc-tensor-right-exact`,
`lem-weil-pbc-tor-long-exact-first-variable`, and
`lem-weil-pbc-complex-ses-long-exact-naturality`.
The first four remain in the new exactness plan, and resolution comparison
remains in the proved naturality plan. This inventories direct pruning only.

## Where the brief, the DAG or earlier work was wrong

The earlier arbitrary-family statement is false: exactness does not fix the
sign or normalization of a connecting morphism. The Z/3 counterexample in the
return applies. A comment-only dispute did not repair it; this delivery replaces
the assertion and the invalid caller application with an actual construction
and its proved naturality.

The canonical boundary's exactness cannot be imported from the existential
`exists_tor_kernel_boundary_exact`: its chosen maps are not identified with this
construction. The new exactness obligation includes that comparison in its
proof in words. It is strictly smaller than the unchanged caller theorem, since
naturality is entirely proved independently, and no new existence theorem is
being used as a renamed caller.

Sources read: [Stacks 00M0](https://stacks.math.columbia.edu/tag/00M0),
[00LZ](https://stacks.math.columbia.edu/tag/00LZ), and
[0111](https://stacks.math.columbia.edu/tag/0111). LeanSearch was unavailable;
LeanFinder and local Mathlib searches supplied the resolution-comparison and
cokernel APIs. Edge cases checked mathematically: zero M makes every tensor and
Tor term zero; injective surjections have zero kernel and zero boundary; no
projectivity of F is assumed. The construction uses projectivity of P₀ only.

Whole-blueprint duplicate search: searched every `dag/nodes/**/*.json` blueprint for the requested place text and for the old `lem-sc-p1-tor-kernel-boundary-naturality-of` repair reference (`rg -n 'constructed canonical boundary and its exactness|tor-kernel-boundary-naturality-of' dag`); no duplicate blueprint block was found.

## New nodes

`def-sc-p1-tor-kernel-boundary-construction` records the real data construction
in `Sheaf.RingTheory.TorKernelBoundaryConstruction`; its main declaration is
`CategoryTheory.torKernelBoundary`. All its data and proofs are complete.

`lem-sc-p1-tor-kernel-boundary-construction-exact` records the remaining exactness
comparison, one theorem in its own module. Its full mathematical proof is in
both the node and theorem docstring. Change record:
`coord/changes/tor-kernel-boundary-canonical.md`.

## Forced adaptations

`Sheaf.RingTheory.TorKernelBoundaryNaturality` is unclaimed. Its original proof
passes δ and hδ to `tor_kernel_boundary_naturality_of`; after the required
signature correction that application fails because the theorem now expects
presentation modules. The only edits are removing two obsolete proof imports,
adding `Sheaf.RingTheory.TorKernelBoundaryConstructionExact`, and replacing the
last three proof lines with the explicit family and its two properties. Every
existing signature and visibility is identical. Counterfactual compilation of the original caller against the delivered overlay
failed at the original line 77, column 46:

```text
error: Application type mismatch: The argument
  δ
has type
  (F N : ModuleCat R) →
    (q : ↑F →ₗ[R] ↑N) → Function.Surjective ⇑q →
      ↑(((Tor' (ModuleCat R) 1).obj N).obj M) →ₗ[R] ↥q.ker ⊗[R] ↑M
but is expected to have type
  ModuleCat R
in the application
  tor_kernel_boundary_naturality_of R M δ
```

Original changed lines: imports 12–13 and proof 75–77. Adapted lines: imports
12–13 and proof 74–76. Import 14 (the item's module) stays, shifted up by one
line. No docstrings, signatures, attributes, or other proof lines are changed.
The adapted module compiles with the same overlay. deliver3.py independently
repeated the baseline/changed-dependency counterfactual and passed.


## Earlier second reading (a previous round; superseded)

1. Interface audit: PASS with the declared correction. Diffed both existing
modules against the repository. Only `tor_kernel_boundary_naturality_of` changes
signature, exactly as declared in the change record. The original universal
arbitrary-family assertion is false (independent sign choices over Z/3).
The caller's full signature, visibility, attributes and docstring are unchanged;
its changed imports and final three proof lines are forced by that correction.
The existing targets and their definitions are untouched. A full-library search
finds the caller as the sole external textual user of the changed declaration.
No DAG node cites the item in stmt_deps or proof_deps in the repository baseline,
so the statement_change citers array is correctly empty.

2. Proof audit: PASS. Independently compiled all four modules in import order.
Read the lift, kernel restriction, tensor-boundary vanishing, cokernel descent,
lift-difference cycle comparison, homology cancellation, and derived-functor
transport. No data come from an unproved existence theorem. The only delivered
sorry is the reported named exactness theorem, whose body is exactly `by sorry`.
Scanned all delivered sources for forbidden declarations and attributes.
Explicit scratch `#print axioms` checks of all eight public construction
helpers/definitions and the naturality theorem show only propext,
Classical.choice and Quot.sound. The exactness theorem and existential caller
show these plus sorryAx, precisely from the one documented remaining hole.
The scratch audit is kept outside the delivered lean/ tree.

3. Split statement audit: PASS. The fixed-map exactness theorem is a true,
strictly smaller part of the caller: it proves no naturality and quantifies no
chosen family. Its sourced docstring includes the essential comparison of the
horseshoe boundary with the constructed map, including independence of the
augmentation lift. Checked zero M, zero N, identity surjections, split
surjections, and nonprojective F mathematically. For split surjections the
boundary vanishes and Tor(q,M) is surjective, as both exact pairs require.
Read the actual free-resolution SES declaration and Mathlib's comparison and
homology APIs. Fresh LeanFinder search for exact sequences of derived tensor
functors and Loogle search for Functor.leftDerived found tensor right exactness
and resolution APIs, but no existing theorem of this fixed boundary's exactness.
Local library and Mathlib searches likewise found no duplicate. This remaining
horseshoe comparison is not a few-minute proof and is retained honestly.
Verified the source statements at [00M0](https://stacks.math.columbia.edu/tag/00M0),
[00LZ](https://stacks.math.columbia.edu/tag/00LZ), and
[0111](https://stacks.math.columbia.edu/tag/0111).

4. Route and pruning audit: PASS. The naturality proof takes the direct
augmentation-lift difference route and uses Mathlib's proved comparison theorem;
no new naturality hole is introduced. Public construction imports supply data,
instances or APIs needed by public definitions; the constructed boundary import
is needed by the corrected naturality signature. Caller imports are proof-only
where appropriate. All six old caller proof dependencies are removed as direct
steps: free-resolution-ses-split, complex-ses-homology-long-exact,
tor-map-via-resolution-lift, tensor-right-exact,
tor-long-exact-first-variable, and complex-ses-long-exact-naturality
(with their full lem-weil-pbc- prefixes). The first four are retained below the
new exactness obligation; tor-map-via-resolution-lift is also used directly by
the proved naturality theorem. The former item dependency on
lem-sc-p1-tor-kernel-boundary-natural is removed. No whole-closure pruning is
claimed. Read dag/units/sk-thm-picard-duality.json: its realized statement and
step arrays are empty, so this auxiliary reduction bypasses no realized step.
This is a correction/decomposition with zero net hole reduction, not a proof
of the old false assertion.

5. Record audit: PASS after repairs. Both existing proof plans match their Lean
proofs; the two new nodes have source, creation, blueprint, chapter/unit, search,
Lean and dependency records. Replaced compressed lean.statement strings with
verbatim signatures from the declaration keyword in the delivered files
(the metadata checker starts at def, after noncomputable). Added lem-weil-pbc-tor-map-via-resolution-lift to the
naturality node's proof step and proof_deps, because its Mathlib declaration is
actually used. The fixed-map exactness node records the full comparison route.

Second reading changed only the node metadata and this report: verbatim
signatures, the missing resolution-comparison dependency, and a complete direct
pruning inventory. No Lean proof or statement was changed during this reading.

## Forced adaptations

### Sheaf.RingTheory.TorKernelBoundaryNaturality
Original against changed dependencies failed:
```
/tmp/forced-adaptation-oo6u2h_l/lean/Sheaf/RingTheory/TorKernelBoundaryNaturality.lean:77:46: error: Application type mismatch: The argument
  δ
has type
  (F N : ModuleCat R) →
    (q : ↑F →ₗ[R] ↑N) → Function.Surjective ⇑q → ↑(((Tor' (ModuleCat R) 1).obj N).obj M) →ₗ[R] ↥q.ker ⊗[R] ↑M
but is expected to have type
  ModuleCat R
in the application
  tor_kernel_boundary_naturality_of R M δ

(with the modules compiled into /tmp/forced-adaptation-oo6u2h_l/.lbuild) [1.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier second reading (a previous round; superseded)

1. Interface audit: PASS. Compared both existing delivered modules with the repository. The caller's signature and visibility are unchanged; the item's changed signature is declared in `coord/changes/tor-kernel-boundary-canonical.md`, with the false arbitrary-family statement replaced by the explicit constructed boundary. The construction and exactness modules are new declarations only.

2. Proof audit: PASS. Compiled all four modules with `lcompile.py --all`; there are no errors, forbidden declarations, or `sorry` in definitions. The only remaining `sorry` is the named theorem `tor_kernel_boundary_construction_exact`. The construction and naturality declarations use only the permitted foundational axioms (the exactness theorem and its caller additionally expose `sorryAx` through that documented hole).

3. Split statement audit: PASS. The exactness split theorem is strictly smaller than the caller: it concerns one explicitly constructed map and asserts no naturality or existential family. Its docstring gives the horseshoe and resolution-comparison argument and covers zero modules, identity surjections, and nonprojective middle modules. Searches recorded in the node found no duplicate Mathlib or library theorem.

4. Route and pruning audit: PASS. Naturality follows the direct lift-difference and cycle-vanishing proof in the source. The adapted caller uses the constructed map and the exactness split. Obsolete proof-only imports and old arbitrary-family dependencies are removed; the unit route remains recorded, and the construction exactness node retains its required lower dependencies.

5. Record audit: PASS. Node Lean statements match the delivered declarations verbatim, proof steps and dependencies match the proof bodies, and the change record documents the forced caller adaptation and statement correction. No realized unit step is bypassed.

Changed during this reading: appended this review only; no Lean proof or declaration was modified.

## Forced adaptations

### Sheaf.RingTheory.TorKernelBoundaryNaturality
Original against changed dependencies failed:
```
/tmp/forced-adaptation-zts0_rx8/lean/Sheaf/RingTheory/TorKernelBoundaryNaturality.lean:77:46: error: Application type mismatch: The argument
  δ
has type
  (F N : ModuleCat R) →
    (q : ↑F →ₗ[R] ↑N) → Function.Surjective ⇑q → ↑(((Tor' (ModuleCat R) 1).obj N).obj M) →ₗ[R] ↥q.ker ⊗[R] ↑M
but is expected to have type
  ModuleCat R
in the application
  tor_kernel_boundary_naturality_of R M δ

(with the modules compiled into /tmp/forced-adaptation-zts0_rx8/.lbuild) [1.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.


## Second reading by F3

1. Interface check: PASS with the declared correction. Independently diffed all
four modules against the read-only repository. Construction and fixed-map
exactness are new modules. The sole changed existing signature is the false
arbitrary-family naturality statement, recorded verbatim in the change record.
The caller's signature, visibility and docstring are byte-for-byte unchanged;
its import and proof edits are forced. Local whole-library search found no other
external user of the changed theorem. No target or existing definition changes.

2. Proof check: PASS. Read every definition and proof, then compiled the four
modules in import order through lcompile.py --all. Scratch #print axioms checks
of all eight public construction declarations and the naturality theorem show
only propext, Classical.choice and Quot.sound. The exactness theorem and caller
add only sorryAx, from the single named, reported exactness hole. The scratch
probe was removed from the delivery tree. No forbidden declaration, attribute,
or sorry in a definition occurs. The projectivity lift is backed by a proved
factorThru theorem; no holed existence theorem supplies data.

3. Split statement check: PASS. The one remaining theorem proves the two exact
pairs for a fixed map and asserts neither naturality nor an existential family.
It is strictly smaller than the caller and its docstring gives the essential
horseshoe-to-explicit-map comparison. Checked zero modules, identity and split
surjections, and the nonprojective middle-module case mathematically. Read the
actual free-resolution SES theorem and the resolution comparison API. Fresh
LeanFinder search for derived tensor exactness and augmentation lifts returned
snake-lemma exactness APIs and cotangent analogues, not this theorem; Loogle's
Functor.leftDerived query returned an unknown-identifier response. Local library
and Mathlib searches found no duplicate fixed-map boundary exactness theorem.
Verified the sources [00M0](https://stacks.math.columbia.edu/tag/00M0),
[00LZ](https://stacks.math.columbia.edu/tag/00LZ), and
[0111](https://stacks.math.columbia.edu/tag/0111). Closing the horseshoe comparison
requires substantial formalization, so the honest named hole remains.

4. Route and pruning check: PASS. The direct augmentation-lift difference
argument proves naturality without exactness, descends by the homology cokernel,
and transports by Mathlib's proved resolution-comparison theorem. Imports
supply the public construction, tensor, abelian homology and projectivity APIs;
caller-only proof imports are plain imports. Compared both old proof_deps lists
with the new plans and completed the direct pruning inventory above, including
the item's removed TorLongExactFirstVariable import. The unit's realized arrays
are empty; no realized unit step is bypassed. This is a correction/decomposition
with one false hole retired and one true hole added, zero net hole reduction.

5. Node check: PASS. Compared existing node changes field by field: they are
proof-route metadata, plus the item's declared statement correction. Lean
signatures, proof steps and proof_deps match the delivered code and remaining
exactness plan. Both new nodes have source, searches, creation, blueprint,
chapter/unit and Lean records. The caller uses precisely the constructed family,
fixed-map exactness and proved naturality recorded in its node.

Changed in this reading: completed the main No longer needed inventory and
appended this independent review. No Lean proof, signature or node was changed.

## Forced adaptations

### Sheaf.RingTheory.TorKernelBoundaryNaturality
Original against changed dependencies failed:
```
/tmp/forced-adaptation-mrg8s64u/lean/Sheaf/RingTheory/TorKernelBoundaryNaturality.lean:77:46: error: Application type mismatch: The argument
  δ
has type
  (F N : ModuleCat R) →
    (q : ↑F →ₗ[R] ↑N) → Function.Surjective ⇑q → ↑(((Tor' (ModuleCat R) 1).obj N).obj M) →ₗ[R] ↥q.ker ⊗[R] ↑M
but is expected to have type
  ModuleCat R
in the application
  tor_kernel_boundary_naturality_of R M δ

(with the modules compiled into /tmp/forced-adaptation-mrg8s64u/.lbuild) [14.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
