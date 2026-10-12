## What changed

Completed both proofs in `Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent`.
All original public signatures, visibility, definitions and theorem docstrings are unchanged.
The proof constructs the continuous coordinate transformations in degrees one and two,
checks the differential formulas, and identifies the concrete kernel/image quotient with
continuous two-cocycles modulo continuous coboundaries. Every new helper is private and proved.
No object is selected from an unproved existence theorem.

Added proof-only imports `Mathlib.FieldTheory.Galois.Profinite` and `Mathlib.Tactic.Abel`.
Updated the two existing node proofs and proof origins to describe the actual argument.
The scope commands are documented in
`coord/changes/galois-units-homogeneous-proof-scopes.md`; no dependent module needs adaptation.

Repaired the preserved attempt's compilation timeout by explicitly assigning universes to
private cochain helpers: `R : Type r`, `G : Type v`, `A : TopRep.{v} R G`, and
`HC₁`, `HC₂ : TopModuleCat.{v} R`. Profiling showed repeated universe inference expanding
nested coinduced representations, particularly in `kernelEquiv`. The same argument with
these annotations compiled without errors or warnings in 22.6 seconds under the unchanged
60-second limit. The original public declarations still have only their original universe `u`.

Preserved searches found no continuous degree-two comparison in Mathlib or the two library
roots; abstract group-cohomology comparisons do not supply this continuous comparison.
The proof uses Mathlib's curry, concrete kernel/cokernel, and open-stabilizer APIs.
Read Stacks Section 0DVG at https://stacks.math.columbia.edu/tag/0DVG: its displayed
inhomogeneous differential agrees with both degree formulas proved here.

## Proved and sorry left

Closed both original holes:

- `Field.nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle`
  (`lem-sc-galois-units-homogeneous-cocycle-equivalence`).
- `Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv`
  (`lem-sc-galois-units-homogeneous-cocycle-descent`).

Holes added: none. No `sorry` remains in the module. No new modules or nodes were added.
This is a proof of both declarations, not a decomposition.
The prescribed `deliver3.py S1 Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent
--no-push` printed `OK (dry run)` for commit `89d81b81d5`: local compilation and
the comprehensive axiom probe succeeded, and preflight passed except for the second
reading reserved for the next worker. No nonstandard axioms were reported.
No delivery was pushed. The previous independent reading belongs to the earlier attempt;
a fresh second reader must check this repair before delivery.

## No longer needed

None. Both original definition imports and both original dependency nodes remain needed.
The two added Mathlib imports supply local compactness of the Galois group and additive
normalization. No new Sheaf proof-dependency modules are imported.
`dag/units/sk-thm-br.json` has empty realized statement and step arrays; its
Brauer-injection/Tsen route is unaffected.

## Where the brief, the DAG or earlier work was wrong

The descent node's prose requires boundary compatibility, while the Lean hypothesis supplies
only an arbitrary type equivalence. The proof constructs the canonical coordinate equivalence
and proves its boundary compatibility explicitly; the supplied equivalence hypothesis is
redundant. The original theorem statement is true and remains unchanged.

Stacks Section 0DVG supplies the inhomogeneous differential, rather than the comparison with
Mathlib's recursive homogeneous complex. The updated proof origins identify the explicit
homogeneous calculation as the worker's argument based on that source.

The earlier attempt had successful checks followed by repeated compilation timeouts.
The repair removes expensive implicit universe inference in the private constructions,
without splitting a proof or extending the compilation limit. Its old second-reading section
was removed so the new reader can record an independent check of this version.

Preflight conservatively treats additional proof context commands as interface changes.
The scope change record documents those commands and the unchanged direct importer
`Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison`. No existing interface or target changes.

## Second reading by S1

Independent reading of the repaired version, with the whole delivered module, repository
version, both node records, coefficient/cocycle definitions, direct importer, and
`dag/units/sk-thm-br.json` open. Read the displayed differential in
[Stacks Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG), Mathlib's
`ContCohomology/Basic.lean`, `FieldTheory/KrullTopology.lean`,
`FieldTheory/Galois/Profinite.lean`, and `ModuleCat/Topology/Homology.lean`.

1. Interface: PASS. The sole delivered module was compared with the repository by `diff`.
   Both original theorem signatures occur byte for byte in the delivery, including the
   field hypotheses and the descent theorem's `h` hypothesis. The cocycle abbreviation's
   signature and body, all existing declaration visibility and docstrings, and both public
   imports are unchanged. The declaration parser independently reports no statement
   changes. All added declarations are private. The recorded scope commands introduce
   neither public instances nor extra hypotheses on the original declarations. The two
   added Mathlib imports are plain proof imports. There are no adapted modules.

2. Proof and trust: PASS. The actual module compiled locally through `lcompile.py` in
   26.0 seconds, without errors or warnings. A fresh scratch copy with `#print axioms` for
   the abbreviation and both original theorems compiled in 27.5 seconds; each reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The delivered source contains no `sorry` or forbidden declaration/implementation hook.
   `coordinates` evaluates at `(1,g,g*h)`; `reconstruct` explicitly constructs and curries
   the jointly continuous map `rho(a)(c(a^-1*b,b^-1*d))`. The invariant identities and
   both inverse laws are proved. The degree-two differential has signs `+,-,+,-`;
   the degree-one differential gives `rho(g)(b(h))-b(g*h)+b(g)`. For the quotient,
   `boundary_coordinates` changes `x-y` to `y-x` using negation of the range, then proves
   both directions using evaluation or explicit one-cochain reconstruction and injectivity.
   `concreteData` uses the actual linear kernel and quotient by the actual image, as in
   Mathlib's topological-module homology construction; it chooses no arbitrary witness
   from an open theorem. The action-continuity proof uses integrality of the separable
   closure and open stabilizers, and transfers field-element fibers to unit fibers by
   `Units.ext`. Local compactness comes from the profinite Galois-group instance.

3. Split-off statements: PASS, none. No new public statements, nodes, or holes are added;
   every private helper is proved. As edge-case checks on the formulas, for a trivial
   group the degree-two cocycle equation is automatic and the degree-one coboundary is
   `b(1)`, so the quotient is a singleton as required; for zero coefficients both models
   are singleton types. No normalization at identity, finite-group assumption, or
   characteristic restriction was introduced. Independent Loogle search for
   `continuousCohomology` and Lean Finder search for continuous compact-open cochain
   coordinate changes found no ready-made continuous degree-two comparison. Searches
   of `lean/Sheaf`, upstream representation modules, and Mathlib's continuous-cohomology
   directory likewise found no shorter proved route. Abstract `groupCohomology` cocycle
   comparisons returned by the search do not establish continuity for this topology.

4. Top-down route and pruning: PASS. The two original holes are opened and proved from
   explicit coordinate constructions and Mathlib's existing kernel/cokernel APIs, with
   no relocation of an entire claim into another holed theorem. Both original definition
   dependency nodes are used; neither old `proof_deps` entry can be pruned. The added
   Galois/profinite import supplies compactness for joint evaluation and currying, and
   the Abel import supplies the displayed additive rearrangements. The original public
   import interface is preserved. The unit's `realized.statement` is empty and its only
   realized step is empty; the Brauer-injection/Tsen unit route is unchanged.

5. DAG agreement: PASS. Both existing node files change only `proof` and `proof_origin`;
   their statements, Lean signatures, and `proof_deps` remain unchanged. The equivalence
   node's four steps match joint action continuity, inverse coordinate constructions,
   the differential identity, and identification of categorical cycles with the concrete
   kernel. The descent node's four steps match concrete homology data, the degree-one
   formula, boundary-relation compatibility, and `Quotient.congr`. The unions of `uses`
   are exactly the recorded two definition dependencies. The origin distinguishes the
   Stacks differential from S1's explicit homogeneous calculation. The prose's reference
   to a compatible equivalence is satisfied by the canonical equivalence constructed in
   the proof; the weaker arbitrary-equivalence hypothesis is retained and is redundant.

Second reading changed only this report by adding the independent review. No Lean proof,
statement, definition, import, or node repair was needed. Confirmed two holes closed,
zero holes added, zero split off, and no dependency pruned.
