## What changed

Removed the duplicated helper declarations and repaired the scalar modules’ export
timeouts. Removed the source consumer’s redundant anonymous finite-extension example;
the full consumer then compiled in 46.1 seconds with all named public declarations intact. The four
original unitor and center-transport lemmas have one shared implementation; the source
consumer imports that implementation. The assigned theorem keeps its name, universes, parameters and mathematical statement. Its
conclusion now uses an exposed name for exactly its former proposition, as documented in
`coord/changes/A3-qbar-scalar-basis-proposition.md`.

Added the explicit, non-exposed `Mod.qbar_scalarUnitLeg` and its proved computation lemma
`Mod.qbar_scalarUnitLeg_eq`. The lower unit theorem uses this compact morphism name instead
of repeatedly inspecting the partially applied concrete derived-functor construction. Its
mathematical statement is identical: rewriting by the computation lemma gives the previous
unit statement verbatim. The assigned proof performs that rewrite before applying it.
The assigned theorem also uses `CondensedQbarDerivedScalarBasis`, whose exposed body is
literally its former full conclusion; this prevents the same export bottleneck there.
`qbar_complexCenter`, `qbar_homotopyCenter`, and `qbar_derivedCenter` are non-exposed, with
proved component equations; its public `qbar_derivedCenter_Qh` equation supplies
the computation needed by the source consumer, whose former private copy is removed.

Reduced `AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_derived_scalar_basis`
without changing its mathematical statement. The proof chooses coherent coefficient sections from the
unit-decomposition theorem, forms their explicitly constructed derived scalar actions,
and applies the proved direct-image scalar-compatibility lemma.

Added `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward`, with explicit regular-module
scalar multiplication, central actions on complexes and homotopy categories, their actual
localization to the derived category, and a complete direct-image compatibility proof.
The four existing unitor and center-transport lemmas are moved from `Compatibility.lean`
into this lower module under their original names, publicly. The old private declarations
are removed from `Compatibility`, which now imports the shared support module for its proofs.
Both consumers use the same four declarations; the prefixed duplicates are removed.
The consumer's five private scalar data definitions are abbreviations of the identical
explicit constructions in the support module. Its scalar-action formula and direct-image
formula invoke the proved shared API. The now-unused private transport pipeline is removed. All data
constructions here are explicit; none is selected from an admitted existence theorem.
All five scalar-center constructions and the scalar unit leg have non-exposed bodies
with public computation lemmas. The ordinary scalar-action formula supplies its
underlying-module calculation; `qbar_scalarNatEndo_app` supplies its natural-transformation
component.

Added `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit`, the remaining finite-support
coordinate construction and derived unit decomposition. Its statement uses actual coefficient
sections, with their inverse-image coherence, rather than arbitrary unrelated central maps.
The assigned theorem now proves the passage from that lower coefficient construction to its
required derived direct-image conclusion.

The source consumer also packages the ordinary scalar-unit isomorphism property in
`Mod.BasisUnitIsIso`, so its finite-basis record does not repeat large concrete categorical
expressions. Its finite-field freeness proof now specializes the proved private lemma
`Profinite.isFree_continuousMapRingObj`. All public consumer signatures are unchanged;
the generic lemma and the coordinate choices are proved, with no new obligation.
The transported finite basis is chosen from a proved local existence statement,
which keeps its large pullback construction folded during the remaining scalar calculations.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_derived_scalar_basis`.
The retained delivery has one strictly lower hole:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_unit`, node
`lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit`.
This is a decomposition with one original hole closed and one added, net zero holes closed.
The current repair retains that existing split and adds zero further holes.

The scalar-action support module has zero holes. In particular,
`AlgebraicGeometry.ProEtale.CondensedRing.qbar_lowerStar_derivedScalarEndo_of_eq` is proved,
as are the termwise localization, exact-functor transport, and adjunction helpers it uses.
The remaining hole needs the continuous finite-support basis coordinate construction,
the regular-module coproduct comparison, and its tensor/derived unit calculation.
It does not leave any direct-image scalar argument to the next worker.

The three scalar-basis modules compile and export within the unchanged 60-second limit.
The fresh complete exporting compilation took 17.3 seconds for the support module,
22.7 seconds for the unit module, 20.8 seconds for the assigned module, and 58.7 seconds
for the adapted consumer before removing its redundant example. The consumer without
that example compiled in 46.1 seconds. `deliver3.py --no-push` passed on commit `d7410460ff`, except for the independent
second reading that the next worker supplies; nothing was pushed. The consumers
`Sheaf.Paper.CondensedFlatCoefficientCalculus` and
`Sheaf.Paper.CondensedQbarBaseChangeCompatibility` compiled against the delivered overlay
in 54.0 and 19.4 seconds respectively. A source comparison confirms that all 12 named
public declarations of `Compatibility` retain their exact written signatures.
No new hole is added by this repair; the single retained unit hole is listed above.

## No longer needed

Removed the consumer's final anonymous example for finite-extension Shriek invertibility
and its now-unused local `HasCompactification f` variable. This example merely invoked
an already available instance and exported no named API. The retained profiler recorded
24.6 seconds linting that final command; removing it avoids repeating the concrete
comparison construction. No proof file was split and no compilation limit was changed.

Removed the new unit module's redundant direct public import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`; its support
module already publicly re-exports the same API needed by the unit statement.

The original node's direct proof dependencies
`lem-weil-pbc-finite-dimensional-linear-homeomorphism` and
`lem-weil-pbc-profinite-point-pullback` move to the lower unit node. They remain needed
for that coordinate argument; neither dependency module is claimed as pruned from the
whole import closure. The assigned node now directly uses only the unit and pushforward nodes.

Removed the prefixed duplicates `CategoryTheory.Mod.qbar_tensorπ_leftUnitor_hom`,
`CategoryTheory.Mod.qbar_leftUnitor_inv_hom`, `CategoryTheory.qbar_map_center_of_iso`,
and `CategoryTheory.qbar_map_center_rightAdjoint`. Their original source declarations now
live in the shared support module, so there is one proof of each proposition. No additional
split, obligation, or DAG node is added by this repair. Removed the consumer's private
`CategoryTheory.derivedCenter_Qh`; its one caller uses the shared public characterization.

Removed the consumer's unused private `Mod.map_scalarEndo`, `Mod.comap_scalarEndo`,
`Mod.extendIso_scalarEndo`, `CategoryTheory.map_derivedCenter`,
`CondensedRing.upperStar_scalarEndo`, and `CondensedRing.lowerStar_derivedScalarEndo`.
The surviving scalar direct-image formula uses the support module's proved formula.

The assigned module no longer directly imports `Sheaf.Paper.ProfinitePointPullback`:
the completed target proof uses only the lower unit theorem and the explicit pushforward API.
The lower unit node still records `ProfinitePointPullback` as a dependency of its
remaining coordinate construction. Its current admitted theorem does not use that
module in Lean; the worker completing the coordinate proof will add the import as needed. The assigned module's proof-only import of the unit-decomposition
module publicly imports `CondensedQbarScalarBasisPushforward`, so the target proof sees the
explicit scalar-action API without an unused large direct import. The unused `WeilConjectures.CategoryTheory.ModuleObjects.Free`
proof import was removed from the new support module. Its unused public import of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` is removed too:
the scalar compatibility theorem applies to arbitrary commutative condensed rings. No finite-free module API or
direct-image infinite-coproduct preservation is used in the proved compatibility argument.

## Where the brief, the DAG or earlier work was wrong

The first attempted split incorrectly inferred compatibility from an arbitrary family of
unit decompositions. Bases chosen independently on different schemes need not agree under
pullback or pushforward. That false draft is withdrawn and is not part of this delivery.
The delivered statement instead requires coherent coefficient sections, and the compatibility
of their actual scalar actions is proved using the inverse-image scalar formula, derived
localization, and the adjunction counit. This is the precise missing hypothesis in the draft.

The returned head duplicated four private lemmas word for word. Direct import from
`Compatibility` is cyclic, so this repair moves those four original proofs into the shared
lower support module and removes their old private copies. `Compatibility` is unclaimed;
its public signatures and mathematical constructions are unchanged; private scalar data
names are now abbreviations of the shared implementations. The large
infinite-support coordinate argument remains absent from the imported public API.

## New nodes

`lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit` states the coherent coefficient-section
construction and unit coproduct isomorphism. Its docstring and node give the complete planned
coordinate, tensor, and derived-localization argument, and identify exactly what remains.

`lem-weil-pbc-condensed-qbar-derived-scalar-basis-pushforward` records the explicit scalar
constructions and the proved generic direct-image compatibility theorem. Its proof uses
only monoidal scalar identities, localization naturality, and the derived adjunction.
Existing consumer public declarations retain their signatures and mathematical meaning. The unclaimed `Compatibility` module
shares the helpers and scalar data, reuses the proved direct-image calculation, and removes
the redundant private transport pipeline.
Change record: `coord/changes/A3-qbar-shared-scalar-helpers.md`.


The previously retained second-reading report is archived in the scratchpad because it
predates this repair. A new independent reading is required.

Change record for the proposition representation: `coord/changes/A3-qbar-scalar-basis-proposition.md`.


## Second reading by A3

Independent second reader, 2026-10-17.

1. **Interfaces — pass.** Read the complete diff of all four delivered modules against
   the read-only repository. The assigned theorem's only written signature change is
   the documented `CondensedQbarDerivedScalarBasis` wrapper. Its exposed definition body
   is byte-for-byte the original conclusion, with the same variable context. A fresh
   scratch consumer applying the new theorem at the original full type compiles. All
   12 existing named public declarations of `Compatibility` have unchanged written
   signatures. The private scalar abbreviations name the same explicit constructions;
   the other private changes and export attributes are covered by the shared-helper
   change record. No target statement is changed.

2. **Proofs and data — pass with the declared single hole.** Fresh exporting compilation
   of the support, unit, assigned, and consumer modules took 9.8, 17.5, 14.0, and 45.2
   seconds respectively, without errors or warnings. The existing downstream
   `CondensedFlatCoefficientCalculus` and `CondensedQbarBaseChangeCompatibility` compile
   against exactly this overlay (37.5 and 11.7 seconds), with no source adaptation. A
   fresh `#print axioms` audit of every declaration attached to the three delivered
   nodes finds only `propext`, `Classical.choice`, and `Quot.sound` in the support and
   proposition definition. Only the admitted unit theorem and the upper theorem that
   applies it additionally use `sorryAx`. There is exactly one source `sorry`, in the
   named unit theorem, and no forbidden declaration or hollow definition. The consumer's
   `htransport` existence proof constructs its witness from proved finite-basis lemmas;
   its classical choice therefore does not select data from an admitted theorem.

3. **Remaining statement — pass as a strict decomposition.** Checked the unit theorem
   clause by clause: it asserts coherent coefficient sections and the extension-unit
   coproduct formula for their actual scalar actions, with no direct-image assertion.
   For a section valued in a finite subextension F, pass to the finite compositum EF,
   choose a finite spanning set, and take the finite union of its Hamel coordinate
   supports; all values then have support in that union. Restricted coordinates are
   continuous over the complete base field. A finite sum of basis-vector sections
   lies in a finite subextension, giving the inverse. Finite covers preserve this
   finite support. Zero modules, empty schemes, identity maps, and finite-coordinate
   subspaces cause no exceptional case. The docstring and node describe pullback,
   tensor and exact derived descent of this explicit decomposition. Fresh LeanFinder,
   Loogle and Mathlib grep searches with different queries found only primitives,
   discrete/constant-coefficient results, and free condensed modules, not this theorem.
   Repository and source searches likewise found the finite-basis template, not the
   missing infinite-basis construction. It cannot be closed in a few minutes from an
   existing lemma. This is one original hole closed and one strictly lower hole added,
   net zero; it is not a completed sorry-free scalar-basis theorem.

4. **Route and pruning — pass.** Read the scalar multiplication, termwise center,
   homotopy descent, localization, exact-functor transport, and adjunction-counit
   arguments from top to bottom. The assigned proof uses precisely the unit and
   pushforward results. The four relocated unitor/transport lemmas replace the old
   private copies, resolving the recorded duplicate-proof return. Public imports
   supply types or definitions in public signatures; proof-only imports are plain.
   The old direct proof dependencies are both transferred to the lower unit plan
   and listed under No longer needed, not falsely claimed as pruned from the closure.
   The unit record `sk-thm-properbasechange` and all its realized statement/step nodes
   remain unchanged; neither transferred dependency is a realized unit step. No
   whole module is claimed pruned.

5. **DAG agreement — pass after metadata correction.** Compared each Lean statement
   with its node's verbatim `lean.statement`, read the old and new proof dependency
   lists, and checked proof-step uses and origins. New nodes have their source,
   blueprint ancestry, chapter/unit, creation, searches and Lean records. Corrected
   the two new nodes' source-place descriptions: the unit uses the finite-basis
   coordinate template, while the pushforward node uses the scalar/localization
   calculations. Added the independent coordinate searches and their actual results
   to the unit node. The existing node's proof and dependency changes match the proof.

Second reading changed only these node source/search records and this review report.
The submitted Lean proofs and constructions required no repair.
