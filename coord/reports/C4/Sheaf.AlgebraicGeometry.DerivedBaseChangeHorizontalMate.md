## What changed

Completed `AlgebraicGeometry.schemeDerivedBaseChange_horizontal_mate` with its signature
unchanged. The existing attempt supplied two proved private helpers: `horizontal_mates`
for the generic adjunction calculation and `pullback_source_square` for coherence.
Added the proved private definitional equation `baseChange_eq`. Rewriting with it avoids
repeated expansion of the large selected canonical adjunction and comparison expressions
in the final specialization. Removed the earlier attempt’s two unnecessary file-level transparency options.
No definitions, public interfaces, or imports changed.
The node records the explicit proof and this final rewrite.

The complete module compiles locally in 33.4 seconds after removing the unnecessary options, with no errors or warnings.
The first compilation reproduced the previous 60-second timeout; the revised proof
compiles without raising the limit or splitting the module.

Searches run in this session: leanfinder for horizontal composition of base-change
morphisms as adjunction mates (generic `mateEquiv_hcomp` and related results), loogle
for `Adjunction.rightAdjointUniq_hom_app_counit` (one exact generic result), and grep
for scheme-derived horizontal identities (no Mathlib matches). Repository searches
found no shorter completed proof of this statement. The inherited generic calculation
uses the Mathlib counit API already available through `RelativeMVMaps`.
Sources read: the three dependency nodes and their Lean signatures; the unit record;
Mathlib adjunction counit and uniqueness API; Stacks
[08HY](https://stacks.math.columbia.edu/tag/08HY) for the base-change transpose and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S) for pullback composition.
The untracked literature sources are absent from this clone; the cited Stacks pages
were read online. The unit's realized lists are empty and its route is retained.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.schemeDerivedBaseChange_horizontal_mate`
(node `new-lem-pc-derived-base-change-horizontal-mate`).
No `sorry` remains in the delivered module. No holes added or split off.
The three private helpers are fully proved. The theorem uses the existing foundational
declarations; this does not claim that their transitive dependencies are free of holes.

## No longer needed

None. The sole import `Sheaf.AlgebraicGeometry.RelativeMVMaps` is needed by the public
statement and proof. All original proof dependencies remain used:
`def-pc-derived-base-change-map`, `def-pc-relative-mv-maps`, and
`lem-pc-ringed-spaces-derived-pullback-composition`.
No imports or DAG dependencies were removed. `DerivedBaseChangeSourceIso`,
`DerivedBaseChangeHorizontalPasting`, and Mathlib `Adjunction.Mates` are not needed
as additional imports; the inherited coherence calculation is proved locally.

## Where the brief, the DAG or earlier work was wrong

The previous report claimed the theorem was proved even though its final specialization
had not passed compilation. Its mathematical argument was usable, but unfolding
`relativeMVAdj` and `relativeMVComp` repeatedly at that step caused a timeout.
The completed proof uses a small proved equation to retain those expressions as named
terms. No mathematical statement or definition needed correction.

## Second reading by C4

1. **Visible interface: pass.** Compared the sole delivered Lean module against the
   repository using `diff`, and independently compared the public theorem signature
   byte for byte. Its signature, section instances, visibility, existing docstring,
   and sole public import are unchanged. The additions are three private proved
   helpers and the replacement of the original proof. There are no definitions or
   change records in this delivery.
2. **Proof and trust: pass.** Independently compiled the module with `lcompile.py`:
   exit 0, 29.1 seconds, no errors or warnings. A scratch copy with `#print axioms`
   for the public theorem and each of `horizontal_mates`, `pullback_source_square`,
   and `baseChange_eq` compiled in 33.0 seconds. Every result uses only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. A source scan found no
   `sorry`, axiom, unsafe, opaque, implemented_by, or extern. The selected
   comparisons and adjunctions are the existing pinned canonical data: the new
   proof only extracts their associativity property and constructs no arbitrary
   witness or hollow definition.
3. **Split statements: pass, none added.** No theorem is split off and no new
   public statement or DAG node is introduced. Read all three private helper proofs:
   the generic identity follows by the two counit comparison equations, transpose
   injectivity, and naturality; the square identity follows by three associativity
   instances and equality-transport naturality; the final helper is definitional.
   These arguments require no cartesian square, nonzero object, or nonempty scheme;
   identity arrows and zero objects introduce no missing assumption. Independent
   leanfinder search for pasting transposes with right-adjoint uniqueness, loogle
   for `Adjunction.comp_counit_app`, and grep for uniqueness/transpose equations
   found generic support but no exact public replacement. Related source-square
   helpers in the library are private, so importing them cannot replace this proof.
4. **Route and pruning: pass.** Inspected Mathlib `mateEquiv_hcomp`, the uniqueness
   counit API, the library's source-isomorphism helper and ordinary horizontal
   pasting theorem. The latter pastes in the other direction and is not this
   identity. Mathlib's generic pasting still requires transport to the two pinned
   composite adjunctions and the same square coherence; no shorter direct
   replacement was found. The sole import `RelativeMVMaps` is required by the
   public signature. All three old proof dependencies are still used, so the
   report's `No longer needed` list is complete. The unit
   `sk-thm-picard-semicon` has empty realized statement/step lists; no unit route
   is removed or bypassed.
5. **DAG: pass.** Compared the delivered node to the repository node. Only `proof`
   and `proof_origin` differ; `proof_deps` stays the exact union of the proof-step
   uses. The three steps match square coherence, the generic mate calculation,
   and specialization via `baseChange_eq`. The unchanged Lean record matches the
   public theorem. No new-node fields or statement-change record are needed.

Second reading changed only this report by appending the independent verification.
No Lean or DAG repair was needed. The delivery closes one original hole, adds zero
holes, splits off zero statements, and prunes no module.
