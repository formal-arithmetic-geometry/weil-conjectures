## What changed

Reduced the unchanged theorem
`AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_section_restriction_surjective`
to two independent parts of the existing completion argument. Its proof now obtains the unique
lift on every quotient-power thickening, proves compatibility by finite-stage uniqueness,
algebraizes that compatible family, and checks the given restriction using both pullback
projections. The proof contains no `sorry`.

Added `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift`, with concrete quotient
spectra, their transitions, the pullbacks of a cover, and inclusions from the restricted cover.
Every auxiliary definition and projection/transition identity is constructed or proved directly.
Its one remaining theorem is unique lifting through a nilpotent thickening, for an arbitrary
surjective ring map, without local, Noetherian or depth hypotheses.

Added `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFormalHomAlgebraization`, whose
remaining theorem consumes actual maps on every thickening, with over-base and compatibility
equalities, and algebraizes them. It does not assume or produce a lift from a supplied map on
the zero section. Thus neither new theorem renames the item: finite-stage lifting and global
completion comparison are separate mathematical tasks, and the compatibility and final
restriction checks are proved in the item's module.

Updated the item's node to the actual four-step Lean argument. Both new nodes inherit the
original chapter and unit and retain the unit's Tag 0EY9 full-faithfulness route. Existing
statements, definitions and signatures are unchanged. There are no forced adaptations.
The three delivered modules compile through the prescribed `lcompile.py`; the unused
simplification argument identified by the compiler was removed.
Static declaration comparison confirmed the original signature unchanged, one original hole
closed, and exactly the two named new holes. All DAG references resolve and the edited
existing node changes only proof, proof_deps and proof_origin.

Sources read: Stacks [0EY9](https://stacks.math.columbia.edu/tag/0EY9),
[0EL8](https://stacks.math.columbia.edu/tag/0EL8),
[0EKP](https://stacks.math.columbia.edu/tag/0EKP),
[0BK0](https://stacks.math.columbia.edu/tag/0BK0), and
[0BQB](https://stacks.math.columbia.edu/tag/0BQB).

## Proved and sorry left

Closed the item's single hole:
`AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_section_restriction_surjective`
(node `lem-sbc-power-series-punctured-section-surjective`). No holes remain in the item.

Added two holes, each a public named theorem with exactly `:= by sorry`, its source and a complete
proof in words:

- `AlgebraicGeometry.Scheme.finiteEtale_adic_unique_lift`
  (`lem-sbc-finite-etale-adic-unique-lift`).
- `AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_formal_hom_algebraization`
  (`lem-sbc-power-series-punctured-formal-hom-algebraization`).

This delivery is a decomposition: one hole closed, two added, net minus one. It is not a
sorry-free proof of the mathematics. All sixteen auxiliary declarations in the `FiniteEtale.Adic`
namespace are definitions or fully proved lemmas; none selects data from an unproved existence
statement. The only choice in the item selects the uniquely determined finite-stage lift and
is used solely in a theorem proof.

Edge cases checked: for the first new statement, the identity ring map has zero kernel and every
thickening is a copy of the original spectrum; a surjection to the zero ring has empty section
and empty thickenings. The empty open is allowed. An empty source cover gives the unique empty
map; an empty target only admits the input map when the restricted source is empty, and
nilpotent thickenings preserve the same underlying space. The algebraization argument works
with rank-zero algebras and locally varying ranks; no connectedness, normality, integrality,
constant-rank, or nonempty-cover hypothesis has been added. The n=0 stage is R/ker(f), not R,
and the explicit zeroMap records its identification with the supplied restricted cover.

## No longer needed

Removed the two direct proof imports
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction` and
`Sheaf.RingTheory.FlatLocalDepthFormula` from the item's module, replacing them by
`Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFormalHomAlgebraization`.
Their nodes `lem-sbc-depth-two-hartogs-restriction` and
`lem-weil-pbc-flat-local-depth-formula` remain needed by the algebraization subproblem and
remain imported there. No existing node or module is pruned from this argument's closure.
All original public imports stay in the item to support its unchanged public signature.
Removed the redundant `Mathlib.AlgebraicGeometry.Noetherian` import from the new algebraization
module; its ring-class signature is supported by the retained `Sheaf.RingTheory.Depth` import.

## Where the brief, the DAG or earlier work was wrong

The original two proof dependencies address the depth/Hartogs inputs. Their Lean signatures
supply neither the internal-Hom completion comparison nor the nilpotent lifting/gluing
interface. The original second proof step had no dependency nodes despite containing both
substantial operations. This delivery states those missing interfaces and proves their
assembly, rather than treating that step as elementary.

LeanSearch returned Internal Server Error for both new statements; this is recorded as
unavailable, not as a negative result. LeanFinder, Loogle and the prescribed grep searches found
related ring-level formal-étale and completion facts but no exact global scheme interface.
Repository and whole-blueprint searches for nilpotent closed immersion, Tag 0BQB, completion
functor and finite locally free completion found no duplicate usable node. The proper
henselian finite-étale equivalence in the source library has a properness hypothesis absent
here and does not directly provide the needed lift on an arbitrary open.

## New nodes

`lem-sbc-finite-etale-adic-unique-lift` states unique finite-stage lifting for any quotient ring
map. It isolates the nilpotent formal-étale lifting and gluing part of Tag 0EL8, using Tag 0BQB.
Its module also constructs the quotient-power thickenings and their maps explicitly.

`lem-sbc-power-series-punctured-formal-hom-algebraization` states effectivity of a compatible
family of maps on all thickenings. Its proof in words retains the original Hartogs,
Krull-intersection, associated-point and finite-locally-free Hom comparison argument, then
checks multiplication and the unit by faithfulness and applies relative Spec. The two
original proof-dependency nodes belong here. No change record is required: no existing
interface or mathematical statement changed.

## Second reading by V2

1. **Interface comparison.** Compared the delivered target module with the repository version.
The theorem signature and all existing declarations are unchanged byte for byte; only the proof
and proof-only imports differ. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled each of the three delivered modules with
`lcompile.py`; all exit successfully. The target has no `sorry`; the only remaining holes are the
two named public split theorems, with no `sorry` in definitions and no forbidden declarations.
Scratch-copy `#print axioms` for the target and both split theorems shows only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` from the documented open statements.
Verdict: pass.

3. **Statements and decomposition.** Read both new statements and checked their edge cases and
docstrings. They are strict subproblems (finite-stage nilpotent lifting and formal Hom
algebraization), not restatements of the target, and each has a matching DAG node. Verdict: pass.
Independently searched LeanFinder for nilpotent morphism lifting and completion on vector
bundles, Loogle for formal-etale lifting and constant coefficients, and grep/rg for formal
étaleness, thickenings, and quasi-affine comparisons. No exact duplicate interface was found.
Read `FiniteEtaleThickeningLift`, which lifts objects rather than the maps in this statement,
and the topological-invariance interface, which still requires identifying the concrete
quotient-power maps as universal homeomorphisms. Neither directly closes the split theorem
without a further substantive geometric construction. Checked the mathematical routes against
Stacks Tags 0BQB, 0EY9 and 0EKP. The identity quotient, zero target ring, empty open, and
rank-zero finite étale covers give the stated expected edge cases.

4. **Pruning and route.** The target proof uses the two new interfaces and removes only the two
direct proof imports they replace; the original unit route through finite-stage lifting and
completion comparison remains represented in the DAG. Verdict: pass.
The unit's `realized` statement and step lists are already empty in the repository; this
delivery preserves them and the unit's written Tag 0EY9 route rather than bypassing it.

5. **DAG agreement.** The target node's proof steps, dependencies, and origin match the Lean
proof; new node records contain the required statements, sources, proofs, searches, and Lean
records. Verdict: pass.

Changed only this report by adding the second-reading findings; no Lean or DAG repair was needed.
This remains a decomposition, with one original hole closed and two lower holes added.
