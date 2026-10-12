## What changed

The target theorem now composes two strict reductions through an explicit quotient of continuous inhomogeneous two-cocycles. Added three modules: `GaloisUnitsTwoCocycles` defines the cocycle quotient and proves its coboundary relation is an equivalence; `GaloisUnitsHomogeneousComparison` states the homogeneous/inhomogeneous comparison; `EtaleUnitsTwoCocycleComparison` states the étale stalk and derived-invariants comparison. The target module imports the two comparison modules and composes their equivalences.

## Proved and sorry left

Closed one upper hole and added two lower holes: this is a decomposition, net minus one hole, not an axiom-free proof. Proved `AlgebraicGeometry.Scheme.nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup` by composing the two intermediate equivalences. The new named theorems left as `sorry` are `Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses` (node `lem-sc-galois-units-homogeneous-comparison`) and `AlgebraicGeometry.Scheme.nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup` (node `lem-sc-etale-units-two-cocycle-comparison`). The cocycle quotient definition and its setoid relation are fully proved. All four delivered modules compile cleanly; scratch probes compile for the discrete coefficient topology, the zero cocycle, and the trivial-group quotient. The two lower holes are strictly separate arguments: one only compares continuous cochain models, the other only compares the explicit inhomogeneous quotient with etale cohomology.

## No longer needed

Removed the redundant direct public import `Mathlib.Topology.Algebra.Group.Basic` from the new cocycle module: its declarations already arrive through `GaloisUnitsCohomology`. The original direct import of `Sheaf.AlgebraicGeometry.AbelianSheavesGModules` is no longer used by the target proof and was removed from the target module. AbelianSheavesGModules remains needed by the geometric intermediate theorem: no module is removed from the transitive target closure. The old proof dependencies `def-br` and `def-sc-galois-units-cohomology` remain statement dependencies, with their public imports retained. The old `lem-exc-abelian-sheaves-gmodules` dependency is used inside the new geometric comparison. Thus no old dependency is discarded from the transitive proof. `Field.nonempty_equiv_brauerGroup_galoisUnitsH2` compares algebraic Brauer groups with Galois cohomology, not with étale cohomology; the downstream BrauerGroup module uses the present item, so importing it would be circular.

## Where the brief, the DAG or earlier work was wrong

The original plan requires two substantial comparisons. The existing derived-invariants interface assumes a finite coefficient ring and cannot be applied to the integer module of units. They are now named as strict intermediate statements: the homogeneous/inhomogeneous cochain comparison and the étale stalk/derived-invariants comparison. No target statement was changed. The explicit cocycle relation was tested on the zero cocycle and on the trivial-Galois-group edge case.

## New nodes

`def-sc-galois-units-two-cocycle-classes` records the explicit quotient object. `lem-sc-galois-units-homogeneous-comparison` records the cochain-model comparison. `lem-sc-etale-units-two-cocycle-comparison` records the étale comparison. Their node files are in `dag/nodes/sec-curve-estimates/`. Search: LeanSearch returned an internal server error; LeanFinder found Hilbert 90 and profinite Galois group declarations but no degree-two comparison; Loogle found the continuousCohomology definition, functoriality and degree-zero comparison; source and blueprint grep found no matching explicit quotient. Sources checked: Stacks tags 04JQ, 03QU, 03QV (2) and 0DVG. The homogeneous/inhomogeneous formulas are an agent-written expansion of the cochain comparison, marked as such in the node. No change record is needed: existing public signatures and public imports are unchanged. The unit sk-thm-br route remains the injection into the function-field Brauer group and Tsen; this only decomposes the field comparison used inside that route.

## Second reading by N3

1. **Unchanged interfaces — pass.** I diffed the only existing delivered module,
`EtaleGaloisUnitsComparison`, against the repository. Its theorem signature and existing docstring
are byte for byte unchanged, as are both existing public imports. The only differences are two
proof-only imports replacing one proof-only import and the composition proof. The other three
modules are new; none changes an existing definition or target.

2. **Kernel check and holes — pass as a decomposition.** All four files compile without warnings
using `lcompile.py --all`. I also compiled scratch `#print axioms` probes for all seven delivered
declarations: the four explicit definitions use only standard axioms, and the two comparisons and
the target additionally use `sorryAx`, as the two named holes require. There are exactly two
`sorry`s, each the whole proof of a named theorem with its node and proof docstring; no prohibited
construct or hollow definition occurs. The target composes actual equivalences in a proposition,
not data chosen in a definition from an arbitrary existence assertion. One original hole is closed,
two are added: net minus one, explicitly a decomposition, not an axiom-free proof.

3. **Truth, size, and reuse — pass.** I read Stacks etale-cohomology.tex, lines 9007–9170:
0DVG defines the exact differential used here and states the profinite comparison (without its
proof); 04JQ identifies abelian stalks with discrete Galois modules; 03QU transports cohomology;
03QV(2) identifies the multiplicative stalk with separable-closure units. The new docstrings supply
the change-of-variables and effaceability arguments rather than claiming Stacks supplies omitted
details. I checked Mathlib `ContCohomology/Basic.lean`: the recursive constant-minus-coinduced
map expands to alternating omissions, and `Continuous/Basic.lean` gives the diagonal action.
`ModuleCat/Topology/Homology.lean` constructs the algebraic kernel and quotient by the actual
image, not its closure, so forgetting topology preserves the claimed classes. The homogeneous
formula and its inverse transform degrees one and two to the displayed equations. The geometric
comparison uses exact stalk equivalence, invariants, and coinduced acyclicity; it contains no
homogeneous comparison. These are separate strict parts of the original argument, not a renamed
copy of it. The coefficient topology is discrete. Zero cocycles and the trivial-group quotient
were checked in compiled scratch proofs; in the trivial group every constant two-cocycle is a
coboundary. No perfection or characteristic hypothesis is needed for the stalk identification.
I independently searched with LeanFinder for continuous homogeneous/inhomogeneous cochain
quotients and for étale stalk units and invariants, with Loogle for continuousCohomology, and with
`rg` in Mathlib, the upstream checkout, Sheaf, and DAG nodes. Search returned algebraic group
cohomology results, degree-zero continuous comparison, and étale field structure results, but no
matching continuous degree-two comparison. Existing derived-invariants, short-exact-cochains, and
coinduced-homotopy interfaces all assume a finite coefficient ring, so cannot be applied to ℤ.
Neither remaining hole is closable by a short application of those interfaces.

4. **Top-down route and pruning — pass after minor repair.** The explicit quotient is constructed
before the two reductions; the target only composes those reductions. The original public imports
are needed by its signature. The new comparison modules publicly import only their signature
objects; AbelianSheavesGModules and the Abel tactic are proof-only. I removed the redundant public
Mathlib.Topology.Algebra.Group.Basic import from the quotient module and recompiled. The report's
No longer needed section now accounts for all three old proof dependencies and distinguishes a
direct import removal from transitive module pruning. No transitive module is pruned. The unit
sk-thm-br still follows injection into the function-field Brauer group and Tsen; I read its unit
record (its realized statement and step lists are empty) and its blueprint step. This delivery
changes only a subordinate field comparison and leaves that unit record untouched.

5. **Nodes agree — pass.** The existing node now cites exactly the two comparison theorems that
the Lean proof composes. The definition node records the same cocycle equation, coboundary
relation, and quotient; reflexivity, symmetry, and transitivity are actually proved. Both new
comparison nodes match their theorem signatures, hypotheses, chapter, unit, sources, and complete
proof docstrings, with created and blueprint records and search records. Their proof_deps are the
union of their steps' uses. The original node's statement and statement dependencies are unchanged.

**Second-reader changes:** removed one redundant public topology import; corrected the scratch
edge-case probe's stale `GaloisUnitsCoefficients` name to `galoisUnitsTopRep`; clarified pruning and
the algebraic Brauer comparison in this report; added the independent reading and axiom checks.
No mathematical statement, construction, or existing proof docstring was changed.
