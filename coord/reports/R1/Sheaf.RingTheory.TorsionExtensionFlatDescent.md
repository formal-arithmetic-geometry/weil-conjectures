## What changed

Replaced the sole sorry in `Sheaf.RingTheory.TorsionExtensionFlatDescent` with a
complete proof of `LinearMap.exists_torsion_extension_flat_descent`, following
all five steps of its existing DAG plan. No signatures, definitions, visibility,
or imports changed. The presentation is applied to `ULift Q` and transported
back to Q, so the theorem keeps its original independent universe parameters.

The proof constructs the pullback submodule, applies cyclic descent and direct-sum
assembly, descends the canonical kernel lift by torsion Hom comparison, and
constructs E as the quotient by the lift's range. It checks injectivity,
exactness, and surjectivity directly. Flat tensor exactness identifies the kernel
of the tensor quotient map with that of the pullback projection; the two first
isomorphism theorems give the required equivalence, with both endpoint identities.
The source remains Stacks Project, Tag 05EG, first paragraph's reduction to a
cyclic presentation (https://stacks.math.columbia.edu/tag/05EG), as expanded in
the existing node and docstring.

## Proved and sorry left

Closed 1 original hole:
`LinearMap.exists_torsion_extension_flat_descent`
(node `lem-weil-pbc-torsion-extension-flat-descent`).

No sorry remains in the delivered module. Added 0 holes and split off 0 theorems.
The proof uses the existing stated dependencies
`Ideal.exists_torsion_cyclic_presentation`,
`LinearMap.exists_cyclic_extension_flat_descent`,
`LinearMap.extension_descends_of_summands`, and
`LinearMap.baseChange_bijective_of_ideal_power_torsion`.
Their existing holes are outside this delivery; the result is proved from these
statements, rather than claimed to be free of all transitive sorries.

Local single-file compilation succeeded without errors or warnings. The required
`deliver3.py --no-push` dry run performs the final compile and mechanical checks.

## No longer needed

None. All four original proof-dependency imports are used, and all nine DAG
proof dependencies remain relevant as statements or Mathlib constructions.
Temporary explicit Mathlib imports were removed because the original public
imports already provide those APIs; none was an original import to prune.
The unit route and the existing DAG proof plan are unchanged, so no node copy
is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The cyclic-presentation declaration places
its quotient in `Type (max u v)`, while this theorem permits Q in an independent
universe. Applying it to `ULift.{u} Q` and composing with `ULift.moduleEquiv`
resolves this interface mismatch without adapting either statement.

## Second reading by R1

1. **Interface unchanged — pass.** Read the complete module and its repository
   diff. The only change is replacing the original theorem's `sorry` body.
   Everything preceding that body is byte-for-byte identical, including its
   universes, hypotheses, conclusion, visibility, docstring, and imports. No
   definitions, extra modules, or change records are delivered.
2. **Proof and axioms — pass.** Independent single-file compilation through
   `lcompile.py` succeeded without errors or warnings. A scratch copy with
   `#print axioms LinearMap.exists_torsion_extension_flat_descent` compiled and
   reported exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last comes from existing open dependencies, as disclosed above. The
   delivered source contains no `sorry`, forbidden declaration, or hollow
   definition. Presentation and extension witnesses are eliminated locally
   inside a proof of an existential proposition; no public data definition
   chooses an arbitrary witness from an unproved existence theorem. The kernel
   lift is determined uniquely by the stated bijective Hom comparison. The
   final module is explicitly the quotient by that lift's range.
3. **Split statements — pass (none).** No new statement or hole is added.
   Read all four imported dependency statements and checked their use: the
   ULift presentation preserves the independent quotient universe; kernel
   torsion transfers across the equivalence; cyclic descent supplies precisely
   the summand hypothesis; Hom comparison both descends the lift and reflects
   its projection identity. The diagram chase handles zero modules and the
   ideals zero and top without any nonzero or faithfulness assumption.
4. **Route and pruning — pass.** Read the proof from its conclusion back through
   quotient exactness, the descended lift, the pullback, and the presentation.
   It follows the reduction in [Stacks Tag 05EG](https://stacks.math.columbia.edu/tag/05EG).
   Re-searched with `msearch.py` grep for extension/descent and Loogle for
   baseChange/Exact, and searched both Lean source roots for torsion-extension
   descent. The Mathlib descent hit concerns faithfully flat comonadicity,
   not this flat-neighbourhood extension theorem, and gives no shorter route.
   All four proof-only Sheaf imports are explicitly used. The three public
   Mathlib imports support the statement. No original dependency is obsolete.
   Read `dag/units/sk-thm-p1.json` including `realized`; no unit step or route
   is bypassed.
5. **DAG agreement — pass.** Read the item's node, its five proof steps,
   `proof_deps`, and `proof_origin`, and checked the declarations/Mathlib
   matches for its dependency nodes. The code realizes all five steps,
   including both endpoint identities. Flat tensor exactness, tensor
   surjectivity, base change, exact sequences, and quotient constructions
   realize the five foundational dependencies; the other four are the
   explicitly applied Sheaf theorems. The existing node accurately describes
   the proof, so no node edit is necessary.

Changes by the second reader: appended this independent review only. No Lean
or DAG repair was needed. Closed 1 of 1 original holes, added 0 holes, split
off 0 statements; transitive dependency holes remain as reported above.
