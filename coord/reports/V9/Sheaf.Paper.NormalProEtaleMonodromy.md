## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.normal_proEtale_monodromy` with a
complete assembly from the existing normalized realization, completed-system
comparison, and integral-fibre reconstruction. Its statement, the
`NormalProEtaleMonodromy` structure, and every public import are unchanged.

The proof restricts the realization to lisse objects, obtains its full and faithful
instances, and proves essential surjectivity by composing reconstruction's
rationalization isomorphism with an integral-model isomorphism. Mathlib's
`Functor.asEquivalence` then constructs the equivalence in the required direction.
`ObjectProperty.liftCompιIso` identifies its inverse realization with the original
functor. All normalization and naturality fields are the original fields of that
same realization.

Added `Sheaf.Paper.NormalLisseCompletedLattice` to isolate the remaining geometric
lattice construction and coefficient/module transport. It has one theorem, which
asserts only existence of a completed integral lattice for a given rational module,
using any specified completed comparison. It neither mentions a representation nor
constructs a monodromy equivalence. This is the finite-cover/descent portion of the
old plan, strictly below the reconstruction and equivalence assembly now formalized.
The item imports it privately. Both modules and the corresponding DAG nodes are
included; no other existing module is modified.

Validation: `lcompile.py --all` compiled both delivered modules without diagnostics:
26.2 seconds for the lattice module and 39.5 seconds for the item, both below 60 seconds.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.Scheme.normal_proEtale_monodromy`
(node `lem-a1-normal-proetale-monodromy`). No holes remain in the item module.

Added one hole:
`AlgebraicGeometry.ProEtale.CompletedLisse.normal_lisse_completed_lattice`
(node `lem-a1-normal-lisse-completed-lattice`). Its proof is exactly `by sorry`;
its docstring gives its source and the finite-cover, descent and coefficient
transport argument. There are no other holes added, and none inside a definition.
This is a decomposition: one upper hole closed, one lower hole added; net zero.
The existing reconstruction theorem and realization theorem are reused without edits.

Returned-delivery repair (reviewer C-a33b4, returned head a33b4d7d3): removed the
item's `set_option warn.sorry false`. The landing hole census matched the `sorry`
component of this option name as an unattributed hole at line 37, offset 1566.
There was no anonymous proof hole to split. With the option removed, the same
census reports no markers or attribution warnings in the item, and exactly the
named lattice theorem's hole in the new module. The repaired item compiles on the
server in 9.4 seconds without diagnostics. The assembly and signatures are unchanged.

Edge cases checked mathematically: rank zero uses the zero integral module and
zero representation; ramified coefficient extensions use the prescribed uniformizer
and the same comparison map, with no unramified assumption. A connected base is
nonempty. Neither the new lattice lemma nor the assembly asserts lattice existence
on a nonnormal base, so the nonnormal nodal-curve example of BS 7.4.9 is not excluded
by an invalid stronger statement. No action-continuity hypothesis is dropped:
reconstruction returns an object of `SfContinuousRepresentations`.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`;
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`;
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`;
- `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent`;
- `Sheaf.Paper.EtaleLocalMonodromyRealization`;
- `Sheaf.Paper.LatticeSheafLocallyConstant`;
- `Sheaf.SecPurity.NormalLocallyConstantFiniteSection`;
- `Sheaf.SixFunctors.IntegralLisseReductionEquivalence`.

The first assertion of `lem-sfb-etale-local-monodromy-realization` is already the
separate declaration `exists_sf_monodromy_realization` in
`Sheaf.Paper.EtaleLocalMonodromyRealizationBase`. The assembly uses it directly;
the local finite-diagram assertion plays no role in global essential surjectivity.
The full theorem can still be imported transitively by reconstruction, so this
packet claims no whole module becomes unreachable from the targets.

The finite-cover presentation and finite-etale lattice descent remain needed below
the new lattice theorem. Adic-limit finiteness, DVR freeness, finite-section geometry,
and integral reduction remain needed by the existing reconstruction or the new
lattice node. Their proofs are not duplicated in the assembly. In particular none
of these mathematical dependencies is withdrawn from the library.

Pruned obsolete direct `tool_uses` entries from the item node:
`lem-sfb-integral-lisse-reduction-equivalence`,
`lem-sfb-etale-local-monodromy-realization`,
`lem-weil-pbc-lattice-sheaf-locally-constant`,
`lem-weil-pbc-lisse-lattice-finite-etale-descent`,
`lem-pod-adic-limit-finite-modules`, `lem-sc-dvr-fg-torsionfree-free`,
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and
`lem-sfb-noetherian-space-compact-subsets`. These are no longer direct assembly
steps. The completed-system-comparison approval remains. No new maintainer approval
is written by this delivery.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid, but its declared dependencies do not directly
compose at their current Lean types. The finite-cover presentation has `E : Type u`
for `X : Scheme.{u}` and uses sheaf modules over a uniformizer-localized completion;
the item has `E : Type (u + 1)` and continuous rational coefficients. The descent
theorem uses a `Type` coefficient field and internal abelian-sheaf modules, while
reconstruction uses the `CompletedLisse.Base`/`Comparison` API. The new theorem
records the required transport and lattice descent without changing those interfaces.
The topology and quasi-compactness assumptions are already carried by the pointed
base; the assembly does not need to extract them again from the finite-cover theorem.

`exists_normal_completed_integral_model` has an overlapping lattice conclusion but
its node `lem-a1-normal-completed-integral-model` explicitly depends on the current
monodromy theorem. Applying it here would create a circular proof. The new lattice
node instead follows the acyclic finite-cover/descent argument already prescribed
by this item's node. Searches found no existing acyclic theorem with the needed
completed-comparison conclusion. All five existing dependency branches were checked
for a path back to the item; none has one.

The latest blueprint's Rankin unit differs textually from its historical unit record.
This packet changes neither version or its route; it supplies the same normal-base
monodromy input beneath the degree-zero compact-support argument.

## New nodes

`lem-a1-normal-lisse-completed-lattice`, in
`dag/nodes/sec-purity-real-sheaves/lem-a1-normal-lisse-completed-lattice.json`, owns
`AlgebraicGeometry.ProEtale.CompletedLisse.normal_lisse_completed_lattice` in
`Sheaf.Paper.NormalLisseCompletedLattice`. It combines the existing parent steps 1
and 3, including the coefficient-universe and internal-module transports needed to
apply the finite-cover and descent declarations. Its proof dependencies are
`lem-a1-normal-lattice-finite-cover-presentation` and
`lem-weil-pbc-lisse-lattice-finite-etale-descent`. LeanSearch, LeanFinder, Mathlib
grep, and whole-blueprint searches are recorded. No existing definition or theorem
signature is changed, so no change record or consumer adaptation is required.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
