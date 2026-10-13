## What changed

Repaired the returned import cycle by replacing the proof-only import of
`Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection` with the new module
`Sheaf.AlgebraicGeometry.IdealPowerTorsionFreeSectionLifting`. The original
extension theorem and its signature are unchanged. Its proof still constructs
a torsion-free carrier, identifies the complement, factors recursive powers,
transports through the power comparison, and proves the scalar identity on all
smaller opens by injectivity, naturality and linearity.

The new torsion-free lifting theorem returns only a map with a specified value
at the lift of 1. It assumes that every ideal-power annihilator in its target
vanishes, and works on general quasi-compact quasi-separated schemes. It does
not produce a carrier in an arbitrary module, prove the power comparison, or
assert the all-opens scalar equation. It is a strictly partial step of the
argument, not the original theorem renamed or its hypotheses repackaged.
Its docstring gives the direct affine denominator and finite gluing argument
of Stacks Tags 01PM and 01PQ. It does not import the general quotient theorem.

Removed the resulting unnecessary zero-object, annihilator-quotient and cokernel
cancellation code and the proof-only QuasicoherentKernel import. No other
existing module, interface, or target was changed. The second reader replaced the
new lifting module's unnecessary public Coherent import with the directly required
Mathlib quasi-coherent module import. It also narrowed the quasi-separatedness
import to `Mathlib.Topology.QuasiSeparated`, which defines the required class. The original private
`power_factor` helper remains proved.

Compiled all four sandbox modules in import order through lcompile.py.
Independently checked project-source imports with sandbox overlays: the item's
92-module closure is acyclic. The prior single-file compilation used compiled
dependencies and therefore did not detect the source-level cycle.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.quasicoherent_open_section_ideal_extension`
(node `lem-pc-quasicoherent-open-section-ideal-extension`). No sorry remains in
the item's module.

Three new public theorem holes remain, each exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.Modules.exists_idealPower_torsionFree_section_carrier`
  (`lem-pc-ideal-power-torsion-free-section-carrier`).
- `AlgebraicGeometry.Scheme.Modules.idealData_recursive_power_comparison`
  (`lem-pc-ideal-data-recursive-power-comparison`).
- `AlgebraicGeometry.Scheme.ideal_power_torsionFree_section_lifting`
  (`lem-pc-ideal-power-torsion-free-section-lifting`).

This is a decomposition: one upper hole closed, three lower holes added;
the repair adds one lower hole relative to the returned delivery. It is not
a sorry-free proof or positive net hole progress. No data definition contains
sorry or chooses an arbitrary existence witness. Lifts of 1 and power factors
are uniquely determined by the injective inclusions used downstream.

Edge cases: the zero ideal has empty complement and torsion-freeness forces
the target module to vanish; the unit ideal uses degree zero. The empty scheme
and zero module have unique sections and maps. Degree zero is the identity
power inclusion. For a general ideal with empty complement, it is locally
nilpotent on affines and torsion-freeness likewise forces the module to vanish.

## No longer needed

Removed proof-only imports relative to the repository version:

- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension`;
- `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules`.

Their nodes are included in the complete replaced-dependency list below.

The second reader also removed `Sheaf.AlgebraicGeometry.Coherent` from the new
lifting module, replacing it with
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: only the Mathlib
quasi-coherent and finite-type classes occur in the new signature. It narrowed
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` to
`Mathlib.Topology.QuasiSeparated` for the topological class in that signature.

Removed proof-only imports from the returned sandbox version:

- `Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection`, node
  `lem-weil-pbc-ideal-power-quotient-local-lifting-section`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The quotient-lifting theorem and its evaluation-eventually-zero dependency
chain are no longer used by this proof. They may still be needed elsewhere;
no whole-library pruning is claimed. The general sections comparison
`Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen`
(`lem-weil-pbc-sections-over-quasi-compact-open`) is also not imported.

The original direct dependencies replaced by the carrier/comparison decomposition:

- `lem-weil-pbc-coherent-artin-rees`;
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`;
- `lem-weil-pbc-module-finite-type-submodule-extension`;
- `lem-weil-pbc-noetherian-acc-quasi-coherent`;
- `lem-weil-pbc-sections-annihilated-by-ideal`;
- `lem-weil-pbc-sections-over-quasi-compact-open`;
- `pqf-lem-coherent-ft-locnoeth`.

All except the general sections comparison remain planned dependencies of the
carrier/comparison nodes. The new lifting node supplies the torsion-free affine
construction and gluing directly, without the quotient evaluation chain.
No original public import was removed. The unit's realized statement and step
arrays are empty, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The return is correct: the earlier report's assertion that the smaller quotient
lifting module was cycle-free was wrong. Its current proof imports reach
IdealPowerEvaluationEventuallyZero, FormalPolynomialPowerLifts,
Modules.IdealTimesQuasiCoherentAffineSections, CoherentFormalModule,
ModuleSupportProperOverBase, ClosedImmersionPushforwardAnnihilated,
AffinePushforwardBaseChange and DirectImage.FiniteFreeComplex; the integral
ideal and open-map extension chain then returns to this item. The repair
removes this import entirely, rather than relying on cached compilation or
changing another group's module. The source-closure check now passes.

The earlier carrier/comparison dependency problems persist: their mathematical
sketches use results whose existing module packaging cannot be imported here.
They remain explicit deferred statements with direct proof sketches, not proof
imports. Future workers must also respect import direction.

For the new lifting step, LeanFinder found localization and adic-completion
results, Mathlib grep found only unrelated torsion-free sections, and Loogle
found no result (unknown project identifier idealSheafPower). The existing
general quotient lifting statement was examined and rejected solely because
of the demonstrated source import cycle. The new specialized theorem is
supported directly by the torsion-free case of 01PM and finite gluing of 01PQ.

The former second-reading text describes the returned version and is removed;
the repaired code awaits a fresh independent reading.

## New nodes

`lem-pc-ideal-power-torsion-free-section-carrier` prepares a quasi-coherent
submodule carrying the section with zero ideal-power annihilators. Its proof
sketch retains finite-type extension, stabilization and Artin-Rees.

`lem-pc-ideal-data-recursive-power-comparison` compares the ideal-data and
recursive image powers, including degree zero, and gives quasi-coherence.
It has no prescribed section or extension conclusion.

`lem-pc-ideal-power-torsion-free-section-lifting` is the new repair node. It
isolates the torsion-free denominator construction and finite affine gluing,
without annihilator quotients or a dependency on the cyclic quotient module.
Its source, complete proof sketch, three recorded searches, blueprint ancestry,
and verbatim Lean signature are included. The parent node's proof and
proof_deps now use it in place of quotient lifting. No change record is needed:
all existing signatures and visibility are unchanged.

## Second reading by R3

1. Compared the item against the repository with diff and checked its theorem
   signature byte for byte. Verdict: unchanged. The existing docstring and both
   public imports are unchanged; no definition or other existing module is edited,
   and no change record is required. The only new local helper is private and proved.

2. Compiled all four delivered modules in import order using lcompile.py; no errors
   or warnings. Checked every declaration with #print axioms in scratch copies.
   The private power_factor uses only propext, Classical.choice and Quot.sound;
   the original theorem and three listed deferred theorems additionally use
   sorryAx, as expected. There are exactly three named theorem holes, each with
   the entire proof `by sorry`; no forbidden declarations or hollow definitions.
   The chosen lifts of 1 are unique by the bijective inclusions. Power factors
   are unique by monicity of the lower-power inclusion. The carrier is obtained
   only within a theorem proof, with no arbitrary witness installed as a definition.
   Verdict: valid reduction, not a completed proof independent of the lower holes.

3. Read all three new signatures, docstrings and nodes. Independently checked the
   carrier against [Stacks 01YB](https://stacks.math.columbia.edu/tag/01YB) and the
   lifting argument against [01PM](https://stacks.math.columbia.edu/tag/01PM) and
   [01PQ](https://stacks.math.columbia.edu/tag/01PQ). The carrier removes stabilized
   ideal-power torsion using Artin-Rees; the comparison identifies two existing
   monomorphic ideal powers; the lifting theorem handles only a torsion-free
   target and returns evaluation at 1. None restates the whole item. Checked
   degree zero, zero and unit ideals, nilpotent ideals with empty complement,
   the empty scheme and zero module. On a nilpotent-ideal affine, the lifting
   hypothesis forces the target to vanish; the carrier may be zero if U is empty.
   Repeated LeanFinder searches with the queries “Artin Rees remove ideal torsion
   from finite type subsheaf while preserving restriction on complement”,
   “monomorphic ideal inclusions with equal stalk ranges induce isomorphism of
   sheaves ideal powers”, and “sections over D(I) as direct limit Hom(I^n,M) with
   no I power torsion”. Also used Loogle (Ideal, Submodule.annihilator), Mathlib
   grep (pow.*range|range.*pow|ArtinRees in AlgebraicGeometry), and project rg
   searches for torsion, annihilators and power comparisons. Matches were affine
   algebra tools or localization, not these statements. Existing quotient lifting
   and sections comparison are more general but have the reported import cycle.
   No lower hole has a short existing proof usable here. Verdict: true, sourced,
   needed, strictly separate parts of the argument; one-to-three decomposition.

4. Read the original DAG plan and used declarations from the top down. The proof
   genuinely combines carrier, complement, finite type, lifting and comparison,
   then proves the scalar identity on every smaller open by injectivity, linearity
   and naturality. All remaining direct imports supply a signature or a named
   declaration used by the proof. Replaced the unnecessary Coherent import of
   the new lifting module with the narrower Mathlib import and recompiled.
   The report now lists every removed original import and all seven old
   proof_deps no longer used directly. The unit sk-thm-picard-coherence has empty
   realized statement/step arrays, and its route is not replaced. Checked the
   actual source import closure with sandbox overlays, rather than relying on
   compiled dependencies. Verdict: pruned and cycle-free; no unit bypass.

5. Checked each node's verbatim lean.statement against its module, the parent's
   proof/proof_deps against the actual proof, and each new node's source, proof,
   searches, status, creation, blueprint, chapter, unit and Lean record. The lower
   nodes record their deferred mathematical routes; the parent records exactly
   its six direct proof dependencies. Verdict: DAG and Lean agree.

Changes by this reading: removed the new lifting module's unnecessary Coherent
import and narrowed its quasi-separatedness import; completed the original-import pruning list in this report; added this
independent review and its search/axiom evidence. No theorem statement or proof
body changed. The original hole is closed conditionally on the three lower holes;
net holes closed minus added is -2, with no whole-library pruning claimed.
