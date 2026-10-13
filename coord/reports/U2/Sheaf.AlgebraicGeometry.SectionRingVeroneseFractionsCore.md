## What changed

Repaired reviewer X-b1b7d's H4 return. In
`lean/Sheaf/AlgebraicGeometry/SectionRingVeroneseFractionsCore.lean`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` now uses
`exact ⟨sectionRingVeroneseFractionEquiv X L d s⟩` from the existing
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula` module.
The theorem's signature, visibility, namespace, universe, original docstring,
and three public imports are unchanged. The module docstring describes reuse.

Removed the entire private helper/context block and the proof-only `import all`
of `InvertibleSectionRing`. Replaced the proof-only fraction-map import with
`SectionRingVeroneseFractionsFormula`; removed `DirectSum` from the open list.
The item's node now has the reviewer's single reuse step and sole proof dependency
`lem-sc-section-ring-veronese-fractions-formula`. Its proof origin records reuse
and the inherited kernel hole. Removed the unnecessary change record
`coord/changes/section-ring-veronese-core-private-context.md`.
No other module, definition, or statement is adapted; no new node is introduced.

## Proved and sorry left

Closed the one local hole in
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core`
(node `lem-sc-section-ring-veronese-fractions-core`) by using the existing
constructed equivalence. One of one local holes closed; zero holes added;
zero statements split off. No direct sorry remains in the delivered module.

The proof inherits the unresolved existing theorem
`AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseFractionMap_kernel`
(node `lem-sc-section-ring-veronese-fraction-kernel`, module
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel`). This delivery does
not prove that kernel theorem. The core is proved relative to this existing hole,
not an axiom-complete result. The equivalence has explicit quotient-map data;
its inverse is determined by the kernel equality and proved surjectivity.

The repaired module compiles without warnings through `lcompile.py`.
A fresh scratch axiom audit of the core theorem, the constructed equivalence,
and the kernel theorem reports `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`. The inherited `sorryAx` is from precisely the existing kernel hole;
the previous report's assertion of only permitted axioms is superseded.

## No longer needed

Removed direct proof-only imports
`import all Sheaf.AlgebraicGeometry.InvertibleSectionRing` and
`import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionMap`.
The latter module and node `def-sc-section-ring-veronese-fraction-map` remain
transitive dependencies of the reused equivalence, so they are not globally
pruned. The former module remains publicly imported for the statement.
All three original public imports remain necessary for the statement's types.

Removed every private declaration in the old helper/context block:
`veroneseNumeratorRing`, `sectionRingVeroneseSummand`, `sectionRingVeroneseSum`,
`tensorPowMulIso_add_inv`, `numerator_formula`, `unitor_transition`,
`sectionRingVeroneseNumerator_transition`, `summand_transition`,
`veroneseFraction_transition`, `raise_to`, `common_denominator`,
`relations_le_kernel`, and `sectionRingVeroneseSum_kernel`.
Their local tensor-coherence, common-denominator, and kernel proof steps are
unnecessary here. The existing fraction-map kernel statement and formula node
remain needed. No existing library module or node becomes unreachable solely
because of this replacement, and no new auxiliary module is delivered.

## Where the brief, the DAG or earlier work was wrong

H4 identified a duplicate kernel statement: after unfolding
`sectionRingVeroneseSum`, the deleted private kernel theorem was the symmetric
form of the existing `sectionRingVeroneseFractionMap_kernel`. The existing
`sectionRingVeroneseFractionEquiv` already has exactly the required equivalence
type. Reconstructing these facts was unnecessary. The node now describes direct
reuse, rather than a second construction and kernel calculation.

The earlier report and second reading incorrectly claimed an axiom-complete
proof. Their old validation text is replaced here with the actual inherited
kernel-hole audit. The unit `sk-thm-curveestimate` is realized by
`thm-sc-proper-cohomology` and has no realized proof steps; this helper reuse
preserves the unit route. There is no interface change or forced adaptation.

## Earlier second reading (a previous round; superseded)

Repair addendum superseding the prior second-reading claims, following reviewer
X-b1b7d's explicit H4 instructions. The duplicate kernel statement and all its
private supporting declarations are removed. The core now reuses the existing
constructed equivalence with the unchanged signature and public imports.
The DAG has exactly the reviewer-requested reuse step and formula dependency.
The private-context change record is removed.

The repair worker compiled the replacement and a fresh axiom audit. The audit
includes `sorryAx` inherited from the existing unresolved
`AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseFractionMap_kernel`.
No new hole or auxiliary statement is introduced, and no unit step is bypassed.
This addendum records the repair and its checks; it does not claim a new
independent second reading. The dispatcher-appointed second reader must verify
the repaired delivery before pushing it.

## Second reading by U2

Independent dispatcher-appointed second reader, 2026-10-13:

1. PASS. Compared the sole delivered Lean module with the repository using
   `diff -u`. The existing theorem signature, docstring, visibility, namespace,
   universe, and three public imports are byte-for-byte unchanged. Only headers,
   a module docstring, the plain proof import, and the proof body are added.
   There are no delivered definitions, new declarations, or change records.
2. PASS with an inherited hole. Independently compiled the module without errors
   or warnings through `lcompile.py`. Compiled the scratch copy with fresh
   `#print axioms` checks of the core, equivalence, and kernel theorem: each has
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The delivered
   module has no `sorry` or forbidden declaration. The existing equivalence uses
   the explicit fraction map and its unique inverse, rather than an arbitrary
   witness from an unproved existence theorem. Its existing kernel hole remains
   unresolved; this is not an axiom-complete proof.
3. PASS. No statements are split off and no holes are added. Read the reused
   equivalence and the inherited kernel theorem. The latter is a strictly lower
   kernel calculation for a fixed map, with a complete proof docstring, including
   empty support, degree zero, and zero or nilpotent denominator cases. No new
   duplicate statement needs searching or closing in this delivery.
4. PASS. The single existing equivalence is the immediate witness of the exact
   requested type. A fresh `rg` search in both Lean roots confirms its existing
   definition and use by `SectionRingVeroneseFractions`; reconstruction here
   would duplicate that construction. The proof-only import is plain `import`.
   All original public imports supply statement types. The repository node's old
   `proof_deps` is empty, so no old dependency was omitted from the pruning report.
   No module is globally pruned. Read `dag/units/sk-thm-curveestimate.json`:
   its realized statement is `thm-sc-proper-cohomology` and its steps are empty;
   this helper reuse bypasses no realized unit step.
5. PASS. Compared the node JSON against the repository. Only `proof`,
   `proof_deps`, and `proof_origin` change. They record exactly the witness used
   by Lean, the formula node that owns its definition, and the inherited kernel
   hole. The statement, statement dependencies, and Lean record are unchanged.

Second reading changed only this report by adding the independent checks above.
No Lean or DAG repair was needed. One local hole is closed relative to the
existing kernel hole; zero holes are added and zero statements are split off.
