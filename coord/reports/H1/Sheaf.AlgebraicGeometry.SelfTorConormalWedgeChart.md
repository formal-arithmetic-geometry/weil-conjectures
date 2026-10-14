## What changed

`SelfTorConormalWedgeChart.lean` closes the existing theorem body by obtaining a
linear section equivalence with a pure-wedge equation, extending that explicit
equivalence to the chart sheaves, and rewriting the terminal component. The
existing theorem signature and all definitions are unchanged.

Two new modules isolate the affine linear section calculation and its extension
to module sheaves. All added proof imports are plain imports. The direct imports
of `AffineConormalSections` and `ExteriorSheafRestrictIso` were removed from the
parent and retained as planned inputs of the new intermediate modules.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart`.

Holes added and still open:
- `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_section_equiv`, node
  `new-t2-self-tor-conormal-wedge-chart-section-equiv`.
- `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections`, node
  `new-t2-self-tor-conormal-wedge-chart-from-sections`.

This is a decomposition: one old hole closed and two new holes added, net -1.
The target is not axiom-clean: it still depends on `sorryAx`. Neither split
contains data definitions, and each remaining hole is exactly a named public
theorem with a source and complete natural-language proof in its docstring.
No existing holed declaration was weakened or changed.

## No longer needed

The parent no longer directly imports
`Sheaf.AlgebraicGeometry.AffineConormalSections` or
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`. Its old direct
proof dependencies `lem-weil-pbc-affine-conormal-sections`,
`lem-sc-exterior-sheaf-restrict-iso`, and `new-t2-self-tor-affine-section` have
been replaced by the two split nodes. All three remain needed below those nodes
or in statement dependencies; no whole module is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The submitted section equivalence was only additive. Additivity and the
pure-wedge equation do not justify extension to an O-module sheaf map. In degree
zero, for example, an additive automorphism of Q[t] that swaps t and t^2 and fixes
all other monomials fixes the empty-wedge unit but is not Q[t]-linear. Thus the
submitted transport argument did not establish scalar compatibility of its
arbitrarily chosen additive equivalence. The repair requires linearity over the
actual chart section ring and passes the equivalence explicitly, eliminating
the `Classical.choose h` term from the transport statement.

The earlier docstrings contained only proof summaries. They now describe the
quotient scalar action, localization, exterior sheafification, affine model
comparison, unit equation, and extension of the inverse. The transport no longer
assumes the pure-wedge equation; only the parent uses it.

## New nodes

`new-t2-self-tor-conormal-wedge-chart-section-equiv` records the chart-ring-linear
section calculation and its pure-wedge formula. It is a section-module result,
with no sheaf isomorphism in its conclusion.

`new-t2-self-tor-conormal-wedge-chart-from-sections` records extension of an
explicit chart-ring-linear equivalence to a module-sheaf isomorphism agreeing
on every section. It uses no pure-wedge normalization hypothesis. Both node
records are in `dag/nodes/sec-picard-framework/` with new modules under
`lean/Sheaf/AlgebraicGeometry/`. No change record is needed: all altered split
signatures are new in this delivery, and the existing interface is unchanged.

## Second reading by H1

1. Compared every delivered module with the read-only repository. Only the
   parent module already exists. Its theorem signature is byte-for-byte
   identical, and no existing definition or public import changed. The other
   two modules and their nodes are new.
2. All three files compile through `lcompile.py`. The two remaining sorries
   occur only in the named split theorems listed above; there are no forbidden
   declarations or hollow definitions. Scratch-copy `#print axioms` checks
   for all three theorems show only the permitted standard axioms and `sorryAx`
   from open statements.
3. Repaired the insufficient additive hypothesis to a linear equivalence over
   Gamma(Z,i-inverse-image U), and made the transport input explicit. Tested
   degree zero, identity/zero ideal, empty chart, zero quotient, and nonregular
   ideals mathematically: the construction uses localization and exterior
   universal properties, with no regularity or finiteness assumption. Read
   Stacks [01R3](https://stacks.math.columbia.edu/tag/01R3),
   [0096](https://stacks.math.columbia.edu/tag/0096), and
   [01I6](https://stacks.math.columbia.edu/tag/01I6). Repeated searches with
   different terms using leanfinder, loogle, msearch grep, and rg on the local
   library. Found affine Hom lifting/extensionality in
   `WeilConjectures.AlgebraicGeometry.Modules.AffineHom`; these require the
   chart quasi-coherence comparison, which is not already available for this
   arbitrary exterior conormal sheaf. Neither split merely renames the parent:
   one calculates section modules, the other extends a supplied linear map.
4. The existing affine conormal calculation remains an input; the parent now
   contains only the two reduction steps it uses. The removed direct imports
   and all old direct proof dependencies are accounted for above. The unit is
   `sk-thm-picard-duality`; its `realized` record currently has empty statement
   and step lists. This node realizes none of those entries, and the unit's
   route and record are unchanged. No whole module was pruned.
5. Checked the parent and both new nodes against the Lean: declaration names,
   verbatim statement records, module paths, source, creation fields, searches,
   proof steps, proof dependencies, and origins agree. Updated the parent's
   proof origin to H1 and the split nodes to the repaired linear statements.

Second reading changed: scalar compatibility and explicit transport parameter;
expanded both docstring proofs and sources; removed redundant parent imports;
corrected node statements, dependency plans, proof origin, and decomposition
accounting. No additional split hole could be closed in the short review pass.
