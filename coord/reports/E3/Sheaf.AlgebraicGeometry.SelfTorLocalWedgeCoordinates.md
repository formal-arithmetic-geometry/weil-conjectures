## What changed

The original statement of `AlgebraicGeometry.exists_local_wedge_selfTor_coordinates`
is unchanged. Its proof now uses normalized agreement on ideal-unit wedges, local
conormal wedge generation, naturality and span induction. All work is in the sandbox.

Added `Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates`, containing one remaining
hole for the coordinate construction and agreement only on wedges of actual ideal
sections on the whole smaller affine chart. This retains the original quotient-resolution,
conormal and exterior-restriction dependencies as proof imports.

Added `Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan`, fully proved using
`affine_conormal_sections`, `range_toModulesι_app`, the existing affine basic-open
localization lemma and exterior multilinearity. Every local wedge becomes, on one basic
neighbourhood, a scalar multiple of a wedge of restricted ideal-unit images. There is no
finite-generation or regularity hypothesis. The existing conormal-sections and affine
localization nodes are used as generic affine module tools; they do not replace any step
of the Picard-duality unit route. The unit records and chapter route are untouched.

Private, proved helpers in the original module transport generator equality by naturality
and extend it by span induction. The generator type is supplied explicitly to avoid
expensive inference through the tensor-pullback and derived-tensor definitions. No
definition, existing signature or visibility changed. The node records follow this route.

## Proved and sorry left

Closed the one original textual hole:
`AlgebraicGeometry.exists_local_wedge_selfTor_coordinates`
(node `new-h3-self-tor-local-wedge-coordinates`). Its proof from the intermediate statements
is complete.

Fully proved the new theorem `AlgebraicGeometry.conormal_wedge_mem_span_locally`
(node `new-e3-conormal-wedge-local-span`), including surjectivity of the chart unit,
localization denominators, inversion of those denominators, restriction of exterior
sections, and the exterior multilinear scalar formula. Its new module has no `sorry`.

Added exactly one hole, the entire proof of
`AlgebraicGeometry.exists_ideal_wedge_selfTor_coordinates`
(node `new-e3-self-tor-ideal-wedge-coordinates`). It asserts only agreement on wedges of
unit images of actual ideal sections on an affine chart. It leaves the resolution and
normalization construction, not the arbitrary-section lifting and multilinearity argument.

This is a decomposition: one upper hole closed and one strictly smaller lower hole added,
so net textual holes closed minus holes added is zero. The lower statement has no arbitrary
subopen, arbitrary local conormal tuple, or pointwise local lifting conclusion. Existing
holes in imported modules are untouched. No hole occurs in a definition or private helper.

## No longer needed

None. No original imports were removed and no original planned node or module is declared
pruned. The original coordinate-construction dependencies remain needed under the
ideal-wedge theorem. The rejected arbitrary-coordinate compatibility and coordinate-data
files remain outside the delivered `lean/` tree, in the earlier attempt's scratch archive.

## Where the brief, the DAG or earlier work was wrong

The earlier compatibility theorem was false: it quantified over arbitrary coordinate
isomorphism families, allowing independent automorphism twists. The replacement theorem
chooses its coordinates jointly with agreement on ideal-unit wedges. The proved span
argument then uses those same coordinates; it never asserts compatibility for arbitrary
families.

The original proof plan's local lifting step is implementable from the existing affine
conormal and basic-open localization interfaces. A single basic neighbourhood of the
closed affine chart works for all entries of the finite tuple. The powers may differ by
entry; their inverses are multiplied in the exterior multilinear formula.

Edge cases checked in the Lean construction: `n=0` uses the empty tuple and product one;
an empty W has no point satisfying the hypotheses; a zero conormal module gives the
zero positive-degree wedge; no regularity, finite generation of the ideal or Koszul
acyclicity is used. The remaining normalized-coordinate statement uses the quotient unit
in degree zero and is vacuous on empty closed charts.

## New nodes

`new-e3-self-tor-ideal-wedge-coordinates` records the remaining, restricted normalization
step in `Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates`. Its source is the parent's
Tags 09PQ, 01R3 and 06YH argument, stopped before lifting arbitrary conormal sections.
Its docstring contains the quotient-resolution construction and localized Koszul-cycle
comparison proof. The three recorded search kinds are actual msearch calls; LeanSearch
was unavailable and the successful semantic and source searches found no exact theorem.

`new-e3-conormal-wedge-local-span` records the fully proved local-generation step in
`Sheaf.AlgebraicGeometry.ConormalWedgeLocalSpan`. Its source is Tag 01R3, the canonical
unit of Tag 0096, and the upstream affine basic-open localization lemma. Its proof uses
existing nodes for those precise interfaces. The three recorded search kinds are actual
msearch calls; no blueprint statement with this precise local generator formula was found.

No change record is needed: there are no changes to existing definitions, statements or
interfaces and no forced adaptations. The unused-variable linter is scoped off for the
original theorem only, to retain its existing inner quantified `hx` binder unchanged; all
new declarations compile with the normal lint settings.


## Second reading by E3

1. **Interface preservation: pass.** Compared the original module with the repository
   using `diff`, and compared its theorem signature byte for byte. The existing signature,
   visibility and docstring are unchanged; only proof imports, proved private helpers,
   the scoped unused-variable linter setting and the proof body were added. No existing
   definition changed. The existing node differs only in `proof`, `proof_deps` and
   `proof_origin`. There are no forced adaptations or applicable open change records.
2. **Kernel checks: pass, with the reported remaining hole.** Compiled all three delivered
   modules with `lcompile.py --all`, without errors or warnings. Scratch-copy
   `#print axioms` checks cover all three public theorems and all six private helpers.
   `conormal_wedge_mem_span_locally` and every helper use only `propext`,
   `Classical.choice` and `Quot.sound`. The original theorem and the ideal-wedge theorem
   additionally use `sorryAx`, precisely because the latter's proof remains open.
   The sole delivered `sorry` is that named public theorem. There is no forbidden
   declaration or holed definition. The adjunction choice is pinned to the canonical
   sectionwise unit formula by its theorem; coordinates from the remaining existence
   theorem are destructured only in a proof and never used to define data.
3. **Split-off statement: pass.** Read the ideal-wedge theorem, its complete docstring
   argument, its node, the normalized algebraic comparison and the three construction
   interfaces. Checked Stacks Tags 09PQ, 01R3 and 06YH against their cited uses. The
   statement chooses coordinates jointly and tests only actual ideal-section tuples;
   it does not claim compatibility for independently twisted coordinates. In degree
   zero normalization gives the quotient unit; zero ideals and empty closed charts
   cause no contradiction; nonregular ideals require no Koszul acyclicity. This leaves
   the resolution/normalization construction and removes the arbitrary local-section
   lifting step, a real part of the argument which is now proved. New semantic search
   used “Functorial map from wedge powers of I modulo I squared to Tor of the quotient
   ring compatible with restriction of affine schemes”; new source search used
   `koszul.*natur|natur.*koszul|Tor.*baseChange`. A Loogle search for “Tor” was too broad
   to help. Repository and upstream searches found no usable exact existing theorem;
   the stronger nested-coordinate result depends on this item and cannot be imported.
   The remaining construction cannot be closed by a short application of the existing
   interfaces.
4. **Reduction and pruning: pass.** Traced local generation from chart-unit surjectivity,
   a basic neighbourhood, one denominator power per entry, and inversion of the basic
   function. The finite product scalar formula gives span membership, including the
   empty product for n=0. Naturality transports agreement to that neighbourhood and
   span induction extends it. This is a genuine reduction, not merely renaming and
   applying the original statement. Existing restriction helpers with the same formula
   are private, so importing their modules would not shorten the proof. Every public
   import in the new modules is needed by their signatures; proof-only imports are
   plain imports. The old construction dependencies remain needed transitively under
   the ideal-wedge node, so none is pruned. Read the Picard-duality unit record: its
   statement, steps and `realized` fields are unchanged and no unit route is bypassed.
5. **DAG agreement: pass.** Checked each stored Lean statement verbatim against its
   module and checked that `proof_deps` is exactly the union of the proof steps' `uses`.
   The original node records generator agreement, local span generation and naturality;
   the new span node records the actual affine conormal/localization/exterior proof;
   the ideal-wedge node records the remaining construction. Both new nodes carry the
   required source, searches, creation, blueprint, chapter, unit and Lean fields.

Second reading changed only this report: added the independent review and removed the
obsolete sentence saying the second-reading section was absent. No Lean or node repair
was necessary. This remains one original hole closed, one lower hole added, net zero;
the local-generation theorem itself and the reduction helpers are axiom-clean.
