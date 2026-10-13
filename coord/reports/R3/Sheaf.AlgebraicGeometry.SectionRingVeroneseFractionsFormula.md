## What changed

Repaired reviewer X-9f6b3's C3/E5 point 4 by constructing the canonical equivalence.
`SectionRingVeroneseFractionMap.lean` explicitly defines the tensor-power numerator
isomorphism, its reverse graded injection, the additive same-denominator fraction
map, and its direct-sum extension. Additivity, cancellation on homogeneous
components, and surjectivity are proved in Lean.

`SectionRingVeroneseFractionKernel.lean` states the remaining kernel equality for
this fixed map, with a complete construction-based common-denominator proof in
its docstring. It is one strict part of the quotient argument and has its own node.
It is not a new generator formula or a repackaged equivalence-existence assertion.

`SectionRingVeroneseFractionsFormula.lean` defines
`sectionRingVeroneseFractionEquiv` as the inverse of the explicit quotient
isomorphism furnished by `QuotientAddGroup.liftEquiv`. The only inverse chosen is
the unique inverse of that fixed bijective map. No arbitrary existence witness is
used, and no definition contains `sorry`. The equality hypothesis is exactly the
replacement requested by the reviewer; the displayed generator conclusion is
unchanged. Its proof evaluates the quotient map on the generator, cancels the
numerator isomorphism and graded injection, and uses the inverse law.

The formula module replaces its public Core import by a public Kernel import.
The kernel proof must be public because the exposed equivalence definition refers
to it; the map is available through the kernel module's public import. No unused
proof imports are added. The original caller receives only its forced one-line
witness adaptation. The formula's node signature and construction route, the
caller's node proof route, and both new nodes match the delivered Lean.

Change record: `coord/changes/sectionRing_veronese_fraction_formula.md`.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_formula`.
The formula has a complete Lean proof and no direct `sorry`.

Added one strictly simpler hole:
`AlgebraicGeometry.Scheme.Modules.sectionRingVeroneseFractionMap_kernel`, in
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel`, node
`lem-sc-section-ring-veronese-fraction-kernel`. Its whole proof is `:= by sorry`.
It identifies the kernel of an explicitly constructed map with the fraction
relation subgroup; its docstring gives both inclusions, including scalar closure,
finite support, transition coherence, and the localization equality criterion.

Also proved:
`sectionRingVeroneseNumerator_cancel` and
`sectionRingVeroneseFractionMap_surjective`; the additive law fields of
`sectionRingVeroneseHomogeneousFraction` are proved. All constructions are real
terms, and every postponed obligation is a named theorem. The adapted caller
`exists_sectionRing_veronese_fraction_equiv` retains a complete proof and precisely
its old signature. All four delivered modules compile without warnings.

Accounting: one upper hole closed and one lower hole added, hence a decomposition,
not a net reduction in holes. The formula and equivalence still depend on the
named kernel hole. The existing Core hole is untouched outside this delivery.

## No longer needed

Removed the formula module's public import of
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` and removed its node's
proof dependency `lem-sc-section-ring-veronese-fractions-core`. The core's bare
existence theorem is not used by the construction or formula. It is not claimed
as a wholly pruned library module: the adapted caller retains its original
proof-only Core import because only forced lines may change in that unheld module.

No unit statement or realized step is bypassed. The rejected chosen-formula
module/node from the earlier attempt remains absent. There are no other old
proof-dependency nodes or modules to prune from the delivered argument.
The second reader removed the unused direct public import of
`Sheaf.AlgebraicGeometry.SectionFractionPresentation` from the map module and
placed it in the kernel module, where its relation definition is needed. The
presentation remains in the import closure; this is import cleanup, not a pruned module.

## Where the brief, the DAG or earlier work was wrong

The old formula depended on an arbitrary choice from `Nonempty (A ≃+ B)`;
that assertion determines no generator images. The reviewer correctly rejected
its natural-language proof. The repaired construction fixes the quotient map
before inverting it. The inverse is determined by bijectivity, exactly the
unique-inverse exception allowed by AGENTS.md section 5.

The existing formula node's equality hypothesis is changed as explicitly requested
by the reviewer. Its generator conclusion is verbatim unchanged. The existing
caller's mathematical statement and every target statement are unchanged. Its
old DAG proof route did not record the formula it actually used; its route now
directly records the formula node. The formula has no old DAG citers in this
checkout, so its statement-change record has an empty old-citer list.

Edge cases checked before stating the kernel lemma: `d=0` still indexes numerator
summands by denominator powers; `s=0` or nilpotent makes both quotient presentations
zero through a killing transition. The finite-support kernel proof works for
arbitrary schemes and uses no compactness. For an empty numerator family, the
kernel inclusion is immediate. Local trivializations are used only to verify
coherence identities, which glue without needing a uniform exponent on a cover.
The exponent killing a numerator comes from the global algebraic localization,
not from gluing local vanishing. Thus no omitted compactness or nonzero-divisor
assumption is needed.

The cited Stacks fraction construction and common-denominator reasoning support
the kernel computation; the remaining proof in Lean is tensor-power coherence
and finite-support transition bookkeeping. The docstring states these steps
explicitly instead of assuming a formula for Classical.choice.

## New nodes

`def-sc-section-ring-veronese-fraction-map` records the explicit additive direct-sum
map in `SectionRingVeroneseFractionMap.lean`, its component definitions, and the
proved cancellation and surjectivity lemmas. No holes are in this module.

`lem-sc-section-ring-veronese-fraction-kernel` records the exact remaining kernel
equality, in its own module. Its natural-language proof gives scalar closure of
the transition relations and the converse finite-support common-denominator
argument. It carries the same source, chapter, unit, and ancestor as the item.
Both new nodes have three kinds of search recorded; LeanSearch was unavailable.
The second reader moved the SectionFractionPresentation import from the map module
to the kernel module, the first new module whose signature actually uses it.

Change record: `coord/changes/sectionRing_veronese_fraction_formula.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` is unclaimed in this
checkout. Against the changed dependencies its original line 61 fails:

```text
Application type mismatch: The argument rfl has type ?m.115 = ?m.115
but is expected to have type e = sectionRingVeroneseFractionEquiv X L d s
in the application sectionRing_veronese_fraction_formula X L d s e rfl
```

Only line 60 changes from
`let e := Classical.choice (sectionRing_veronese_fraction_core X L d s)` to
`let e := sectionRingVeroneseFractionEquiv X L d s`. This is required by the
repaired formula's equality hypothesis. The complete adapted module compiles.
Every existing signature, visibility, import, and other proof line of this caller
is unchanged. The independent reader can compile the original against the changed
dependencies to reproduce the failure and then compile the delivered adaptation.

## Second reading by R3

1. **Visible declarations and forced adaptation: pass.** Read the unified diffs of
   both existing modules. The formula's only existing signature change is `he`,
   from equality with the unconstrained core choice to equality with the explicitly
   constructed equivalence. This is declared in the change record; all parameters
   and the entire generator conclusion are unchanged. The adapted existence theorem
   has exactly its repository signature and visibility, and only its witness line
   changes. The delivery tool also confirmed that the original caller compiles against
   the baseline, fails against the delivered dependencies, and the adapted caller
   compiles. No target or target-used definition changes. The change record now quotes
   the old and new signatures verbatim, including line breaks.

2. **Proof and constructions: pass with the declared kernel hole.** Compiled the four
   modules in import order. Read every construction and both cancellation/surjectivity
   proofs. The numerator isomorphism is composed from exponent equality, the recursive
   tensor-power isomorphism, and the inverse unitor. The summand map uses actual
   localization fractions; its additive fields are proved. The direct-sum extension
   is explicit. `liftEquiv` descends this fixed map and its inverse is uniquely
   determined. There is no arbitrary witness from an existence theorem, no hole in
   data, and no forbidden declaration. A scratch probe printed axioms for all ten
   delivered declarations: the first six use only `propext`, `Classical.choice`,
   `Quot.sound`; the kernel theorem, quotient inverse, formula and adapted existence
   theorem additionally use `sorryAx`. The only direct hole is the named kernel
   theorem, exactly as reported. This is one hole closed and one added: decomposition.

3. **Remaining statement and mathematical proof: pass.** Read the kernel module and
   its node, the definitions of the submodule span and tensor transitions, and the
   section-ring product. In a local generator of L, the recursive exponent and
   tensor-power maps preserve generator powers. Thus the inverse numerator transport
   sends a transition to multiplication by `s^b`, and degree-zero multiplication to
   scalar multiplication. This kills the entire submodule span, not just its listed
   generators. For the reverse inclusion finite support permits one common N; the
   global ring localization criterion supplies k killing the resulting numerator,
   hence its transition to N+k. The defining relation then kills the single summand.
   This checks both inclusions without compactness or a regular denominator.
   Checked d=0, b=0, n=0, empty support, zero/nilpotent s, and the empty scheme:
   the same identities hold (zero localization and zero quotient in the degenerate
   cases). This kernel equality is a strict intermediate statement, not the formula
   or existence theorem renamed. Read Stacks properties.tex, equation module-invert-s,
   lemma-invert-s-sections (01PW), and lemma-ample-immersion-into-proj (01Q1), fetched
   into scratchpad because literature is not installed here. The QC/QS hypotheses of
   01PW concern the geometric restriction isomorphism, which this purely algebraic
   argument does not invoke. Independent LeanFinder query about kernels generated by
   transition differences returned localized-module kernel lemmas, not this kernel
   equality; Loogle `Localization.mk_eq_zero` reported unknown identifier. Grep of
   Mathlib and both Lean roots found localization equality criteria and private
   normal-form/power lemmas, but no already-stated equality for this explicit map.
   Closing the remaining hole needs tensor-transition coherence and finite-support
   bookkeeping, rather than a few-line application of any search result.

4. **Route and pruning: pass after import cleanup.** The formula proof evaluates the
   fixed quotient map on its generator, invokes proved numerator cancellation, and
   uses the inverse law. It does not assume a generator formula. The old sole proof
   dependency, the bare Core existence node, is listed as no longer needed. The caller's
   unused proof-only Core import stays because its adaptation is restricted to forced
   lines; Core is therefore not claimed wholly pruned. Moved the unused presentation
   import out of the new map module and into the kernel module that needs it.
   Other public imports supply signature or exposed-definition dependencies; no
   proof-only import has been made public. Read sk-thm-curveestimate.realized:
   statement thm-sc-proper-cohomology, no realized steps. This algebraic reduction
   bypasses neither that statement nor any realized unit step.

5. **Nodes and records: pass after literal-signature cleanup.** Read all four node
   files. The map node lists the six actual constructions and proved facts; the kernel
   node states exactly the additive-subgroup equality and records both inclusions.
   Formula proof_deps names the map and kernel nodes; the adapted existence node
   names the formula node, as its Lean body does. Their proof origins cite the checked
   Stacks construction. New nodes have source, searches, created, blueprint, chapter,
   unit and Lean records. Filled their empty same_as lists and explicit unavailable
   search verdicts, and made the three new/changed Lean statement records verbatim from the declaration
   keyword (the tool records `def`, omitting the `noncomputable` modifier).
   Existing nodes differ only in permitted proof/Lean fields and the declared formula
   statement-change fields; unchanged fields and the unit record are preserved.

Second reading changed: import placement, verbatim signature records and change-record
quotations, new-node blueprint/search metadata, and this review. No Lean proof body or
mathematical statement was changed by the second reader.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions
Original against changed dependencies failed:
```
/tmp/forced-adaptation-6qf6jk6q/lean/Sheaf/AlgebraicGeometry/SectionRingVeroneseFractions.lean:61:60: error: Application type mismatch: The argument
  rfl
has type
  ?m.115 = ?m.115
but is expected to have type
  e = sectionRingVeroneseFractionEquiv X L d s
in the application
  sectionRing_veronese_fraction_formula X L d s e rfl

(with the modules compiled into /tmp/forced-adaptation-6qf6jk6q/.lbuild) [2.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
