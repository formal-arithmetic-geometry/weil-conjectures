## What changed

Reduced `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_root_presentation`
to the geometric construction of a localized root chart, stated in the new module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart`.
The original theorem's signature and visibility are unchanged. Its proof now proves
locality of the whole root algebra by uniqueness of its maximal ideal, identifies
its localization with the whole algebra, transports the local flat stalk map and
ideal equality, and proves irreducibility from the auxiliary DVR uniformizer identity.
The private algebra helper `root_local` is fully proved. The new geometric module is imported only for the proof. The second reading
removed redundant direct proof imports of `Mathlib.RingTheory.Ideal.GoingUp`
and `Mathlib.RingTheory.Localization.AtPrime.Basic`; their declarations are already
available through the retained imports. A declaration-local heartbeat budget matches that
used by the adjacent generic-factor module; it does not change other declarations.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_root_presentation`
(node `lem-sbc-stalk-normalization-trait-section-root-presentation`).
Added one hole, the whole proof of the public theorem
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_localized_root_chart`
(node `lem-sbc-stalk-normalization-trait-section-localized-root-chart`).
This is a decomposition, with one upper hole closed and one strictly geometric
hole added; net holes closed: zero. The whole-root-algebra locality, localization
isomorphism, local canonical map, transport of flatness and ideals, and uniformizer
irreducibility are proved here and absent from the remaining geometric statement.
There are no other sorries in the delivery, none in definitions, and no definitions
choosing existential chart witnesses.

## No longer needed

The redundant newly added direct imports `Mathlib.RingTheory.Ideal.GoingUp` and
`Mathlib.RingTheory.Localization.AtPrime.Basic` were removed by the second reading;
no module becomes unreachable as a result. No original imports were removed: they supply the unchanged statement's types and
instances. No named proof-dependency nodes or modules were pruned: the original
node had an empty proof-dependency list. The existing chart modules
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts`,
`Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts`, and
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor`
were examined and are not imported by this proof. The last is downstream of this
item and cannot be used to prove it. These modules remain needed by other branches.

## Where the brief, the DAG or earlier work was wrong

The original node had three non-elementary steps but no named proof dependencies.
The existing generic normalization chart declarations do not include the relation
between their common divisor equation f and the closed fibre. Their signatures
therefore cannot alone supply the transverse uniformizer conclusion. The new
geometric statement records the localization at the chosen root point, while the
original whole-root-algebra identification is now actually proved. The unit's
trait/tame-normalization/section route is retained. Stacks Tags 0EYH and 0EYI were
read from their official pages; the construction uses the preliminary chart and
section paragraphs of 0EYI, before its rational-point and splitting arguments.

## New nodes

`lem-sbc-stalk-normalization-trait-section-localized-root-chart`, in
`dag/nodes/sec-smooth-base-change/`, records the geometric chart selection and
transverse generic factor. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationTraitSectionLocalizedRootChart.lean`.
It supplies a localized stalk rather than a local whole root algebra, and a
maximal-ideal generator rather than an irreducibility proof. Positive exponents,
a maximal root prime, and a genuine auxiliary DVR exclude the zero-degree,
empty-fibre and field edge cases. No existing interface is changed and no forced
adaptation is needed; there is no change record.

## Second reading by U1

1. Compared the existing module and node against the repository with `diff`.
   The existing theorem signature is byte for byte unchanged, as is its
   visibility. Only its proof, a private proved helper, proof imports and a local
   elaboration budget were added. The existing node changes only `proof`,
   `proof_deps` and `proof_origin`. No target, definition or other module is altered.
   Verdict: pass; no change record is required.

2. Compiled both delivered modules through `lcompile.py --all` without errors or
   warnings, and recompiled the root-presentation module after import pruning.
   The scratch axiom audit checks `root_local`, the upper theorem and the new
   theorem. The helper has only standard axioms; the upper theorem also has
   `sorryAx` through the explicitly reported geometric hole. The sole syntactic
   `sorry` is the whole proof of the named localized-root-chart theorem. No
   forbidden declaration or hollow definition is present. Existential chart
   witnesses are eliminated only inside a proof of an existential proposition;
   no definition chooses data from this existence theorem. Verdict: pass as a
   decomposition, not a complete proof or net reduction in holes.

3. Read the new theorem and its docstring against Stacks
   [0EYH](https://stacks.math.columbia.edu/tag/0EYH) and
   [0EYI](https://stacks.math.columbia.edu/tag/0EYI). The chart can be chosen over
   the section point and a root factor selected over x. Localizing its base
   makes the root prime maximal by integrality. Pulling the same chart back to
   the section makes the divisor equation a uniformizer in an etale local DVR
   extension; its generic root factor embeds openly in the generic section
   fibre. The section's closed point is the reduced inverse image of the
   smooth special fibre, so the transversality hypothesis of 0EYI is satisfied.
   Checked e=1, f=0 in the algebraic helper, empty covers (no x), disconnected
   torsors (component stabilizers), and the excluded field and zero-degree
   cases. No rational point or splitting hypothesis is needed. The remaining
   theorem omits whole-root-algebra locality, the local canonical map and
   localization transport, all now proved in Lean, so it is strictly a part of
   the argument. Independent Lean Finder, Loogle and grep searches with
   different wording found no replacement. The existing trait-chart statements
   do not relate their f to the closed divisor or the section, and the generic
   factor theorem is downstream. Verdict: pass; the geometric hole cannot be
   closed by a short application of an existing theorem.

4. Read the reduction from the upper theorem downward. The finite integral
   algebra argument proves uniqueness of the root algebra's maximal ideal by
   polynomial decomposition; the localization equivalence transports flatness
   and the ideal identity; the DVR uniformizer lemma supplies irreducibility.
   Removed the two redundant newly added Mathlib imports and recompiled. All
   original proof dependencies are accounted for (the old list was empty).
   The unit `sk-prop-input-spreading` has empty `realized` entries; its stated
   trait, tame-normalization and section route is retained. Verdict: pass.

5. Checked both nodes' Lean statements verbatim against their modules. The
   upper node lists exactly the localized-root-chart dependency; its other
   steps match the actual algebraic proof. The new node has the source, full
   natural-language proof, searches, creation and blueprint provenance, unit,
   chapter and complete Lean record required by the brief. Verdict: pass.

Second reading changed only the two redundant direct proof imports, the
corresponding report descriptions, the new node's independent search records,
and this review section. No mathematical statement or proof body changed.
