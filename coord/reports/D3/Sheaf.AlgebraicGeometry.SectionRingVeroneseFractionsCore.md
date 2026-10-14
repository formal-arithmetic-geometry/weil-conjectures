## What changed

Reworked the proof of `sectionRing_veronese_fraction_core` in the assigned module. The
canonical quotient map is shown injective from the kernel equality and surjective by
choosing a homogeneous localization representative; the generator formula is isolated as
`hformula` and used to prove the explicit surjectivity witness. The public interface and
single import are unchanged.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is proved with no
`sorry`; no new declarations or holes were added. The baseline already has zero sorries, so this
delivery closes zero holes and splits off zero holes.

## No longer needed

No imports or modules pruned. The proof no longer calls
`sectionRingVeroneseFractionMap_surjective` or the generic quotient-lift surjectivity lemma:
it constructs the preimage directly using the generator formula. The map dependency node
still supplies numerator cancellation, and the kernel node is still needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked because its module was byte-for-byte unchanged, even though
the repair was already present. The baseline already satisfies #1428. This delivery reuses the canonical generator formula
to construct surjectivity witnesses directly while
preserving the repaired bijectivity statement and generator formula from review #1428.



## Second reading by D3

1. Interface preservation: compared the sole delivered Lean module with the repository
   using `diff -u`. Only the body of `sectionRing_veronese_fraction_core` changes.
   Its signature, the complete definition of `sectionRingVeroneseFractionCanonicalMap`,
   visibility, docstrings, and public import are byte-for-byte unchanged. No change record
   or forced adaptation is required. Read the landed canonical-map, generator-formula,
   and import change records; this delivery preserves those repairs.
2. Proof validity: compiled the delivered module locally with `lcompile.py`, with no
   errors or warnings. Inspected both declarations and the dependency modules
   `SectionRingVeroneseFractionKernel` and `SectionRingVeroneseFractionMap`. The map is
   an explicit quotient lift, not an arbitrary existence witness. The generator formula
   reduces that lift on a direct-sum summand and applies numerator cancellation.
   Injectivity applies `QuotientAddGroup.injective_lift_iff` to the kernel equality;
   surjectivity takes the transported numerator of a representative supplied by
   `HomogeneousLocalization.Away.mk_surjective`. No forbidden declarations or `sorry`
   occur. A scratch copy of the delivered proof reports exactly `propext`, `Classical.choice`,
   and `Quot.sound` for both declarations, with no `sorryAx`.
3. Split statements: none. There are no new declarations, new nodes, or holes to
   validate or search for duplicates. Checked the existing Mathlib representative lemma:
   its zero-power case explicitly uses the subsingleton localization, so zero and
   nilpotent denominators are covered. Degree zero and exponent zero require no extra
   hypothesis in any applied statement.
4. Route and pruning: read the imported numerator cancellation and surjectivity proofs
   and the Mathlib quotient-lift lemmas. The baseline's generic quotient-surjectivity
   route is shorter, but the delivered explicit witness is correct and reuses the
   generator formula already required by the conclusion; no rewrite is needed.
   The sole public import supplies data for the canonical-map definition as well as
   its well-definedness, so it is required and correctly public. Both old proof dependency
   nodes are still used; `## No longer needed` omits none. The unit
   `dag/units/sk-thm-curveestimate.json` realizes `thm-sc-proper-cohomology`, with no
   steps, and this local quotient computation bypasses no unit statement or step.
5. DAG agreement: compared the node JSON with the repository. Only `proof` and
   `proof_origin` change. The two proof steps describe the kernel-based injectivity,
   explicit preimage using the generator formula, and cancellation calculation actually
   written in Lean; their union equals the unchanged `proof_deps`. The recorded Lean
   statement matches the unchanged theorem signature. No new-node requirements apply.

Second reading changed only this report and refreshed the scratch axiom check to use
this delivery's proof rather than the baseline proof. No mathematical repairs were
needed. This is a repair delivery for listed review #1428, already repaired in the
baseline: zero holes closed, zero added, zero split off, zero modules pruned.
