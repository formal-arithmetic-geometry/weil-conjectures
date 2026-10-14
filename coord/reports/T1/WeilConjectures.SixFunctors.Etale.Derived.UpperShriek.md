## What changed

Corrected `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` in
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`: it is now an explicit theorem
requiring a uniform global upper-amplitude bound N for the actual derived lower
shriek. Its complete Lean proof uses Mathlib t-structure orthogonality and the
existing adjunction to obtain the lower bound n-N for a bounded-below input K.
Corrected `AlgebraicGeometry.Etale.hasBoundedBelowUpperShrieks` similarly: its
mapwise amplitude hypotheses are explicit, and its proof applies the individual
theorem. Neither false coefficient-only claim remains an automatic instance.
The bounded-below classes, fields, exceptional functor and adjunction are unchanged.
Removed the disputed-statement comment after replacing its false statement.

Corrected the coefficient-only claim in the pro-étale UpperShriek module docstring.
Adapted the unclaimed pro-étale UpperShriekComposition module to carry explicit
bounded-below hypotheses for f, g and f ≫ g where upper-shriek functors occur.
The lower-shriek statements precede these hypotheses and remain unchanged.
The unclaimed pro-étale ClosedImmersionUpperShriek unit theorem explicitly takes
the mapwise bounded-below hypothesis required to type its exceptional Hom
equivalence; its proof and the two fully-faithfulness instances are unchanged.
Removed the redundant direct public LinearFunctor import; it remains public
through LowerShriek → UpperLowerStar. No proof imports were added. The change record is
`coord/changes/etale-upper-shriek-global-amplitude.md`.

## Proved and sorry left

The item's single original textual hole in
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` is retired by the authorized
statement correction. The corrected theorem is proved with no direct sorry,
using `DerivedCategory.TStructure.t.isGE_iff_orthogonal`, `t.zero`, the actual
`rightDerivedUpperShriekAdjunction`, and `Adjunction.homAddEquiv_symm_zero`.
This does not prove the old false statement. It proves its true amplitude-bounded
replacement, recorded by `lem-etale-upper-shriek-bounded-below-from-amplitude`.

The corrected `AlgebraicGeometry.Etale.hasBoundedBelowUpperShrieks` is also proved,
recorded by `lem-etale-upper-shrieks-bounded-below-from-amplitude`. No new holes are
added, no intermediate statement is split off, and no sorry remains in the item
or any of the three adapted modules.
The earlier `isLeftAdjoint_rightDerivedLowerShriek` proof is retained and uses
the existing imported proper-adjoint existence infrastructure. That dependency
was further proved by another group while this session ran; this delivery does
not claim to have proved it or checked its full transitive axiom closure.
The correction adds no hole to any adapted module and leaves its existing holes
untouched. No functor data are chosen from mere existence; eliminating the global
amplitude existential constructs only a proof of the Prop-valued class.

## No longer needed

Removed the redundant direct import
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`. The same module is
already publicly re-exported by UpperLowerStar, itself publicly re-exported by
LowerShriek, so this removes no public declaration. No DAG node or module on the
former adjoint-existence route is pruned. The false unconditional finite-coefficient
bounded-below instances are removed from typeclass inference, with their names
retained as explicit theorems. The new proof adds no geometric dimension theory,
compactification independence, Brown representability proof, or new lower lemma
beyond the existing left-adjoint declaration; its amplitude is an explicit input.
No blueprint unit statement or realized proof step is bypassed: `sk-prop-sf-cbc`
has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The original finite-coefficient bounded-below statement is false. The proper
morphism ⨿ₙ Pⁿ_C → ⨿ₙ Spec C, with coefficients F₂, has exceptional inverse image
of the constant degree-zero object in degree -2n on component n. Its image is not
globally bounded below. Finite coefficients give no uniform global amplitude
when fibre dimensions are unbounded. This is the counterexample already recorded
by the earlier B2 report; the launcher explicitly authorized the correction and
withdrew the instructions that had rolled it back to the false statement.

No existing primary DAG node was attached to the original bounded-below theorem;
the only primary attachment in the item records its different, already-reduced
left-adjoint existence theorem. The two new proved attachments record the corrected
statements and the original false claims in statement_change fields. No unrelated
Noetherian blueprint theorem is changed. The global class remains an explicit,
strong hypothesis over all compactifiable schemes; it is not inferred solely from
finiteness of a nonzero coefficient ring.

Edge cases: N=0 gives lower bound n, a positive bound gives n-N with the correct
sign, the zero ring has zero derived categories, and the empty-source case also
has zero exceptional image. The unbounded-dimension counterexample fails the new
uniform-amplitude hypothesis. The proof uses no quasi-compactness, Noetherianity,
constructibility, or coefficient-exponent invertibility that is absent from its
signature. LeanFinder found no exact theorem, Loogle found the orthogonality API,
and grep found orthogonality and the adjunction's zero-preservation API. LeanSearch
returned Internal Server Error; this is recorded as unavailable, not as no match.

## New nodes

`lem-etale-upper-shriek-bounded-below-from-amplitude` attaches the corrected,
proved individual theorem to the amplitude/orthogonality argument in the source
module. Its proof dependency is the already-existing left-adjoint declaration.
`lem-etale-upper-shrieks-bounded-below-from-amplitude` attaches the corrected,
proved mapwise constructor and depends on the individual theorem. Both nodes
have source, proof steps, actual search records, chapter/unit metadata and
statement_change records. They are attachments of proved declarations in the
item's existing module, not new modules or split-offs.

Change record: `coord/changes/etale-upper-shriek-global-amplitude.md`.

Validation: 20 focused modules compiled in import order through lcompile.py,
including the direct declaration-bearing importers, the étale orientation datum,
the pro-étale exceptional/duality callers and the full trace-formula caller set.
Every file passed without warnings. Unchanged test copies were removed from the
delivery; the four changed Lean modules are the item and the three adaptations.
The known pre-existing slow Smooth.Conventions importer was not changed.

## Forced adaptations

Both modules are unclaimed in the coordination snapshot, so their necessary
signature corrections are authorized by the launcher's unclaimed-module rule.

`WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition`: the original
fails at lines 195, 197 and 199 to synthesize the bounded-below instances for f,
g and f ≫ g, and at the later upper-shriek uses. Add these three explicit
hypotheses only after the lower-shriek statements and in the bounded-below
composition section. Move hf₂, hg₂, hfg₂ to the upper-shriek block and adjust the
one positional call to match. The three upper-shriek composition declarations
carry the hypotheses; the two lower-shriek composition declarations keep their
original types. The adapted module compiles without warnings.

`WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek`: the
original fails at line 95 to synthesize the bounded-below instance for i, which
is required by the exceptional Hom-equivalence in the theorem's type. Its proof
has the same failures at lines 98, 103, 107 and 110. Add the single explicit
instance binder at the unit-isomorphism theorem; the existing finite-coefficient
prerequisite is retained as an explicit binder to avoid an unused section-variable
warning. No other signature or proof is changed. There is no named caller of this theorem.

## Second reading by T1

1. **Interface and accidental changes.** I compared all four delivered modules with the
repository versions. Existing declarations retain their signatures except for the explicitly
recorded correction of the two false étale bounded-below claims and the forced hypotheses in the
two unclaimed pro-étale adaptations. The removed `LinearFunctor` import is re-exported through
`LowerShriek`, and the change record lists the affected modules. Verdict: passed.

2. **Proof validity.** I compiled all four modules with `lcompile.py --all`; the delivered files
contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
`debug.skipKernelTC` declarations. Scratch `#print axioms` checks show only the permitted axioms
plus `sorryAx` inherited from still-open upstream declarations. The amplitude proof uses the
stated orthogonality lemma, the existing lower-shriek adjunction, and the additive adjunction
equivalence; its bound is `n - N` with the correct integer arithmetic. The adapted
closed-immersion theorem and composition declarations compile with their explicit prerequisites.
The original adapted copies fail exactly with missing `HasBoundedBelowUpperShriek` instances at
the recorded lines, confirming that the adaptations are necessary. Verdict: passed.

3. **New statements.** I searched the library and recorded Mathlib searches for both new amplitude
statements. Neither theorem duplicates an existing declaration. The individual statement is
exactly the orthogonality consequence needed for the class; the global statement is its mapwise
constructor and constructs only proofs of propositions. The two DAG nodes include source, proof
steps, dependencies, metadata, and statement corrections. Verdict: passed.

4. **Route and pruning.** The proof follows the shortest available route through
`isGE_iff_orthogonal` and the existing adjunction, with no new geometric lemmas. The only removed
import is the redundant public `LinearFunctor` import; no old proof dependency or unit route is
bypassed. The three adapted modules contain only the forced typing changes described in the change
record. Verdict: passed.

5. **DAG agreement.** The node statements, declarations, proof steps, proof dependencies, and
proof origins match the Lean terms. Unit `sk-prop-sf-cbc` has no realized statement or proof steps,
so its route is unchanged. Verdict: passed.

No additional Lean or DAG changes were needed during this second reading.
