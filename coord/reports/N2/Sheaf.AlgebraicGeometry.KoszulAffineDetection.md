## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.KoszulAffineDetection` with a
complete Lean reduction. The statement, binders, universes and public imports are
unchanged. Two proved private helpers handle localization-universe transport: one
uses the existing affine generator criterion, and one extracts the existing Koszul
triangles in standard localizations and transports them through the canonical
triangulated equivalence. The main proof identifies both encodings of termwise tilde
by a natural isomorphism, factors each eventually killed map through a shifted
Koszul complex by triangle exactness, uses diagonal positive-exponent orthogonality
to kill that factor, and then applies affine zero detection.

Added proof imports `Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase`,
`Sheaf.AlgebraicGeometry.KoszulSupportedAugmentationVanishing` and
`Mathlib.CategoryTheory.Localization.HomEquiv`. The new module states only the
filtered-colimit eventual-vanishing step, without an orthogonality hypothesis.
Updated the existing node's proof, proof_deps and proof_origin to follow this proof.
No existing statement or definition changed; no adaptations or change records.

Validation: both delivered modules compile through the prescribed launcher. The
unit `sk-thm-picard-duality` and its realized steps are unchanged. Sources were
checked at https://stacks.math.columbia.edu/tag/09IR,
https://stacks.math.columbia.edu/tag/08DC and
https://stacks.math.columbia.edu/tag/08DD because the literature files are not
present in this clone. Search results supplied no shorter exact theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.isZero_of_koszul_powers_orthogonal`, node
`lem-pc-koszul-affine-detection`. Its complete Lean body uses the existing
`affine_perfect_open_represent_cohomology` and `perfectGeneration_affine_base`
statements, plus the new intermediate statement below.

Added and still sorry:
`AlgebraicGeometry.koszul_supported_augmentation_eventually_zero`, node
`lem-pc-koszul-supported-augmentation-vanishing`, in its own new module. It asserts
that a map from a shifted structure object into a supported quasi-coherent derived
object is killed by some shifted Koszul augmentation. It does not assume
orthogonality and does not conclude that the object is zero. The original theorem's
orthogonality is used separately, in the proved triangle-factorization argument.
This is a strict intermediate step, not a restatement of detection.

There are no sorries remaining in the assigned module and no sorries in either
private helper. One original hole is closed and one lower hole added: this is a
decomposition, with net hole change zero, not a claim of a sorry-free dependency
closure. Existing dependency holes are unchanged.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`. Its result is now used
through the existing affine generator criterion
`Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase`, node
`lem-pc-perfect-generation-affine-base`; hence
`lem-pc-affine-qcoh-derived-equivalence` is removed only from this node's immediate
proof_deps. It is still needed transitively by both the affine generator criterion
and represent-cohomology, so no whole-library or target-closure pruning of that
module is claimed.

Retained `Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology`: the private
triangle helper uses it directly. Every added proof import is needed by the
completed reduction. No other prior import, node or module is pruned. The original
argument's explicit identification of every global cohomology group with a colimit
is replaced by the strictly weaker eventual-zero assertion and triangle exactness.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan remains valid. Its original Lean interface assumptions no
longer line up: `affine_perfect_open_represent_cohomology` and
`perfectGeneration_affine_base` require localizations in the same universe on every
open, whereas this item assumes only the localization over U. The cohomology
comparison additionally restricts via `Scheme.Modules.overEquiv` to U.toScheme.
The private helpers solve the universe mismatch for triangles and affine detection
by choosing standard localizations and transporting back, without modifying any
signature. The remaining intermediate's docstring explains the corresponding
restriction transport needed for the colimit step.

The power index in `KoszulOpenSystem` is e with exponent e+1. The main proof uses
that positive diagonal tuple explicitly. Mathlib shifts triangles with a factor
(-1)^n on the first two arrows; the zero-precomposition hypothesis is transported
through this sign before applying exactness. The transported `koszulOpenTilde`
functor is not definitionally the same functor as the hypothesis's Mathlib tilde;
a termwise natural isomorphism is used instead of assuming definitional equality.
No mathematical false statement or tool failure was found.

## New nodes

`lem-pc-koszul-supported-augmentation-vanishing` is the filtered-colimit portion of
steps 1–2 of the original argument. Its source is Stacks Tags 08DC and 08DD, as used
in the supported-object reduction of Tag 09IR. The proof in words records shifting,
the restriction-zero image in the canonical colimit, filtered-colimit equality at
a later index, augmentation compatibility, and localization-universe transport.
It passes the empty family, zero ring and zero target checks. Its public theorem
has exactly `:= by sorry`, no data construction and no orthogonality assumption.
LeanSearch was unavailable; LeanFinder found only ordinary section-vanishing and
generic derived results; library and Mathlib grep and blueprint searches found no
exact existing statement. Its chapter and unit are inherited from the assigned
item. There are no change records.


## Second reading by N2

1. **Visible declarations: PASS.** Compared the assigned module with the repository
   using `diff`, and separately compared the original theorem signature as raw
   text through `:= by`: byte-for-byte identical, including universes, instance
   binders, hypotheses, conclusion and visibility. The original public imports
   are unchanged. Only proofs, proof imports and the existing theorem's proof
   documentation changed; the two helpers are private proved theorems. The
   additional public statement is in its own new module. No definition, existing
   signature, target or change record is altered by this delivery.
2. **Proof and axioms: PASS, with the reported dependency holes.** Compiled both
   modules in import order using `lcompile.py --all`: no errors or warnings.
   The assigned module has zero sorry tokens; the additional module has exactly
   the one reported named theorem hole. A scratch copy with `#print axioms` for
   both private helpers, the original theorem and the new intermediate reports
   only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. Checked that no
   forbidden declaration or implementation escape is present. The representative
   complexes chosen by `Q.objPreimage` occur inside proofs, not in an exported
   data definition; their images are explicitly identified with E by isomorphisms.
   The natural isomorphism between the two tilde functors and the triangle-shift
   sign are handled explicitly, so no false definitional identification is used.
3. **Split statement: PASS.** Read the whole new assertion and its proof docstring,
   the existing comparison theorem and the Koszul tail construction. The new
   assertion is strictly the supported-map eventual-vanishing part: it neither
   assumes orthogonality nor concludes IsZero E. In particular, nonzero supported
   objects are permitted. Checked r=0 (all positive exterior powers vanish and
   the tail is zero), A the zero ring, E=0, all f_i=0 (positive transition powers
   annihilate the tail), and a unit among the f_i (U=X forces E=0). No added
   regularity or nonemptiness premise is needed. Independently checked Stacks
   [08DC](https://stacks.math.columbia.edu/tag/08DC),
   [08DD](https://stacks.math.columbia.edu/tag/08DD) and
   [09IR](https://stacks.math.columbia.edu/tag/09IR).
   The comparison cocone and filtered-colimit equality provide exactly the proof
   described. Independent LeanFinder search for annihilation of a supported
   derived cohomology class found only generic derived-category lemmas. Loogle
   found the generic `Types.FilteredColimit.isColimit_eq_iff`, and Mathlib grep
   also found its same-index variant; neither supplies localization/shift
   transport or the Koszul specialization. Repository searches for Koszul
   augmentation maps and their Hom diagram found the existing comparison and
   system, but no matching supported-map theorem. Closing the remaining hole
   requires restriction and shift transport across localization equivalences;
   this is not a few-minute completion. One closed hole and one added hole remain
   a decomposition, net zero.
4. **Route and pruning: PASS.** Read the proof from detection down through its
   two helpers and the intermediate. It first uses the existing affine generator
   criterion and represent-cohomology statement, then Mathlib localization
   equivalences and triangle exactness. The diagonal exponent e+1 satisfies the
   positive-exponent hypothesis. The old immediate proof dependency
   `lem-pc-affine-qcoh-derived-equivalence` is the only removed node and is fully
   listed under No longer needed; it remains transitively used, so no closure
   pruning is claimed. All added imports are private proof imports (the new
   hole's imports record its intended comparison and filtered-colimit proof).
   The unit sk-thm-picard-duality and its realized field are unchanged; this is
   a reduction below unit level using the same affine-comparison route.
5. **DAG consistency: PASS.** The existing node changes only proof, proof_deps
   and proof_origin. For each delivered node, the union of proof-step uses equals
   proof_deps. The main node records precisely eventual vanishing, triangle
   factorization and affine unit detection. The new node has its independent
   statement, statement dependencies, source, full proof in words, search
   record, split status, creator/item/group/date, blueprint ancestry, inherited
   chapter and unit, and verbatim Lean statement record. Its dependency is the
   existing represent-cohomology node. No duplicated detection theorem is hidden
   behind the new name.

Second reading changed only this report: added the independent checks, searches,
edge cases and explicit verdicts. No Lean or node repair was needed.
