## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.bijective_powerSeries_punctured_globalSections`
with a compiling proof, preserving its signature and every public import.
The proof follows the original Tag 0EY9 route, with two explicit intermediate
interfaces: unique formal approximation along the punctured zero section,
and detection of sections by germs there. Neither intermediate asserts the
original bijectivity statement.

The main module proves the Krull-intersection step directly: the kernel of
any zero-section stalk map is proper since the target stalk is nontrivial;
Mathlib's local Krull intersection theorem annihilates a germ in all its powers.
The germ-detection lemma then annihilates the section. Uniqueness of formal
approximation proves injectivity, and existence plus the proved vanishing step
proves surjectivity. No inverse map or other data is defined by an unproved
existence statement.

Added modules `PowerSeriesPuncturedFormalApproximation` and
`PowerSeriesPuncturedGermDetection`, each with one named theorem and a complete
proof in words. Updated the item's proof-dependency record to match this route.
Read Stacks Tag 0EY9 online and the signatures of the existing Hartogs,
flatness, associated-prime base-change, depth-bound, and localization-detection
interfaces. LeanFinder and Loogle found no matching comparison theorem;
LeanSearch returned an HTTP 500, recorded as unavailable.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.bijective_powerSeries_punctured_globalSections`
(node `lem-sbc-power-series-punctured-global-sections`). No sorry remains in
the item's module. The local Krull-intersection argument and the final
injectivity/surjectivity assembly are complete Lean proofs.

Added two holes, exactly the following public theorems:

- `AlgebraicGeometry.Scheme.existsUnique_powerSeries_punctured_formal_approximation`
  (node `lem-sbc-power-series-punctured-formal-approximation`): reconstruction
  from restrictions modulo every power of the zero-section ideal, including
  uniqueness. This only compares infinitesimal germs, not sections on V.
- `AlgebraicGeometry.Scheme.eq_zero_of_powerSeries_punctured_germs`
  (node `lem-sbc-power-series-punctured-germ-detection`): the independent
  associated-point detection argument. Its premise is actual vanishing of
  germs; Krull intersection converting formal vanishing to that premise is
  proved in the item's module.

This is a decomposition: one hole closed, two added, net -1. It is not an
axiom-free completion of the mathematical result. All three delivered modules
compiled together without errors or warnings.

## No longer needed

Removed direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`
- `Sheaf.RingTheory.MvPowerSeriesFlat`
- `Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange`
- `Sheaf.RingTheory.DepthLeDimAssociatedPrime`
- `Sheaf.RingTheory.InjectivePiLocalizationAssociatedPrimes`

These five modules remain dependencies of the two smaller statements, so they
are not claimed as globally pruned. Their five DAG nodes are likewise retained
below those statements. `Mathlib.RingTheory.Filtration` is used directly, and
`Mathlib.RingTheory.MvPowerSeries.Equiv` supplies the Noetherian instance needed
for the stalkwise Krull argument. No node or module is globally pruned by this
delivery; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface change was found. The original plan's first
step does not follow by a direct application of the listed Hartogs theorem:
finite free truncation sheaves, their sections, and compatibility of the
truncations must also be assembled. Likewise its second step still needs the
scheme-level associated-point detection glue. The two new statements isolate
these missing pieces instead of relocating the original theorem.

Checked edge cases in the new statements: n=0 imposes no condition because
the zeroth ideal power is the whole ring; nilpotents in A are permitted and
are handled by associated primes, not reducedness. Local rings in this Lean
version are nontrivial, so a zero coefficient ring is excluded already by the
unchanged hypotheses. The depth bound excludes the maximal ideal from Ass(A)
and forces the punctured spectrum to be nonempty; no extra nonempty assumption
was added. Finite d is needed for Noetherianity and the finite monomial bases.
The formal approximation lemma does not assert equality on V, and germ
detection neither constructs nor chooses a power series.

The blueprint ancestor tool follows `created.item` as a node ID, but this
item's creation record contains a module name and therefore yields None. The
new nodes use the valid ancestor and via chain already recorded on the item:
`sbc-thm-spreading-finite-etale-galois`. A full blueprint keyword search found
no node stating either new intermediate result.

## New nodes

`lem-sbc-power-series-punctured-formal-approximation`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesPuncturedFormalApproximation.lean`,
is Tag 0EY9's inverse-limit calculation formulated through canonical stalk-map
kernels. Every object and quantifier is explicit; the uniquely determined
power series is only destructured inside a proposition proof.

`lem-sbc-power-series-punctured-germ-detection`, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PowerSeriesPuncturedGermDetection.lean`,
is the associated-prime and specialization part of the omitted injectivity
detail of Tag 0EY9. It retains the algebraic inputs of the original plan.
The existing Mathlib leaf nodes for power-series completeness, Noetherianity,
domain structure, and the canonical affine/Spec stalk localizations record
the corresponding tools used in the proof plans. No definitions, existing
signatures, or change records were added or changed.

## Second reading by G2

1. **Visible changes and statements.** Compared all delivered modules with the repository versions. The existing target theorem signature is byte-for-byte unchanged; imports were reduced only in the target module, and the two added theorem statements are recorded verbatim in their new DAG nodes. Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeded without errors or warnings. The target has no `sorry`; the only remaining sorries are the two named split-off theorems, each with a docstring and node. No forbidden declarations or hollow definitions were found. Verdict: pass, subject to the two declared open nodes.

3. **New statements.** Checked the formal-approximation and germ-detection premises on the edge cases described above (including n = 0 and nilpotents). They are strictly smaller than the target and do not restate bijectivity. Mathlib and repository searches in `searches.jsonl` found no existing equivalent declarations. Verdict: pass.

4. **Route and pruning.** The target proof uses the two split-off interfaces, local Krull intersection, and the finite-variable Noetherian instance. The unit route remains represented by the target node and its recorded ancestors. Five direct proof-only imports were removed from the target and retained where needed by the split-off modules; no additional node can be pruned by this delivery. Verdict: pass.

5. **DAG agreement.** Compared each theorem's declaration, proof dependencies, proof origin, module, and declaration fields with the Lean source and report. The target's proof dependencies match the calls in its proof, and each new node is marked `split` with source, blueprint, and Lean records. Verdict: pass.

I changed only this review record; no Lean source or DAG repair was needed.
