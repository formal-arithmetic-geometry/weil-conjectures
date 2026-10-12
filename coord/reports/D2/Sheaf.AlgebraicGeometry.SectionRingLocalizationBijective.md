## What changed

In `Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective`, proved
`AlgebraicGeometry.Scheme.Modules.sectionRing_localization_bijective` from the existing
section-fraction equivalence, a new purely algebraic Veronese fraction identification,
and nonvanishing-section trivialization. The theorem's signature and visibility are unchanged.
The new imports are proof-only. Four private helpers construct the tensor-power isomorphism
and prove its compatibility with section-ring powers, including all dependent degree casts.
The comparison of the two maps and transfer of bijectivity are complete Lean proofs.

Added `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` and its node. Its sole theorem
identifies homogeneous localization with the existing section-fraction quotient and specifies
its value on every fraction. It has no open, restriction map, compactness, quasi-separatedness,
positive-degree, or comparison-map hypothesis: it is strictly the algebraic identification
step, not a restatement of the bijectivity theorem. The node copies record the implemented route.

Both delivery modules compile without warnings using `lcompile.py --all`. The positive-degree
hypothesis is retained verbatim, although this proof only needs nonnegative degree.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.sectionRing_localization_bijective`
(node `lem-sc-section-ring-localization-bijective`). No sorry remains in the item module.
Its private `eqToHom_app_heq`, `ring_power_of`, and `veroneseIso_power` are proved;
`veroneseIso` is an explicit composite of existing isomorphisms, with no postponed data.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_veronese_fraction_equiv`,
in `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions`,
node `lem-sc-section-ring-veronese-fractions`. This is a decomposition: one upper hole
closed and one strictly algebraic lower hole added, so the net hole reduction is zero.
The remaining theorem's full source and proof are in its docstring and node.

The equivalence is characterized on every fraction representative, hence uniquely determined;
no arbitrary object is chosen from an unproved mere existence theorem. The main proof obtains
and combines the equivalences locally; it introduces no public data definition from them.

Edge cases checked mathematically: degree zero gives ordinary localization of global functions;
exponent zero uses the identity tensor power and left unitor; zero or nilpotent s makes both
fraction presentations zero by the transition relations. Empty schemes and empty nonvanishing
opens are admitted: free-generator cancellation is bijectivity between zero modules, and no
nonemptiness assumption is used. For a trivial line bundle on an affine scheme, the statement
reduces to the usual numerator-over-powers description of a ring localization. For positive d,
only degrees n*d occur, exactly as in the Veronese ring.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.InvertSCOhomology` and the proof
dependency `lem-sc-invert-s-cohomology`. This proof does not need cohomology fractions,
degree-zero cohomology identification, Mayer--Vietoris, or compact-open cohomology induction.
No other original import was removed: `InvertibleSectionRing`, `Ample`, and
`Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization` occur in the unchanged signature.
This is pruning of this item's proof route; other callers may still need the cohomology module.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan called the identification of the homogeneous-localization quotient with
tensor-power fractions elementary, but no declaration supplies that identification. It is now
an explicit algebraic subproblem with an exact numerator formula. The cohomology route is
unnecessary here because the existing section-fraction equivalence already supplies the needed
geometric comparison. The old theorem docstring is preserved and describes that original route;
the delivered DAG proof and the actual Lean proof give the shorter section-fraction route.

The unit record `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and has no
realized proof steps replaced by this change. The generic section-localization tool from the
Picard framework is used as a black box; the curve unit already cites Picard duality.
Nonvanishing-section trivialization is also used as a generic tool, as in the original route.

The local Stacks TeX is absent on this machine. Read the official online versions of
[01PW](https://stacks.math.columbia.edu/tag/01PW),
[0B5L](https://stacks.math.columbia.edu/tag/0B5L), and
[01Q1](https://stacks.math.columbia.edu/tag/01Q1).
The new proof origin is marked agent because the algebraic Veronese identification expands
an implicit identification in those sources rather than copying a separate stated lemma.
LeanSearch was unavailable (HTTP internal server error); LeanFinder, Loogle and local source
searches ran. No matching theorem or duplicate node was found.

## New nodes

`lem-sc-section-ring-veronese-fractions`:
`dag/nodes/sec-curve-estimates/lem-sc-section-ring-veronese-fractions.json`, with module
`lean/Sheaf/AlgebraicGeometry/SectionRingVeroneseFractions.lean` and declaration
`AlgebraicGeometry.Scheme.Modules.exists_sectionRing_veronese_fraction_equiv`.
Its three proof steps identify numerators and transition maps, descend the direct-sum map to
the quotient, and construct the inverse by homogeneous fraction representatives and common
denominators. No existing public interface or statement was changed; no change record is needed.

## Second reading by D2

1. Compared the delivered item module with the repository version. The theorem signature and all
existing declaration interfaces are unchanged; only proof-only imports, private proof helpers,
and the theorem proof differ. The added Veronese module is a new declaration with its own node.
Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors or
warnings. The item has no `sorry`, and the only remaining `sorry` is the named split theorem
`exists_sectionRing_veronese_fraction_equiv`. No forbidden axioms, unsafe declarations, or
hollow definitions were introduced. Verdict: pass, with the documented split hole.

3. Checked the split theorem against its edge cases and its formula on every homogeneous
fraction. It is a strictly smaller algebraic identification than the bijectivity target,
with no compactness, nonvanishing, or positive-degree assumptions, and its equivalence is
specified by the fraction formula. It is not a restatement of the target and no duplicate
library declaration was found. Verdict: pass.

4. Read the proof from the target downward. It uses the existing section-fraction comparison,
the new Veronese identification, tensor-power coherence, and nonvanishing-section
trivialization; the old cohomology import is removed. The private induction and cancellation
lemmas are the shortest local route for the required compatibility. Verdict: pass; the
cohomology route is pruned.

5. Checked the DAG proof steps, dependencies, proof origin, and the new node against the Lean
proof. The unit route is retained: the localization comparison remains the realized target,
and the new theorem only realizes its algebraic intermediate step. Verdict: pass.

I changed this report only by adding this second-reading record. No Lean statements or proofs
were changed during the second reading.
