## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.ideal_power_torsionFree_section_lifting`
with a complete proof. The existing affine quotient-lifting theorem is specialized
to the zero annihilator, constructed as the free module on the empty type. Its
cokernel projection is inverted, so the affine lifts take values in F itself.
A finite affine cover supplies a common degree; compatibility of r with the monic
power inclusions preserves evaluation. Torsion-free restriction injectivity gives
agreement immediately on overlaps, and existing sheaf morphism descent glues the maps.

Added `Sheaf.AlgebraicGeometry.IdealPowerTorsionFreeSectionRestriction` with the fully
proved theorem `AlgebraicGeometry.Scheme.ideal_power_torsionFree_section_restriction`.
It uses affine localization, finite generation, and the proved affine-power section
helper from CoherentSupportVanishingIdealNilpotence. These are proof-only imports;
all existing signatures and public imports are unchanged. No definition changed.
Updated both DAG proof records to describe the actual proof. The unit's realized
statement and steps are untouched.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.ideal_power_torsionFree_section_lifting`
(node `lem-pc-ideal-power-torsion-free-section-lifting`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.ideal_power_torsionFree_section_restriction`
(node `lem-pc-ideal-power-torsion-free-section-restriction`).

There are no sorries in either delivered module; zero holes were added or split off.
The proof uses the existing stated theorem
`AlgebraicGeometry.Scheme.ideal_power_quotient_affine_lifting_section`, whose import closure
still contributes sorryAx in the compiled baseline. Its existing node and module remain dependencies;
no copy or additional hole was created. This is a proof from existing declarations,
not a claim that the complete target import closure is now axiom-free.

## No longer needed

No existing imports were removed: all three public imports support the unchanged
statement. The old node had no proof-dependency imports or proof_deps to remove.

The finite-cover-of-overlaps and eventual-degree-enlargement portions of the old
plan are unnecessary: torsion-free restriction injectivity gives agreement at the
first common degree. This proof does not need
`Sheaf.AlgebraicGeometry.IdealPowerLocalMapsEventuallyAgree`
(`lem-weil-pbc-ideal-power-local-maps-eventually-agree`),
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero`
(`lem-weil-pbc-ideal-power-evaluation-eventually-zero`),
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero`
(`lem-weil-pbc-ideal-power-evaluation-affine-eventually-zero`), or
`Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection`
(`lem-weil-pbc-ideal-power-quotient-local-lifting-section`).
No statement about their necessity for other targets is intended.
The FormalPolynomialPowerLifts module is also unnecessary: the two monicity and
section injectivity helpers are proved locally by induction and categorical
monicity. Quasi-separatedness is retained in the existing signature but is not
needed by this torsion-free gluing argument.

## Where the brief, the DAG or earlier work was wrong

The original plan bundled the complete affine denominator construction and gluing
into one elementary step with no proof dependencies. The affine step already has
a suitable stated declaration, and the gluing argument can avoid eventual vanishing
because the target is torsion-free. No statement was found false or changed.

Importing the global quotient-lifting, eventual-agreement, or FormalPolynomialPowerLifts
modules would create cycles. Import-direction checks permitted the affine quotient
lifting and the two proved affine helper modules used here. The compiled affine
quotient-lifting module was initially missing; it appeared in the next green snapshot,
and the final proof compiled against it without creating a duplicate statement.

Sources were checked at https://stacks.math.columbia.edu/tag/01PM and
https://stacks.math.columbia.edu/tag/01PQ. LeanSearch was unavailable; LeanFinder,
Loogle, source grep, and blueprint searches found no matching restriction theorem.
The empty scheme, empty open, zero ideal, unit ideal, and degree zero are included
in the proof: no nonemptiness or positivity assumption was added.

## New nodes

`lem-pc-ideal-power-torsion-free-section-restriction`, in
`dag/nodes/sec-picard-framework/lem-pc-ideal-power-torsion-free-section-restriction.json`,
records the fully proved injectivity lemma for F(W) -> F(W intersect U), without
compactness assumptions. The proof uses no existence-selected unproved data.
The affine quotient lifting and sheaf descent are generic local construction tools
from the proper-base-change chapter, rather than replacements for the Picard unit's
route. No change record is needed because no existing interface changed.


## Second reading by H3

1. Compared the lifting module with the repository version and checked the full
   existing theorem signature byte for byte: identical. Public imports and existing
   declaration visibility are identical. No definition or statement changed, and no
   change record is required. The additional restriction theorem is in its own module.
2. Read both proofs and compiled the restriction and lifting modules locally. Neither
   delivered source contains sorry, axiom, unsafe, opaque, implemented_by or extern,
   or a hollow definition. A scratch #print axioms check gives only propext,
   Classical.choice and Quot.sound for the restriction theorem. The lifting theorem
   additionally has sorryAx through existing dependencies, as reported above. Its
   zero module is constructed explicitly; choice of local lifts is inside the theorem
   proof, with no existence-selected data definition added.
3. There are no split-off holes. The new, fully proved restriction theorem is a
   strictly smaller overlap-agreement result, with source, complete proof docstring
   and matching node. Checked empty scheme/open, zero ideal, unit ideal and degree
   zero: the local annihilation and separation arguments still apply. Independent
   LeanFinder search for supported sections killed by powers, Loogle search for
   Ideal.FG and Ideal.radical, and source grep found no duplicate sheaf theorem.
   Loogle recovered exists_pow_le_of_le_radical_of_fg, which the proof already uses.
4. Reviewed the top-down zero-annihilator reduction, finite affine degree maximum,
   torsion-free overlap agreement and sheaf descent. All proof-only imports are
   private imports. The original node has empty proof_deps, so no old dependency
   is omitted from No longer needed. The Picard unit realized record is untouched;
   this replaces only a below-unit argument. No new module is actually pruned from
   the original import closure; the report lists unused alternative plan modules.
5. Checked both node proofs, proof_deps and proof_origin against the declarations
   used. Both Lean statement records match their source signatures. The new node
   has the required creation, source, blueprint, chapter/unit and search fields.

Changed the lifting theorem's stale natural-language proof to describe the actual
zero-annihilator specialization and immediate restriction-injectivity gluing,
without unnecessary finite overlap covers or a quasi-separatedness argument.
Updated the report's dependency caveat: the refreshed source now proves the affine
quotient theorem, but its compiled import closure still contributes sorryAx.
No proof, signature, definition or import changed in the second reading.
