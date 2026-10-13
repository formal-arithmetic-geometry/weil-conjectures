## What changed

Preserved the original signature of `AlgebraicGeometry.koszulRegularImmersion_extSheaf`
byte for byte. Its proof splits on the sign of q and uses two sibling modules.
The negative branch is now proved using an ordinary injective resolution concentrated
in degrees >= 0, `derivedInternalHom_obj_iso`, `homComplex_single_iso`, and
`DerivedCategory.isZero_of_isGE`. Unfolding `locallyRankedExteriorTerm` gives the
zero object on the other side; additive pushforward preserves it. Regularity and the
rank equality are unnecessary in this branch and were removed from the new negative
lemma. The nonnegative affine determinant comparison remains open.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.koszulRegularImmersion_extSheaf`.
New hole added: `AlgebraicGeometry.koszulRegularImmersion_extSheaf_nonnegative`, node
`lem-sc-koszul-regular-immersion-ext-sheaf-nonnegative`.
The proposed negative hole `AlgebraicGeometry.koszulRegularImmersion_extSheaf_negative`
is now closed, with node `lem-sc-koszul-regular-immersion-ext-sheaf-negative`.
This is a partial proof/decomposition: one original hole replaced by one strictly
nonnegative-degree hole, net zero direct holes removed. The negative-degree calculation
is formalized; the global nonnegative Koszul calculation is not claimed as proved.
Existing imported foundational statements can still contribute `sorryAx` transitively.
No new data construction or definition is introduced.

## No longer needed

The parent no longer directly imports `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`,
`Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect`,
`Sheaf.Paper.DerivedInternalHomRestrictOpen`,
`Sheaf.RingTheory.KoszulRegularSequenceDualComplex`, or
`Sheaf.RingTheory.KoszulConormalBasis`. Their nodes are no longer direct parent
proof dependencies; all five remain in the nonnegative comparison's proof plan and
import closure, so none is claimed globally pruned. The negative module needs none
of these five imports. A duplicate HomologySequence import was removed from the
nonnegative module. No unit step or unit dependency was bypassed.

## Where the brief, the DAG or earlier work was wrong

The initial report claimed two helpers in the same module, but they were separate
modules. Its new node statements were not self-contained, its helper proof descriptions
were incomplete, and it omitted the parent's changed proof dependencies. Its degree
split added two holes for one original hole without proving either calculation.
The second reader proved negative vanishing, strengthened that new lemma by removing
unneeded hypotheses, completed the nonnegative docstring, and repaired all three nodes.
The result is explicitly reported as a partial proof, not a completed Ext calculation.

## New nodes

`lem-sc-koszul-regular-immersion-ext-sheaf-negative`: the negative-degree comparison,
proved without immersion, regularity, or conormal-rank assumptions. Its proof node
records the K-injective representative computation, degreewise Hom comparison,
and identification of two zero objects.

`lem-sc-koszul-regular-immersion-ext-sheaf-nonnegative`: precisely the parent's
comparison in nonnegative degree, with all original geometric and rank hypotheses.
Its full proof plan is the affine Koszul computation and intrinsic localization/gluing
argument of [Stacks Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ).
No change record is needed: no existing declaration's signature or definition changed.

## Second reading by R4

1. Compared all delivered Lean modules with the repository. The sole existing
   declaration retains its exact signature and docstring; only its proof and private
   proof imports changed. New helper signatures agree with their node records.
2. Compiled all three modules through lcompile.py in import order. The sole explicit
   sorry is the whole proof of the named nonnegative theorem. No axiom, unsafe,
   opaque, implemented_by, extern, hollow definition, or arbitrary data witness is added.
   Explicit #print axioms checks allow only the three standard axioms and sorryAx
   from the remaining nonnegative theorem or existing foundational obligations.
3. Checked negative q (including -1), q=0, the zero-length regular sequence,
   rank-zero strata, and empty Z. Negative vanishing is independent of regularity;
   the nonnegative statement is exactly the corresponding degree range of the original.
   Reviewed all five existing proof-dependency statements. Searched with LeanFinder,
   Loogle and rg/msearch grep using injective-resolution, connectivity, sheaf Ext,
   and conormal-determinant terminology. LeanSearch returned Internal Server Error,
   recorded as unavailable. Used the existing HomComplexSingle computation in the
   negative proof. AffineRHomQuasiCoherent needs additional Noetherian hypotheses,
   and FiniteLocallyFreeDerivedHom needs a locally free source, so neither closes
   the nonnegative comparison. No identical new helper was found.
4. Proved the easy degree range rather than retaining its new sorry. Removed the
   five unused direct parent proof imports and the corresponding imports from the
   negative module; retained them for the still-open nonnegative calculation.
   Read dag/units/sk-thm-picard-duality.json: its realized arrays are empty and
   unchanged; the existing unit route and affine Koszul route remain intact.
5. Replaced the vague new node statements with self-contained statements. Updated
   their signatures, proof steps, proof_deps, searches and proof_origin. Added the
   parent node update describing the actual sign split and its two dependencies.

Changes made during this reading: proved negative vanishing; removed its unnecessary
hypotheses and imports; completed the remaining helper's proof docstring; corrected
node records, pruning claims, and the report's progress accounting.
