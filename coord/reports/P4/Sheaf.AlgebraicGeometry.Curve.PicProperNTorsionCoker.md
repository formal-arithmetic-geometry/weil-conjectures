## What changed

Retire AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker and retain its
complete proof as local hc in AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion.
The surviving parent signature is unchanged. Replace its proof-only import of
PicProperNTorsionCoker with plain imports of PicardDecomposition and
Mathlib.Algebra.Group.TypeTags.Hom. The retired module is a declaration-free
stub with public meta import Mathlib.Lean.Linter for the maintainer's command
probe. Update the two existing DAG records to reflect the inlined proof.

Change record: coord/changes/pic_proper_ntorsion_coker.md.

## Proved and sorry left

Zero holes closed out of zero; zero holes added; zero statements split off.
The baseline assigned module was already sorry-free. This is repair and
pruning, not a new proof or decomposition. The complete proof of
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion is retained, including the
cokernel calculation formerly named pic_proper_ntorsion_coker. Neither delivered
module contains a sorry. Inherited unproved geometric dependencies remain;
the parent depends transitively on sorryAx, which this delivery does not add.

## No longer needed

The parent no longer imports Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker.
It was the retired module's sole direct caller/importer. The cokernel node
lem-sc-pic-proper-ntorsion-coker remains realized by the parent's second
conjunct, formally .2.1. The parent's proof_deps drops this retired component
and cites torsion, decomposition and divisibility directly.

The retired file removes these public imports:

- Mathlib.AlgebraicGeometry.Morphisms.Proper
- Mathlib.AlgebraicGeometry.Morphisms.Smooth
- Mathlib.FieldTheory.IsAlgClosed.Basic
- Mathlib.GroupTheory.QuotientGroup.Basic
- WeilConjectures.AlgebraicGeometry.Curve
- WeilConjectures.AlgebraicGeometry.Picard.Group

It removes these proof imports:

- Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
- Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv
- Mathlib.Algebra.Group.TypeTags.Hom

The parent's mathematical inputs remain directly imported. No other mathematical
module is pruned. The stub's meta import supports verification commands.

## Where the brief, the DAG or earlier work was wrong

The latest return in coord/returns/P4.md, dated 2026-10-14 10:02 UTC (reviewer
X-9f2f7), rejects the unrelated collision repairs as outside the supplied
forced-adaptation scope. This reading follows its exact repair: withdraw
ExternalCupUnitCoefficientIdentities, PicardTensorFrameCoordinates,
PicardTensorFrameRestrictionNormalized, SchemeTensorShiftBinaryLocalizationSquare,
SchemeTensorShiftLocalizationNormalization and ModuleCupNaiveDerivedCompatibility
from the delivery, and remove coord/changes/picard-probe-name-collisions.md.
The original versions of those modules remain unchanged in the delivered library.
The earlier report and review claiming all eight files passed are superseded.

The parent original fails against the retired stub because it still calls
pic_proper_ntorsion_coker. This caller adaptation is forced and retained.
The unrelated inherited imported-probe name collisions require separate
interface-repair deliveries as the return directs; this delivery does not claim
to repair them or to pass an ordinary imported parent probe.

## Forced adaptations

Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion is the only adapted module.
Its original proof calls the removed pic_proper_ntorsion_coker constant;
against the stub it fails with Unknown constant
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker. The adaptation replaces
that call with the unchanged original calculation, indented inside local hc,
and replaces the retired proof import with the calculation's proof imports.
Its theorem signature, visibility and docstring remain byte-for-byte unchanged.

## Second reading by P4

1. **Visible interfaces: PASS after scope repair.** Compared both retained Lean
   files with the supplied checkout. The surviving parent theorem's signature,
   visibility and docstring are byte-for-byte identical. Its proof-only imports
   change as recorded. The sole removed declaration is the disclosed standalone
   pic_proper_ntorsion_coker; its assertion remains the parent's .2.1 conjunct.
   Withdrew all six unrelated collision-repair modules and their change record
   exactly as reviewer X-9f2f7 requested in the latest return. Those modules have
   no source changes in this delivery. No target signature or definition changes.

2. **Proof and axioms: PASS.** Independently recompiled the narrowed two-file set
   using lcompile.py --all: parent 3.1 s, stub 0.5 s, no errors or warnings.
   Compared the full original cokernel proof with local hc: identical tokens,
   differing only in indentation. Read the argument: divisibility gives roots
   in P0, integer cast proves the coordinate map surjective, the two kernel
   inclusions identify the power image, and the quotient first-isomorphism
   theorem gives the required equivalence. A scratch copy prints the parent's
   axioms as propext, Classical.choice, Quot.sound and inherited sorryAx.
   The isolated ordinary imported stub probe reports SHEAF-PROBED with zero
   declarations. Neither delivered source has a sorry or prohibited declaration;
   neither introduces data or chooses an arbitrary witness in a definition.
   Zero holes closed, zero added, zero split off.

3. **Split statements and small cases: PASS.** No new statement or split-off hole.
   At n=1 the root can be L and the cokernel is trivial. The nonzero cast excludes
   n=0; genus zero does not affect the cokernel calculation. Repeated leanfinder
   search for a product with an n-divisible factor finds general quotient and
   divisibility APIs, not a shorter proper-curve theorem. Loogle verifies the
   first-isomorphism API; rg checks integer-cast divisibility and the library's
   Picard quotient declarations. The existing decomposition and divisibility
   theorems provide precisely the subgroup equality and roots the proof uses.

4. **Route, imports and pruning: PASS.** The parent replaces its old cokernel
   dependency by its existing decomposition/divisibility inputs; both additional
   mathematical imports are plain proof imports. The report lists all nine
   removed imports of the retired module. An overlay source scan finds no
   remaining importer or caller of the retired declaration. The unit record
   sk-thm-curveestimate and its realized statement/steps are unchanged.
   The two unchanged direct parent importers were verified byte-for-byte against
   the checkout and compiled against the narrowed overlay: ConstantInvariance
   46.5 s and WeilConjectures.AlgebraicGeometry.Curve.Estimate 5.4 s, both clean.
   Compiling the original parent against this overlay reproduces Unknown constant
   AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker at line 70; the retained
   adaptation is therefore forced. The unrelated inherited ordinary-import
   collisions are explicitly outside this delivery following the latest return;
   this review does not claim they have been fixed.

5. **DAG agreement: PASS.** Read both node records against their originals and
   the proof. The parent proof_deps names torsion, decomposition and divisibility,
   exactly the geometric inputs used. The cokernel node keeps its original
   statement and proof dependencies and points to the parent's .2.1 conjunct.
   Its lean.statement records the unchanged parent signature. Only lean, proof,
   proof_deps and proof_origin fields change across the two records; no new nodes,
   altered unit route or weakened statement.

**Second-reader changes:** withdrew six unrelated Lean edits and
coord/changes/picard-probe-name-collisions.md; rewrote the report and amended the
remaining change record to remove the superseded collision-repair claims and
record the latest return accurately. The retained cokernel proof and node edits
needed no mathematical repair. This is one-module pruning with net zero holes.
