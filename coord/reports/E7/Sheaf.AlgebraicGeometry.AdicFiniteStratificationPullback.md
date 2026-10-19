## What changed

Retained and checked the earlier sandbox proofs, and completed the composition proof.
Changed Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback and the proof route
of lem-sfb-adic-finite-stratification-pullback (steps 5 and 7). Added a
proof-only import of WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf.
The coefficient isomorphism follows from uniqueness of left adjoints at a terminal
site object. The constant-module comparison is constructed by the two module
adjunctions, with scalar linearity checked on constants. Direct-image pasting uses
Mathlib pushforwardComp and pushforwardCongr₂. Constant-module composition follows
from the conjugate adjunction unit equation and the specified normalization on sections.
The constant-module comparison is invertible because precomposition induces a
bijection on maps into every module sheaf: the two sheafification adjunctions reduce
this to evaluation of constant presheaves at terminal objects. The scalar comparison
is restriction along the constant-section ring equation.
Existing public statements and definitions are unchanged; a fully proved private
constant-presheaf Hom equivalence supplies this proof.

## Proved and sorry left

Closed five of the six original holes, all in AlgebraicGeometry.Scheme:

- adicStratificationRingMap_isIso.
- adicStratificationConstantMap_existsUnique.
- adicStratificationConstantMap_isIso.
- adicStratificationPushforwardComp_existsUnique.
- adicStratificationConstantMap_comp.

One original hole remains, attached to
lem-sfb-adic-finite-stratification-pullback:

- AlgebraicGeometry.Scheme.adic_finite_stratification_pullback.

No holes are added, and none are split off. The module compiles through lcompile.py
without warnings. A full-file axiom check confirms that each of these five theorems
uses exactly propext, Classical.choice and Quot.sound, with no sorryAx.

## No longer needed

Removed the following proof-only imports, unused by the five completed proofs:

- WeilConjectures.ConstructibleSheaf.Pullback.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- Mathlib.AlgebraicGeometry.Morphisms.Immersion.
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures.
- Sheaf.Paper.LocalizeRingedSiteMorphism.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification.
- Sheaf.CategoryTheory.ConstantLeftModuleInverseImage.
- Sheaf.Paper.LocalizeRingedSiteMorphismGeneral.
- Sheaf.SixFunctors.GeometricInverseImageConstantModule.

The completed coefficient and composition steps no longer directly use
lem-weil-pbc-etale-inverse-image-algebraic-structures or
lem-pe-constant-left-module-inverse-image. Removed these direct proof dependencies
and their tool-use approvals. The latter can still be reached through the planned
geometric constant-module theorem; no whole-library pruning is asserted.

The geometric refinement and localization dependencies still belong to the final
obligation's pending plan. In particular, removing their imports at this partial stage
does not establish that those nodes or modules can be pruned from the whole theorem.

## Where the brief, the DAG or earlier work was wrong

The retained composition experiment needed reassociation of the naturality equation
and explicit sheafification universe parameters. No mathematical statement defect was found.
The resumed dry run compiled the retained module and passed preflight. Four
proof-dependency imports had been added to the shared source since the earlier
report; the complete removal list above now includes those imports.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
