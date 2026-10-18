## What changed

Proved `AlgebraicGeometry.Etale.isIso_strictLocalSpecialization_smooth_proper_prime`
in `Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization`, keeping its signature
and the definition of `strictLocalSpecialization` unchanged.

The proof forgets scalars, reuses the given locally constant datum, and proves every
section is killed by ell using characteristic ell of the coefficient ring.
The geometric stalk / coefficient-forgetting comparison transports this annihilator
to the abelian stalk. The local ring map to the residue field preserves the assumed
unit ell; the additive order divides ell and is prime to nonzero residue characteristic.
Apply `smooth_localAcyclicity`,
`isLocallyAcyclicRelative_of_locallyConstant_torsion`, and
`isIso_etaleStalkSpecialization_of_proper_locallyAcyclic` in that order.
The last result has exactly the required map by definitional equality.

Added the proof-only import `Mathlib.Algebra.CharP.CharAndCard` for the unit /
characteristic divisibility equivalence. Updated the node proof and dependencies
to match the abelian route actually used.

Validation: the complete proof compiled through lcompile.py, then compiled again
after removing the unused proof imports. No compiler errors or warnings.
Source checked: Stacks etale-cohomology.tex, Tag 0GKD,
`lemma-sp-isom-proper-loc-cst-torsion`, whose proof invokes 0GJW, 0GJR and 0GJQ.
The source explicitly allows infinite stalks. The Lean proof handles zero elements,
characteristic zero, all nonnegative degrees, and arbitrary test geometric points.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Etale.isIso_strictLocalSpecialization_smooth_proper_prime`
(node `lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The three existing local-acyclicity / proper-specialization dependencies remain
separate proof obligations; this delivery proves the assigned theorem from their
stated declarations, as required by stage 3.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` and the
proof dependency `lem-weil-pbc-module-abelian-derived-direct-image-comparison`.
The conclusion already uses abelian higher direct images after forgetting scalars,
so the optional module-derived comparison (old proof step 5) is unnecessary.

Removed the proof-only import `Sheaf.CategoryTheory.RingedSiteModules` and the
proof dependency `def-weil-sheaf-of-modules-category`. The statement already uses
Mathlib's ModuleCat-valued sheaves; the proof only needs those modules and their
underlying abelian groups, not the ringed-site module category. Its unchanged
statement dependency remains as part of the node's mathematical terminology.

All three nontrivial local-acyclicity / specialization dependencies are used.
No unit statement or realized unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The optional coefficient-comparison step of the node was unnecessary for the
existing abelian-valued conclusion. Otherwise the given plan applied without
signature, definition, or consumer changes. No disputed statements were found.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
