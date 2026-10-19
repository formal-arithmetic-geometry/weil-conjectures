## What changed

Proved AlgebraicGeometry.ProEtale.VaryingRing.properOpenPasting and
AlgebraicGeometry.ProEtale.VaryingRing.gamma_identities without changing their statements.
Vertical pasting applies Mathlib mateEquiv_hcomp to alpha_vertical, and transports
through the proper compositors using the two conjugate/mate composition identities.
Horizontal pasting applies mateEquiv_vcomp to alpha_horizontal. A proved private
mate_whisker helper supplies naturality in the open comparison maps. Identity
normalization follows from alpha_identities, the conjugate identity comparisons,
and the adjunction triangle identities.

Only the assigned Lean module changes. No definitions, public signatures, public
imports, target statements, or DAG route change. The retained module was rechecked against the current published build through
lcompile.py. A copy with profiler and trace.profiler enabled compiled without
errors in 22.8 seconds. No profiler options are included in the delivery.
The earlier 900-second failure was in the Python delivery preflight, not a Lean
60-second compilation failure; no definition change is justified by that result.
Required delivery checks are run again on this resumed attempt.

## Proved and sorry left

Closed 2 of the original 9 holes:

- AlgebraicGeometry.ProEtale.VaryingRing.properOpenPasting
- AlgebraicGeometry.ProEtale.VaryingRing.gamma_identities

Added 0 holes; split off 0 statements. These are proofs from the existing declared
alpha laws, which remain the intended next obligations.

The following 7 original holes remain unchanged, all attached to
lem-sp-varying-ring-proper-open-pasting:

- AlgebraicGeometry.ProEtale.VaryingRing.modulePi_components
- AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_vertical
- AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_horizontal
- AlgebraicGeometry.ProEtale.VaryingRing.alpha_vertical
- AlgebraicGeometry.ProEtale.VaryingRing.alpha_horizontal
- AlgebraicGeometry.ProEtale.VaryingRing.alpha_identities
- AlgebraicGeometry.ProEtale.VaryingRing.gamma_evaluation

The first three still need the ordinary clopen projection and section computations;
the next three need localization of those ordinary comparisons and identity lifts;
evaluation still needs the normalized comparison with the constant-ring construction.

## No longer needed

Removed these unused proof-only imports:

- Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.Paper.SemilinearDerivedSections

The new proofs use the existing VaryingRingProperOpenArrows public interface and
Mathlib.CategoryTheory.Adjunction.Mates. No planned dependency node is declared
obsolete: the remaining seven holes still have the original geometric/localization
plan. No whole module is withdrawn; the removed imports may remain transitively reached.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction or statement change was needed. The existing DAG's
Steps 10 and 11 are now implemented for mate pasting and gamma identity normalization.
The unit route is preserved. Several lcompile.py requests temporarily returned
server-busy-or-unreachable errors; later retries succeeded and returned actual Lean
feedback. No tool was changed or bypassed.

Earlier interrupted attempts did not push a delivery. On this resumption the
retained source compiled with profiling enabled. The initial delivery retry was
cancelled while still in the worktree-capacity queue, before constructing a
commit; the subsequent retry is allowed to finish. Launcher files were neither
edited nor copied. No definition or target meaning was changed.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
