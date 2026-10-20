## What changed

Retired the assigned duplicate Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift,
as requested by its coord/retire-items.tsv row. The node
lem-sc-open-stalk-free-map-local-lift now points to the existing, proved source theorem
AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts, recording its exact
signature. The source fixes the comparisons to openModuleStalkRestrictionComparison;
choosing this family proves the original existential-family assertion unchanged.

Adapted the only remaining direct consumer, Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift:
replace its private import by the source twin and supply the explicit canonical family
before applying the lifting theorem. Its signature, public imports, visibility and
finite-support proof are preserved. The source library is untouched.
Change record: coord/changes/M2-retire-open-stalk-free-map-local-lift.md.

## Proved and sorry left

Zero-hole retirement: proved 0 of 0 existing sorries; holes added 0; split off 0.
No sorry remains in the delivered consumer or the withdrawn module. This is pruning,
not a new mathematical proof or a decomposition. The retained source proof was read:
one-neighbourhood lifting and restriction transport combine by functoriality,
naturality, and isomorphism cancellation, exactly as in the node's plan.

The adapted consumer compiled through lcompile.py --all in 5.0 seconds without warnings.
An earlier import-only migration failed at the old existential obtain, establishing
why the explicit-family proof adaptation is needed. The canonical family is chosen
independently of degree, source, target and map. Rank zero, an empty support interval,
equal opens, non-affine U, and arbitrary target modules remain included.
The delivery dry run passed compilation, static preflight and axiom checks
(commit 3d29ec118a). The packet is class CODEX for independent review.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift, including its duplicate
private restriction_lift_stalk helper and its existential wrapper of the source result.
Removed its private import from PerfectOpenStalkDegreewiseLift, replacing it with
WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapLocalLift. No other consumer import is
removed or changed. The withdrawn file's imports disappear with it: public
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor,
Mathlib.Algebra.Category.ModuleCat.Sheaf.Free, Sheaf.Paper.DerivedHomMayerVietoris;
private WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapOneLift and
WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport. Their mathematical APIs
are still available where needed through the surviving consumer and source modules;
no additional module is claimed globally pruned.

No mathematical node or proof dependency is withdrawn: the one-lift and transport nodes
remain needed by the source proof, and parents still cite the same local-lift node.
The unit sk-prop-av-cube and its route remain unchanged. No quarantined parent imports
this module. No adopted source declaration or proof dependency is deleted.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a theorem already proved. Its current retirement
row is the applicable task: eliminate the duplicate while preserving its meaning.
The inventory names two direct consumers; FiniteProjectiveOpenStalkMapsLift has already
been retired, leaving only PerfectOpenStalkDegreewiseLift. The source API is stronger:
the comparison family is explicit and canonical, rather than existentially packaged.
The old node attachment referred to the duplicate; it now refers to this source theorem.

The import-only consumer migration produced `Tactic rcases failed ... is not an inductive
datatype` at line 69. The source theorem is universally quantified over m, N and t,
so the necessary adaptation defines e explicitly and takes he to be that theorem.
No binder, hypothesis or conclusion of the consumer is changed.

Read the Stacks sources locally: modules.tex, lemma-stalk-internal-hom (Tag 01CP),
and sheaves.tex, lemma-j-pullback (Tag 00A0), especially (3) and its cofinality proof.
Read both local-lift proofs, both stated proof-dependency signatures and their source
proofs, the open-stalk definitions, the consumer and the cube unit record.
Real msearch.py searches with leanfinder, loogle and grep found affine Tilde germ
formulas, free-module rank results, and restriction-stalk comparison APIs, respectively;
none gives this arbitrary module-sheaf uniform lifting theorem. Direct library search
found the stronger fully proved source twin, which is used without modifying it.
No new node or unfinished obligation is introduced.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
