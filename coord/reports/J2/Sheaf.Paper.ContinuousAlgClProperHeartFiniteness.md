## What changed

Replaced the hole in `continuousAlgCl_proper_heart_finiteness` by finite-stratum
devissage. The statement and original public import are unchanged. The proof uses
the already proved coefficient-general `bounded_finiteModel_generation`: its
finite sheaf filtration and short-exact-sequence triangles reduce the arbitrary
constructible sheaf to extensions by zero of reduced locally closed pieces.
The generic proved helpers in `CoefficientHeartClosure` give the weak Serre class,
using `continuousAlgCl_lf`; their generic coefficient parameters permit the actual
all-continuous coefficient. The restricted public finite-field/Qbar theorem is
not applied to that coefficient.

Added `Sheaf.Paper.ContinuousAlgClProperLisseStratum`, isolating precisely the
proper image calculation for a lisse module on a single locally closed stratum.
The parent turns a finite constant local model into local finite presentation,
then local finite freeness, and applies this stratum theorem. The parent node's
proof now records this argument. No shared definition or existing signature changes. A proved private generic
`finiteModel_heart_image` keeps the devissage independent of the concrete
proper pushforward; this reduced kernel checking from a timeout to 5.5 seconds
in the diagnostic compile. Profiling options have been removed.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_heart_finiteness`
(node `det-sf-comp-continuous-algcl-heart-finiteness`).
Added one named hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_lisse_stratum`
(node `lem-sfb-continuous-algcl-proper-lisse-stratum`).
There are zero holes in the item module and one in the new module.
This is a decomposition (one closed, one added, net zero), not a complete
sorry-free finiteness proof. The completed portion is the arbitrary-sheaf finite
filtration assembly, including weak Serre closure and passage to derived cohomology.
The remaining theorem has the strictly special input `(v_! t_* L)[0]`, with S
reduced and L lisse; it does not accept arbitrary constructible sheaves.

Edge cases: the generation theorem includes zero objects and empty strata; the
weak Serre property contains the rank-zero constant model; the stratum statement
allows rank zero, empty S, identity immersions and arbitrary integer cohomological
degrees. It imposes no finite-coefficient-image assumption on continuous functions.

## No longer needed

Removed the item's direct proof import
`WeilConjectures.RepresentationTheory.IntegralModel`: compact matrix coefficient
descent belongs to the remaining stratum calculation, not to the completed
filtration argument. It is still needed in the new node's proof plan, so no
underlying representation-theory declaration is withdrawn.
All original declared dependencies remain relevant, either to the completed
proof or the stratum calculation. No module is withdrawn or globally pruned.
The new proof does not use the all-continuous proper scalar comparison or any
identification of the all-continuous ring with finite-subextension-valued sections.
The proper-heart module is imported for its already proved generic zero,
isomorphism and degree-zero single-object helpers; its finite-coefficient proper
finiteness theorem remains part of the new stratum node's plan.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan includes a coefficient comparison that is not supplied
by the finite-coefficient proper-heart declaration. That theorem concerns finite
extensions and finite-subextension-valued Qbar, whereas this item concerns all
continuous maps to PadicAlgCl. These rings must not be identified.

`ContinuousAlgClProperScalarComparison` cannot supply the missing comparison in
this proof: its existing imports and its proof step 3 use
`ProperLocalizingContinuousAlgCl`, then `ContinuousAlgClProperFiniteness`, then
this item. Its proof explicitly first assumes that the all-continuous proper image
is constructible. Using it here would be circular. That module and its dependencies
are preserved. The new stratum node explicitly retains the finite-model comparison
as work to prove, without appealing to that circular route.

The blueprint ancestor search follows module-valued `created.item` poorly here:
it returned no ancestor for the parent. The parent's existing explicit blueprint
reference identifies `det-sf-comp-coherence-single`; the new node retains that
ancestor and records the parent in `via`. Blueprint search for proper/lisse found
no duplicate of the all-continuous stratum assertion. The unit route is preserved.

## New nodes

`lem-sfb-continuous-algcl-proper-lisse-stratum` is the existing plan's lisse-piece
calculation, with finite-filtration assembly removed. Its new module has one public
theorem and one whole-proof sorry, with the source and proof in its docstring.
Its node records LeanSearch, Loogle and grep searches, the actual continuous-map
coefficient, and the compact-monodromy/lattice/finite-model comparison route.
No change record is required: only the item, its node, this new module and its new
node are changed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
