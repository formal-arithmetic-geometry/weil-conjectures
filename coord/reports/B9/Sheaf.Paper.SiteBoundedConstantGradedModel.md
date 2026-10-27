## What changed

Replaced the hole in `CategoryTheory.exists_site_bounded_constant_graded_model`
by a complete proof from finite constant extension towers. The original public
statement and all its public imports are unchanged. A direct source comparison
confirmed both are byte-for-byte identical. Remote compilation checked the tower
definition (2.0 seconds), the local existence statement (3.7 seconds), and the
completed realization proof (5.0 seconds), all below the 60-second limit.

Added `Sheaf.Paper.FiniteConstantExtensionTower`, defining a genuine finite
sequence of distinguished triangles, and
`Sheaf.Paper.SiteFiniteConstantExtensionTower`, isolating the source's
cohomological tower construction. The latter is the sole remaining hole.

The proved private helper `constant_tower_has_model` works for any additive
functor from B-modules to an abelian category, without Noetherianity or a site.
It inducts on the tower, represents each boundary using the already proved
bounded-top morphism theorem, constructs the actual mapping cocone, identifies
its terms by removing zero biproduct summands, and compares distinguished
triangles. Shifting back gives the required derived isomorphism. The final
application retains the covering and proves the exact interval bounds.

This separates source steps 1--3 (local generator lifting and the cohomological
induction) from steps 4--5 (chain realization and triangle comparison), which
are now implemented. The remaining statement contains no complex, differential,
chain representative, or isomorphism to the localization of a complex. Its
inductive tower is real data defined without any postponed proofs. Thus the
new hole is a proper part of the source argument, rather than the model theorem
under another name.

## Proved and sorry left

Original holes closed: the body of
`CategoryTheory.exists_site_bounded_constant_graded_model` now contains a complete
Lean proof. `constant_tower_has_model` is also fully proved.

Holes added and left: exactly one,
`CategoryTheory.exists_site_finite_constant_extension_tower`, in
`Sheaf.Paper.SiteFiniteConstantExtensionTower`, node
`lem-weil-pbc-site-finite-constant-extension-tower`. Its proof is exactly
`:= by sorry`; its docstring and node give the cohomological induction in full.

Classification: decomposition of one original hole into one strictly partial
obligation; zero net hole closures, one split off. No holes in definitions and
no new axioms. The tower definition has zero holes.

Edge checks: the generic realization handles width zero, width one (a genuine
two-term differential), zero coefficient modules, zero ring, and arbitrary
additive functors preserving zero objects. In a successor, at degree a+n+1
the old term vanishes; at every other degree the shifted single term vanishes.
Consequently there is never a spurious overlap term or a term outside the
specified interval. The local tower statement also permits empty covering
families and zero-rank free presentations.

## No longer needed

Removed these private proof imports from the item module:

- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.Paper.LocalFiniteEpiLifts`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

Their mathematical dependencies are retained in the new tower-existence node's
proof plan; they are not claimed as globally pruned mathematics. In particular,
the finite-free lifting, Serre, restriction, and truncation results remain
needed for the cohomological induction. The main node now uses the new tower
lemma plus the existing bounded-top representative and standard triangulated
and derived-category APIs. The long exact sequence is confined to the tower
construction; the realization uses the triangle isomorphism theorem directly.

No module or upstream declaration is withdrawn. No unit route is bypassed.
No right-fraction lemma or differential-descent theorem is introduced. No
public imports are removed from the original module.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or target was changed. The old DAG combined the
cohomological induction and the chain realization into a single obligation.
The new nodes expose their interface so the latter can be checked independently.

The recorded Serre and localized-system exactness theorems use ringed-module
sheaves, while this item uses ModuleCat-valued sheaves. They cannot be applied
literally without a comparison. The new tower proof plan explicitly cites the
already proved constant-ring module-sheaf equivalence
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence` and its constant and
slice comparisons. No duplicate encoding or bridge statement is added.

## New nodes

`def-weil-pbc-finite-constant-extension-tower` defines the finite triangular
tower before chain realization, in `Sheaf.Paper.FiniteConstantExtensionTower`.
It starts with a finite constant single object and attaches finite constant
single objects in successive degrees by distinguished triangles.

`lem-weil-pbc-site-finite-constant-extension-tower` states source steps 1--3,
including the base case and composition of covering refinements, in
`Sheaf.Paper.SiteFiniteConstantExtensionTower`. It retains the original
cohomological hypotheses and produces only the finite triangular tower. Its
remaining work is local top-generator lifting, the cone cohomology calculation,
finite local constancy, and induction over slices. The existing main node has
its proof and proof dependencies updated to the compiled realization argument.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
