## What changed

Replaced the hole in `CategoryTheory.exists_site_finite_constant_extension_tower`
by induction on the natural cohomological width, simultaneously for all slices
C/U of the original site. The original theorem statement and every original
public import remain unchanged.

The item now proves the width-zero case using the canonical derived t-structure,
its single-cohomology comparison, and the supplied finite constant trivializations.
Its successor case applies the local cone step, invokes the induction hypothesis
on each cone, restricts the rotated triangle to the resulting covering refinement,
and applies the tower constructor. The proof explicitly transports the constant
single object, the triangle's shift, and the iterated derived restrictions.
`Precoverage.comp_mem_coverings` composes the covers. The final comparison
identifies the restrictions with the exact objects in the original conclusion.
All auxiliaries in the item are private and fully proved; the two abbreviations
only name existing restriction and local-constancy expressions inside these proofs.

Added the private proof imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
and `Sheaf.Paper.SiteFiniteConstantConeStep`. The source-library import provides
existing derived functor comparisons; the constant/restriction comparisons use
Mathlib's existing sheafification API. The new module isolates the
single nonrecursive geometric step: locally killing top cohomology by a finite
free constant source and proving the cone has finite locally constant cohomology
in the smaller interval. It asserts no tower, representing complex, induction
hypothesis or full-interval model.

The existing DAG node now follows this Lean induction. The local lifting,
truncation and Serre arguments remain in the new cone node, rather than being
silently dropped. No source-library module, definition or consumer is changed.

Verification: both sandbox modules compile together through `lcompile.py --all`.
The complete tower proof compiles in 24 seconds; the cone module is cached from
its successful compile. Two unused private binder names were subsequently
prefixed with underscores; the delivery checks compile the final files again.

## Proved and sorry left

Original holes: one. Closed by a complete reduction:
`CategoryTheory.exists_site_finite_constant_extension_tower`
(`lem-weil-pbc-site-finite-constant-extension-tower`). There are zero textual
`sorry`s in the item module.

Added and left: one named public theorem with proof exactly `:= by sorry`,
`CategoryTheory.exists_site_finite_constant_cone_step` in
`Sheaf.Paper.SiteFiniteConstantConeStep`
(`lem-weil-pbc-site-finite-constant-cone-step`). Its docstring and node give the
source, the finite generator lift, the long exact sequence, the finite locally
constant Serre argument, and the slice comparisons needed to prove it.

This is a decomposition of one hole into one strictly smaller, nonrecursive
obligation, with zero net hole closures. The complete induction from that
one-step assertion to a finite tower is the new proved content. In particular,
the new assertion is not the tower theorem under another name: it gives one
triangle and one smaller-interval object, never a tower, and it applies only to
positive width. All width-zero cases are proved without it.

Edge checks: width zero uses arbitrary finite coefficient modules, including
zero modules. Width one invokes the proved width-zero case on the cone and adds
one triangle. No step assumes a nonzero ring, positive free rank, a nonempty
cover, a point of the site or nonzero top cohomology. Sigma-indexed covering
composition handles empty families. The induction uses only the given derived
categories of C/U; it makes no extra assumption about derived categories of
iterated slice presentations.

## No longer needed

No original imports are removed, and no module or declaration is withdrawn.
No modules are claimed as globally pruned. The unused trial proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf` was removed. The new
cone module also omits a redundant direct import of `Sites.ConstantSheaf`.
`Sites.Pullback` is retained because it supplies preservation-of-limits instances
needed to form the exact derived restriction in the new statement.

The tower induction no longer directly needs these original planned dependencies:
`lem-weil-pbc-truncation-descends`,
`lem-weil-pbc-local-finite-free-epi-lift`,
`lem-weil-pbc-locally-constant-derived-serre`, and
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`.
They are retained as dependencies of the new one-step cone node, where their
mathematics is still required. The original direct edge to
`def-weil-finitely-generated-module` is also unnecessary for assembling the tower;
finite module data is supplied by the base hypothesis or the cone step.

The recorded ringed-module restriction theorem
`lem-pur-site-restriction-module-adjunction-exact` is not applied by the tower
induction: exactness of ModuleCat-valued restriction is proved directly from its
left adjoint and limit-preserving descriptions, using existing Mathlib APIs.
The ringed-module theorem remains in the cone node's plan for the transport of
the recorded Serre result. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found, and no signature was changed.
The existing plan hid the induction's slice bookkeeping: applying induction
naively on C/U would ask for derived categories on iterated slices that are not
explicit hypotheses of the original statement. Induction over all original-site
objects U, with restriction along V to U, avoids that unnecessary assumption.
Canonical exact derived compositors and constant comparisons perform the
transport explicitly.

The remaining work is the actual local finite-free cone reduction, not the
induction or tower assembly. Its new statement is a genuine partial step of
Tag 094G, preceding the source's invocation of the induction hypothesis.

## New nodes

`lem-weil-pbc-site-finite-constant-cone-step`, implemented by
`Sheaf.Paper.SiteFiniteConstantConeStep`, records the positive-width local cone
construction of Stacks Project Tag 094G. Its hypotheses are finite locally
constant cohomology on all further slices and cohomological support [a,b]; its
output is one rotated triangle with a finite constant attachment in degree b-1
and a cone supported on [a,b-1] with the same local constancy property. LeanSearch,
LeanFinder, Loogle and text searches found the needed generic ingredients but no
existing theorem with this conclusion. This is the only new node and the only
remaining hole. No change record is needed because existing statements and
definitions are unchanged.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
