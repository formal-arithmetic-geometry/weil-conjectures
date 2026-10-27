## What changed

Replaced the hole in `AlgebraicGeometry.affine_pushforward_colimit` by a proof using
relative spectrum, the canonical affine projection formula, and tensor preservation of
colimits. The statement and public imports are unchanged. All auxiliary lemmas are private
and proved in the item module. No source-library module is changed.

Repair of returned head `031d3e37924`: removed the duplicate private theorem
`AlgebraicGeometry.algebra_eqToHom_app`. The source theorem in
`WeilConjectures.AlgebraicGeometry.AffineOverLimitInclusion` is itself private, so
importing that module cannot expose it. Both uses now apply the existing general Mathlib
theorem `eqToHom_map` directly, specialized to the functor taking an algebra sheaf
to its sections on the chosen open. A local binding with the section expression as its type
exposes this specialization to the simplifier without introducing another library declaration.
No source declaration is changed or reintroduced.

To avoid unfolding the tensor pullback construction while constructing the projection map,
its private helper now takes an arbitrary module `G` and a map `F → f_*G`. The affine
projection isomorphism specializes it to the tensor pullback and the prescribed unit.
A private generic cocone-transport lemma proves the categorical transport before
specializing it to sheaves, so the main proof avoids repeated reduction of the concrete
category. The section actions are explicit local instances, avoiding repeated unfolding of the
pushforward while elaborating the bilinear map. The underlying-module functor is explicitly
typed in the scheme module category. After constructing the projection map, local
irreducibility of the tensor-section and pullback constructors keeps the subsequent proof
on their established APIs.

The algebra comparison is obtained by restricting to the cofinal tail, viewing the
limiting cone in affine schemes over the fixed stage, and applying the relative-spectrum
anti-equivalence. Its section formulas identify the given algebra diagram with the
image diagram and identify the colimit legs.

The projection map is constructed from the bilinear formula `t, a ↦ a • η(t)` and module
sheafification. On an affine open it is bijective by the existing pullback-section and
tensor-section comparisons; the affine basis criterion makes it an isomorphism.
The underlying module functor preserves directed algebra colimits by the existing
sheaf-algebra colimit theorem. The supplied module diagram and cocone are transported
along their specified object equalities, using the section hypotheses. Tensoring preserves
the resulting colimit by the sheaf tensor–Hom adjunction. The transition and leg formulas
follow by cancellation of each projection isomorphism and the pure-tensor naturality law.

## Proved and sorry left

Closed: `AlgebraicGeometry.affine_pushforward_colimit`
(node `lem-sc-valuation-limit-affine-pushforward-colimit`).
One original hole, zero added holes, zero remaining holes in the item module.
No new split statements. The duplicate-declaration/import-pruning check passed. The
optimized complete proof compiled without warnings in 33.9 seconds (the section actions deliberately use
inline `letI`; its style suggestion is scoped off for this performance-sensitive helper). The delivery tool performs its fresh
compile, declaration and axiom checks before pushing.

Searches recorded in `searches.jsonl`: LeanFinder for the affine projection formula
returned pullback/pushforward and tensor pullback declarations but no packaged theorem;
Loogle for colimits and tensorLeft returned a cokernel tensor theorem; grep for
`pushforward.*tensor|tensor.*pushforward` found no direct projection-formula match.
The existing relative-spectrum, affine-section and tensor–Hom APIs give the proof.

## No longer needed

The explicit import `WeilConjectures.AlgebraicGeometry.LimitAffineTransition` is unnecessary:
Mathlib already supplies `isAffineHom_π_app` for the supplied limiting cone. This prunes the
explicit dependency on `lem-weil-pbc-limit-affine-transition` from this proof.

`lem-weil-pbc-spec-colimit-limit` is not invoked separately: the already proved
relative-spectrum anti-equivalence takes the limit directly to an algebra colimit.
The ring-module node `lem-weil-pbc-tensor-commutes-with-colimits` is replaced here by
the more direct sheaf tensor–Hom adjunction. Its old tool-use approval is removed, as
are the old approvals of `lem-weil-pbc-limit-affine-transition`. The separate
affine-section calculation of tensor colimits is unnecessary because the
existing sheaf tensor–Hom adjunction proves preservation of all colimits directly.
The import `WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
and proof dependency `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections` are also
unnecessary: the algebra comparison α transports quasi-coherence from the affine
pushforward of the structure sheaf directly. Both pullback-affine-sections and
tensor-affine-sections theorems remain necessary for the projection formula. No declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily duplicated a private source-library transport helper.
That helper is now removed in favor of the general Mathlib API at its call sites.
No statement error was found. The planned proof has a shorter categorical implementation:
apply the relative-spectrum anti-equivalence rather than reconstruct its affine charts,
and use the tensor–Hom adjunction rather than test the tensor colimit on affine sections.
The unit's cube-theorem route is preserved; this is only a simplification of its generic
inverse-limit tool. The named general sheaf-algebra directed-colimit result supplies the
underlying-module assertion directly. No definitions or target statements are changed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
