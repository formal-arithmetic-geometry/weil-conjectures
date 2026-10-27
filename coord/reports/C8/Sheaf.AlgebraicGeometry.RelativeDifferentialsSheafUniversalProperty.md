## What changed

Proved `AlgebraicGeometry.Scheme.Hom.relativeDifferentials_sheaf_universal_property`
in `Sheaf.AlgebraicGeometry.RelativeDifferentialsSheafUniversalProperty` without changing
its statement or its public imports. The existing source-library
`relativeDifferentialsHomEquiv` proves bijectivity; sectionwise addition, zero and
composition give the three middle conjuncts. The final conjunct follows from
`relativeDifferentialsToRestrict_app_d`, since the inverse of the canonical restriction
isomorphism is `relativeDifferentialsToRestrict`. The restricted morphism has the original
morphism's component on the image open. Updated the declaration docstring and the item's
DAG proof, proof dependencies and proof origin to reflect this route.

The proof is uniform in arbitrary module sheaves and arbitrary schemes. In particular it
adds no quasi-coherence, nonemptiness, affineness or characteristic hypothesis. The formulas
also apply to the empty open immersion and zero target module. No shared definition,
statement, instance or attribute was changed; no consumer adaptation is needed.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_sheaf_universal_property`
(node `lem-sfb-relative-differentials-sheaf-universal-property`).

Holes closed: 1 of 1. Holes added: 0. Holes remaining in the item: 0.
No split-off theorem or new module was added.

Validation: the final module compiled through `lcompile.py` with exit code 0 in 3.5 s,
without errors or warnings. The declaration signature and public imports were compared
verbatim with the current source and are unchanged.

## No longer needed

Removed these private proof imports:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.

The proof no longer directly needs these planned proof dependencies:

- `lem-weil-pbc-affine-tilde-gamma-adjunction`, represented by
  `Mathlib.AlgebraicGeometry.Modules.Tilde`: the global Hom equivalence is already proved;
- `lem-sfb-affine-derivation-global-ext`, represented by the proved declaration
  `Scheme.Modules.derivation_ext_of_isAffine` in
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`: no affine reduction is needed;
- `lem-pur-sheaf-hom-cover-gluing`, represented by
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`: global existence,
  uniqueness and restriction already have proved canonical APIs;
- `def-weil-pbc-kahler-differentials`: the proof uses the sheaf Hom equivalence directly,
  rather than applying the ring universal property again. This remains a statement
  dependency of the unchanged item.

Removed the obsolete top-level `tool_uses` approval for
`lem-pur-sheaf-hom-cover-gluing`. No library module or declaration is withdrawn. In
particular the upstream differential module and its public imports are preserved; its
internal affine results still use some of the preceding dependencies. These are removals
from this item's direct proof route, not a claim that their modules leave the targets'
entire import closure. The fixed unit statement and its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's affine-local construction argument is unnecessary for the current Lean
construction. Reading `WeilConjectures.AlgebraicGeometry.Modules.Differentials` shows
that the sheaf is constructed by sheafification of presheaf differentials, and its
universal property is already the proved `relativeDifferentialsHomEquiv`. That same
module proves `relativeDifferentialsToRestrict_app_d`. Thus the naturality, additive
and restriction clauses can be assembled without redoing affine descent. This is also
consistent with Stacks Morphisms Tag 01UR (`lemma-universal-derivation-universal`),
whose proof is a restatement of the definition, and Tag 01US
(`lemma-differentials-restrict-open`). There is no mathematical statement correction.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
