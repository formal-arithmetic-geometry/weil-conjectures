## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteInertiaAdequateCoarseSpace` states
`CategoryTheory.finiteInertia_exists_adequate_coarse_space`. Its sole proof is `sorry`.
No definitions, dependency modules, or statement corrections are introduced.

Clause-by-clause correspondence:

- A field k is `(k : Type u) [Field k]`.
- The algebraic stack over k is `F : BasedCategory.{v, w} (Over (Spec
  (CommRingCat.of k)))` with `hF : IsAlgebraicModuliStack F`.
- Finite type is `hft`: existence of a scheme atlas `U`, an actual atlas map `a`,
  `IsSmoothModuliAtlas F U a`, `LocallyOfFiniteType U.hom`, and `QuasiCompact U.hom`.
  The atlas is smooth over F; U is not required to be smooth over k. An étale atlas
  is not required, so non-DM stacks remain included.
- Finite inertia is `hI : IsRepresentableFiniteModuliMap
  (moduliInertiaProjection F)`. The existing inertia objects are pairs of an object
  and a vertical automorphism; its projection forgets that automorphism. The finite
  predicate identifies the actual scheme-base-change projection with a finite scheme
  morphism. It is not just finiteness of groups of geometric automorphisms.
- The existential `Q : AlgebraicSpace (Spec (CommRingCat.of k))` and
  `q : BasedFunctor F (discreteModuli Q.obj.obj)` give the required space and map over k.
- Surjectivity is `Function.Surjective (moduliPointMap q)`, on the existing quotient
  of field-valued objects by arrows and field extensions. This is stack surjectivity.
- Adequacy is exactly `IsAdequateModuliSpace F hF Q q`. Its definition includes qcqs,
  the canonical structure-map isomorphism, and power lifting for every algebra
  surjection on every affine étale base change, including non-descending algebras.
- The universal property ranges over every algebraic space T, without any separation
  condition, and every map f from F. It asserts a unique presheaf morphism g from Q
  to T with `Nonempty (ModuliTwoIso (q.comp (discreteModuliMap g)) f)`. Morphisms of
  stacks here mean morphism classes: the composite is identified with f by an
  isomorphism over the identity on the base. Literal equality of total functor
  records would not express this universal property.
- For every algebraically closed `Ω : Type u` and field embedding `j : k →+* Ω`,
  bijectivity of `((moduliFiberMap q (Over.mk (Spec.map
  (CommRingCat.ofHom j)))).mapSkeleton.obj)` expresses the geometric isomorphism-class
  bijection. The skeleton of the discrete target fibre is canonically Q(Ω).
- `HasFiniteModuliDiagonal F → AlgebraicSpace.IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) (prod.lift (𝟙 Q.obj.obj) (𝟙 Q.obj.obj))`
  is exactly the conditional separatedness assertion, over Spec k. Its diagonal is
  the actual presheaf diagonal. The existing finite diagonal tests retain both
  projections and require finiteness over the product of the two test schemes.
- There is no smoothness, order, étaleness or characteristic assumption on inertia.

Definitions read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`, full signature and docstring.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`: `CategoryTheory.IsAdequateModuliSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, and `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite`,
  `IsIntegralHom`; `.FiniteType` and `.QuasiCompact`: `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`: `moduliInertiaProjection`, `moduliInertia`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`: `IsRepresentableFiniteModuliMap`,
  `HasFiniteModuliDiagonal`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `moduliPointMap` (its definition
  of field objects and their quotient applies to general algebraic stacks too).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `moduliFiberMap`. The existing
  `IsCoarseModuliScheme` accepts only a scheme Q, so the space-valued conclusion is
  written out with the same geometric fibre map, and factorization up to 2-isomorphism.

The three already-landed definition owners `def-sfb-moduli-inertia`,
`def-sfb-finite-stack-scheme-tests`, and `def-sfb-dm-stack-morphism-properties` are added
as statement dependencies under the permission to cite landed notions. No new notion
or duplicate definition is needed. All original node fields otherwise remain unchanged.

Sources read: local `stacks-more-morphisms.tex`, theorem-keel-mori (0DUT), its gluing
proof, and lemma-keel-mori-diagonal (0DUY); Alper arXiv:1005.2398v3 §8.1 Theorem 8.1.1
and §8.2 Proposition 8.2.1, read at https://arxiv.org/html/1005.2398v3#S8.SS2 .
The current blueprint unit's `_section.md` was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
The ten-step node proof is carried in the theorem docstring, including the two overlap
comparison maps, flat-base-change categorical descent, the invariant-product
calculation, positive-rank norm lifting, and the relative diagonal argument.

All currently recorded proof-dependency modules are imported privately (the
algebraic-space definition is already public through adequacy). The Mathlib leaves
for determinant and finite-implies-proper are imported too. Four proof dependencies
have no recorded module yet: `lem-sfb-finite-inertia-etale-affine-charts`,
`lem-sfb-etale-stabilizer-preserving-affine-moduli`, `lem-sfb-etale-local-moduli-gluing`,
and `lem-sfb-stack-universal-homeomorphism-separated-target`. These are future proof
inputs, not missing statement notions; no interface for them is fabricated.

Edge cases checked before writing: the empty stack and empty atlas are allowed;
finite nonreduced inertia in characteristic p (e.g. Bμ_p) is not excluded;
finite constant inertia whose order is divisible by p is not excluded; the identity
stack of a finite-type scheme has its usual coarse space; non-separated targets T
remain in the universal property; finite inertia alone does not force Q separated,
so separatedness is conditional; smooth atlas does not impose smoothness of F/k.
The field, schemes, algebraic spaces and geometric extensions use the same universe u;
the total-category morphism and object universes v,w are explicitly independent.
No vacuous instance assumptions, extra equality of universes, or unbound variables occur.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Finite inertia algebraic stack has an adequate coarse
  moduli space"`: eight scheme-finiteness hits; no coarse/adequate existence theorem.
- `msearch.py ... loogle '"coarse"'`: ten unrelated partition/coarsening hits.
- `msearch.py ... grep 'Keel.Mori|coarse.moduli|adequate.moduli'`: zero Mathlib hits.
- `msearch.py ... leansearch "Algebraic stack with finite inertia admits an adequate
  coarse moduli space"`: eight scheme properness/finiteness hits, no stack theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `Keel.Mori|coarse.moduli|adequate.moduli|FiniteInertia`, and the required item-id
  grep over `lean/WeilConjectures`: no existing theorem states this node. Project
  hits are the adequate-moduli definitions/consequences, DM-only coarse theorems,
  and unrelated inertia constructions.
- Name searches for `finite_inertia_adequate_coarse_space`,
  `finiteInertia_adequateCoarseSpace`, and `IsCoarseModuliSpace` in Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`: no hits.
- Project declaration searches found and reused `moduliInertiaProjection`,
  `IsRepresentableFiniteModuliMap`, `HasFiniteModuliDiagonal`, and the point quotient.

No STATEMENT-DISPUTED finding. The prescribed CompactObject example is now withdrawn
and contains no declarations; the current module-mode convention in the brief and
nearby algebraic-geometry modules was followed.

Validation: prescribed `scompile.py` succeeded in sandbox and library module modes
(10.3 s and 10.4 s), without errors or unexpected warnings.

## Second reading by Q121

Author's second pass, not an independent review; the dispatch brief prohibits starting
another agent, and the maintainer supplies the independent review. I reopened the node
and compared every clause with the signature: hF is algebraicity, hft is finite type
via a smooth atlas, hI is finite inertia, the existential gives Q and q, and the four
conclusion blocks give surjectivity, adequacy, both coarse properties, and conditional
separatedness. In particular I checked that the smoothness occurs only in the atlas
map, the target T is arbitrary, the geometric map is induced by q, and the closed
immersion is the relative diagonal over k. No mismatch or statement change was needed.
