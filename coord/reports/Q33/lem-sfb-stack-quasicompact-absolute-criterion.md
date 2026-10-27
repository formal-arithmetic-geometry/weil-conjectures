## Worker report

The module `Sheaf.AlgebraicGeometry.StackQuasicompactAbsoluteCriterion` states
`CategoryTheory.isQuasiCompactModuli_iff_absoluteStructure`. Its only theorem proof
is `sorry`. It introduces no definitions and makes no statement correction.

Clause-by-clause correspondence:

- Schemes and Spec use the recorded Mathlib `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Spec`, from `Mathlib.AlgebraicGeometry.Scheme`.
- The absolute base is `Spec (.of (ULift.{u} ℤ))`. The universe lift realizes the
  integers in the same universe as the schemes; it changes neither ring nor base.
- The algebraic stack A over that base is
  `A : BasedCategory.{v₁, w₁} (Over (Spec (.of (ULift.{u} ℤ))))`, with hypothesis
  `hA : IsAlgebraicModuliStack A`. This is the recorded algebraic-stack predicate:
  etale descent, algebraic-space diagonal, and existence of a smooth surjective
  scheme atlas. No atlas is chosen in the hypothesis.
- Its structural morphism p is the existing `moduliBaseStructure A`, whose
  underlying functor is exactly `A.p`. Its target is the identity category over
  Sch/Spec Z. The fibre over each test scheme is the singleton groupoid, hence
  this is the usual represented base scheme. It is canonically equivalent over
  the site to the Yoneda/discrete model; no arbitrary map is substituted for p.
- “A admits a smooth surjective atlas from a quasi-compact scheme” is precisely
  `IsQuasiCompactModuli A`. The existing definition unfolds as
  `∃ (U : Over _) (a : BasedFunctor (discreteModuli (yoneda.obj U)) A),
  CompactSpace U.left ∧ IsSmoothModuliAtlas A U a`.
- “If and only if p is quasi-compact” is the displayed `↔` with right side
  `IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, u, u + 1, v₂, w₂}
  (moduliBaseStructure A)`.
- “For every quasi-compact algebraic stack V over Spec Z” and quasi-compactness
  of `A ×_Z V` are the actual defining quantifiers and conclusion of this map
  predicate: for every based category Z and based functor g into the base,
  `IsAlgebraicModuliStack Z → IsQuasiCompactModuli Z →
  IsQuasiCompactModuli (moduliTwoFiberProduct (moduliBaseStructure A) g)`.
  Test universes are `max u v₁ v₂` for arrows and
  `max (u + 1) w₁ w₂` for objects, including the base and the source stack.
  Independent upper bounds v₂ and w₂ allow arbitrary enlargement; no small-only
  specialization is made. The 2-product is the existing category of triples,
  retaining its comparison isomorphisms and automorphisms.
- There is no quasi-separatedness assumption on A or any test stack, and no
  representability, finite-type, smooth-structure-map, or DM assumption on A.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map` (scheme and affine-spectrum dependencies).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `CategoryTheory.IsQuasiCompactModuli`, `IsQuasiCompactAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `IsFibredInGroupoids`, and the based-functor/2-isomorphism conventions.
- Added the already landed `def-sfb-relative-moduli-inertia` to stmt_deps, solely
  to cite its existing canonical structural map, not to introduce another one.
  Its module `Sheaf.AlgebraicGeometry.RelativeModuliInertia` defines
  `CategoryTheory.moduliBaseStructure` with `toFunctor := F.p`, `w := rfl`.
- `def-weil-size-convention` is metatheoretic: explicit universe binders implement
  it; its record names no module or declaration.

The stated proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (schemeSpace),
`Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection`
(algebraic_stack_quasicompact_surjection),
`Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts`
(algebraicStack_twoFiberProduct), Mathlib's AffineScheme and Morphisms.QuasiSeparated
(compactSpace_of_isAffine and quasiSeparatedSpace_of_isAffine), and Pullbacks
(pullbackSpecIso). The recorded
`lem-sfb-fibred-groupoid-representable-smooth-calculus` has neither a Lean record
nor a Mathlib match at preparation time, so there is no module to import for it;
its role is retained explicitly in the complete natural-language proof docstring.
It is only a proof dependency and introduces no missing statement notion here.

Source checks: read Stacks `stacks-properties.tex`, lemma-quasi-compact-stack,
Tag 04YC (affine and quasi-compact smooth atlas criteria),
`stacks-morphisms.tex`, definition-quasi-compact, Tag 050U (all quasi-compact
algebraic-stack tests), and `schemes.tex`, lemma-fibre-product-affines, Tag 01JQ
(the product of affine atlases over Spec Z is affine). The theorem docstring
contains all four DAG proof steps, including their cited node names.

Edge cases checked before writing:

- Empty A: the empty scheme is an admissible quasi-compact atlas and every test
  product is empty. No Nonempty binder excludes this case.
- Empty V: its product is empty; it remains among the quantified tests.
- A = Spec Z: its identity atlas and every base-change identity satisfy the two
  sides. No requirement that arbitrary V be a scheme or an algebraic space appears.
- Non-quasi-separated A or V: finite unions of affine atlas charts suffice; only
  their product over the affine base needs to be affine. No intersection-of-opens
  or diagonal-quasi-compactness argument is used.
- Arbitrary stack and test universe bounds: v₁,w₁,v₂,w₂ are explicitly declared;
  test bounds contain the base site. There is no restriction on characteristic,
  genus, or finite type. `ULift ℤ` permits every scheme universe u.

Searches performed (not merely inherited from stage 1):

1. `msearch.py leanfinder`, query “An algebraic stack is quasi compact if and only
   if its structure morphism to Spec integers is quasi compact”: eight results,
   including `AlgebraicGeometry.compactSpace_iff_quasiCompact` and
   `quasiCompact_iff_compactSpace`; all are scheme assertions, not this stack fact.
2. `msearch.py loogle`, query `"compactSpace_iff_quasiCompact"`: exactly that
   scheme-only theorem. It does not state the present algebraic-stack criterion.
3. `msearch.py grep`, query
   `compactSpace_iff_quasiCompact|quasiCompact.*[Ss]tack|[Ss]tack.*quasiCompact`:
   one Mathlib hit, the scheme terminal-map criterion.
4. `msearch.py leansearch`, query “An algebraic stack is quasi compact if and only
   if its structure map to the spectrum of the integers is quasi compact”:
   eight scheme-morphism results; no exact match.
5. `rg` of `lean/WeilConjectures`, by the item id and the terms
   `IsQuasiCompactModuli`, `IsQuasiCompactAlgebraicModuliMap`, and
   `moduliBaseStructure`: no declaration for this theorem upstream.
6. `rg` of `lean/Sheaf` for these predicates, structural maps, and absolute
   quasi-compactness criteria found StackQcqsMorphism and the existing
   `moduliBaseStructure` in RelativeModuliInertia, which are reused. The only
   theorem-level item reference is the consumer AlgebraicStackQcqsPermanence's
   proof docstring, not an existing statement. Searching the proposed full name
   in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found none.

Server compilation via scompile.py passed for the delivered statement, with no
errors or warnings. The item copy changes only lean and stmt_deps (the added
landed structural-map owner). No new definition nodes or dependency repairs are
needed. There is no disputed statement or source fault.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
