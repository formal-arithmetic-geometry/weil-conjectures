## Worker report

The module `Sheaf.AlgebraicGeometry.InertiaFreeCoarseScheme` states
`AlgebraicGeometry.inertia_free_coarse_scheme`, with its single proof `sorry`.
The node's natural-language statement, proof, and proof dependencies are unchanged.
There are no new definitions, auxiliary theorems, new nodes, or dependency repairs.
Three already-landed definition owners are added to `stmt_deps` for the existing
smoothness, finite-type predicates, and canonical structural functor used below.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the arbitrary total category
  over all S-schemes is `F : BasedCategory.{v, w} (Over S)`. The independently
  bound total-category universes do not restrict the base or the test schemes.
- The DM hypothesis is `hF : IsDeligneMumfordModuliStack F`. Its definition
  includes fibred-in-groupoids, etale descent, representable diagonal, and
  a surjective etale scheme atlas. No stabilizer, finiteness, or separation
  property is smuggled into this hypothesis.
- The S-scheme C is `C : Over S`; its structure morphism is `C.hom`. The
  specified coarse map is `c : BasedFunctor F (discreteModuli (yoneda.obj C))`.
  `hc : IsCoarseModuliScheme F C c` is exactly the recorded coarse convention:
  universal for every algebraic-space target and bijective on geometric
  isomorphism classes. The universal property is not assumed only for schemes.
- The geometric inertia hypothesis is `hgeom`: every `Ω : Type u`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, every `a : Spec (.of Ω) ⟶ S`, every object of the actual
  fibre `Functor.Fiber F.p (Over.mk a)`, and every endomorphism `α` satisfies
  `α = 𝟙 x`. The fibres are groupoids, so these are precisely automorphisms.
  This is the identical field/test universe convention used by the recorded
  geometric-inertia dependency, not an independent smaller field universe.
- The assertion about the SPECIFIED morphism is `c.toFunctor.IsEquivalence`.
  Since c is already a functor over Sch/S, this is an equivalence over the
  base (its quasi-inverse can be taken over the base for fibred groupoids).
- Full-groupoid representability is also spelled out as
  `IsRepresentedByScheme F C`. This is the existing predicate asserting an
  equivalence from the discrete Yoneda groupoid of C to F, retaining arrows.
- The assertion for every S-scheme, including nonreduced ones, is the third
  conjunct, `∀ (T : Over S) (x : Functor.Fiber F.p T) (α : x ⟶ x), α = 𝟙 x`.
  There is no field, reducedness, affine, or finiteness restriction on T.
- The final "if" is a conditional fourth conjunct. `IsSmoothModuliStack F`
  uses a smooth surjective scheme atlas with smooth structural composite.
  `IsLocallyFiniteTypeModuliMap (moduliBaseStructure F)` and
  `IsQuasiCompactModuliMap (moduliBaseStructure F)` are the existing DM
  finite-type ingredients. Etale-atlas local-finite-type tests agree with
  smooth-atlas tests on DM stacks. Quasi-compactness is explicitly the
  existence of a quasi-compact etale atlas after every affine scheme base
  change; for DM stacks this is equivalent to quasi-compactness of those
  point spaces. In particular it is not replaced by local finite type.
- The consequent is `Smooth C.hom ∧ LocallyOfFiniteType C.hom ∧
  QuasiCompact C.hom`. These are the exact ordinary scheme properties of
  the original node. No smoothness or finite-type assumption is needed for
  the first three conclusions, and the final conditional includes both
  properties together as the node requests.

Recorded dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraic-closure
  node's `mathlib_match` expressly names this closed-field notion).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.discreteModuli`, `IsDeligneMumfordModuliStack`,
  `IsCoarseModuliScheme`, `IsRepresentedByScheme`, and the fibre/groupoid
  conventions. The complete signatures and docstrings were read, including
  the specified base-change projection and actual induced fibre functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`;
  its presheaf morphisms, representability, etale and surjective chart tests.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsSmoothModuliStack` and `IsSmoothModuliAtlas`.
  Its owner `def-sfb-algebraic-moduli-stack` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.IsLocallyFiniteTypeModuliMap`, `IsQuasiCompactModuliMap`;
  owner `def-sfb-dm-stack-morphism-properties` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`:
  `CategoryTheory.moduliBaseStructure`, the actual projection F.p into
  the identity category over Sch/S. Owner `def-sfb-relative-moduli-inertia`
  is added to `stmt_deps`. There is no arbitrary structure map parameter.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- Proof imports: `Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial`,
  `AlgebraicGeometry.dm_geometric_inertia_trivial`;
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`,
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`;
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective`.
  The unstated proof dependency `lem-sfb-stack-finite-type-calculus` has no
  recorded module to import, and `scompile.py --source
  Sheaf.AlgebraicGeometry.StackFiniteTypeCalculus` confirmed no such published
  module. It supplies no missing notion for this signature: the necessary
  predicates are already owned by the landed definition nodes listed above.
  Its planned use remains explicitly described in proof step 5.

Source checked: Stacks `algebraic.tex`,
`proposition-algebraic-stack-no-automorphisms` (04SZ), including its
stack-in-setoids/algebraic-space equivalence; the node's explicit coarse
inverse argument; 05B5 in the published smoothness descent declaration;
and the current blueprint's direct-image proof paragraph (3) under
`literature/blueprint/latest/`. The module docstring contains all five node
proof steps and names their dependencies.

Edge cases checked: the empty stack and empty representing scheme; an already
representable stack h_C; a nonempty BG with nontrivial geometric G (excluded by
hgeom); infinitesimal B(alpha_p) (excluded by the DM condition); arbitrary
nonreduced T, in particular dual numbers; arbitrary non-Noetherian base S;
and non-quasi-compact stacks. For the last case the equivalence still applies,
while the finite-type implication requires its separate quasi-compactness
antecedent. No genus, level, characteristic, field-base, or separatedness
hypothesis from neighboring moduli applications is added.

Searches (2026-10-24):

- `msearch.py ... leansearch "A Deligne Mumford stack with trivial geometric
  automorphisms is equivalent to its coarse moduli scheme"`: eight hits,
  all ordinary scheme smoothness/etaleness/isomorphism material, no match.
- `msearch.py ... leanfinder` with that same query: eight hits, scheme
  strict initial objects, affine schemes, etale schemes and stalkwise
  isomorphism criteria; no statement about coarse groupoid equivalence.
- `msearch.py ... loogle "IsCoarseModuliScheme, IsDeligneMumfordModuliStack"`:
  zero hits, unknown identifier IsCoarseModuliScheme in Mathlib.
- `msearch.py ... grep "CoarseModuli|DeligneMumford"`: zero Mathlib hits.
- `rg -n` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `inertia_free_coarse_scheme`,
  `inertiaFreeCoarseScheme`, and the blueprint id: no existing statement.
  The broader `CoarseModuli|DeligneMumford|coarse|inertia` searches found
  the recorded definitions, geometric-inertia criterion and the different
  finite-cover coarse theorem. None asserts the present statement.
- Signature searches for stack smoothness, local finite type,
  quasi-compactness and `moduliBaseStructure` found the three landed owning
  definition modules reused here. No parallel definition is introduced.

No statement dispute or correction is needed. The added stmt_deps only attach
already existing notions used to render the unchanged statement.

Validation: `scompile.py` compiled the module cleanly in sandbox and library
module modes. `deliver2.py Q118 lem-sfb-inertia-free-coarse-scheme --no-push`
printed OK: commit d8df260426d passes the preflight and compiles. The final
delivery uses the same prescribed wrapper. A local read-only check confirmed
that the recorded signature is verbatim, the module has one sorry, all lines
are at most 100 characters, and only lean and stmt_deps differ from the node.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
