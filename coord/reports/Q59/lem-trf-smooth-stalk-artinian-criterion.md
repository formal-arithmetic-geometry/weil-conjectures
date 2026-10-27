## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothStalkArtinianCriterion` states
`AlgebraicGeometry.noetherian_stalks_and_smooth_near_of_artinian_local_lifting`.
Its sole proof is `sorry`; no definitions or additional theorem statements are introduced.
The node is unchanged except for its `lean` record. No statement correction or dependency
repair is necessary.

Clause-by-clause correspondence:

- Schemes and their morphism: `{Z T : Scheme.{u}} (f : Z ⟶ T)`.
- Locally of finite type: `[LocallyOfFiniteType f]`; locally Noetherian target:
  `[IsLocallyNoetherian T]`. These are precisely the two geometric assumptions.
- Prescribed point: `(z : Z)`; the point `t` is the actual image `f z`.
- The rings `A` and `B` are literally `T.presheaf.stalk (f z)` and
  `Z.presheaf.stalk z`. The ring map is always `(f.stalkMap z).hom`, rather than
  an independently supplied local map.
- The asserted Noetherian stalk setup is the first two conjuncts,
  `IsNoetherianRing (T.presheaf.stalk (f z))` and
  `IsNoetherianRing (Z.presheaf.stalk z)`. They are asserted before the implication
  containing the lifting assumption, so they do not depend on that assumption.
- Stalk locality and nonzero rings come from the scheme's inherited locally ringed
  space instances. `IsLocalRing` extends `Nontrivial`; it is the unique-maximal-ideal
  notion. The actual stalk map has Mathlib's `Scheme.Hom` locality instance.
- Every test pair is quantified as `(C' C : Type u)` with `[CommRing C'] [CommRing C]`,
  `[IsArtinianRing C'] [IsArtinianRing C]` and `[IsLocalRing C'] [IsLocalRing C]`.
  Thus the rings are commutative, Artinian, local, and nonzero. Artinian means DCC
  on ideals via Mathlib's module Artinian predicate. The test universe is the scheme
  ring universe, as in the recorded scheme criterion; it is not an independent smaller
  universe which could make the tests vacuous.
- The small extension is `(q : C' →+* C)` with `Function.Surjective q`.
- Its annihilation condition is exactly
  `∀ r ∈ IsLocalRing.maximalIdeal C', ∀ x ∈ RingHom.ker q, r * x = 0`.
- Its dimension-one condition is
  `Nonempty ((RingHom.ker q) ≃ₗ[C'] IsLocalRing.ResidueField C')`.
  The right-hand `C'` action is the canonical quotient action. This says precisely
  that the kernel, with its inherited `C'` action, is the one-dimensional residue-field
  module. Given annihilation, the action descends uniquely to the quotient field,
  and a basis of cardinality one is equivalent to such an isomorphism. Conversely,
  an isomorphism supplies the canonical quotient action and dimension one. No
  coefficient-field section or auxiliary scalar action is assumed.
- The pair consists of `(a : T.presheaf.stalk (f z) →+* C')` and
  `(b : Z.presheaf.stalk z →+* C)`, with `IsLocalHom a` and `IsLocalHom b`.
  For local rings Mathlib's `IsLocalHom` is equivalent to inverse image of the
  maximal ideal being the maximal ideal (`IsLocalRing.local_hom_TFAE` and
  `IsLocalRing.maximalIdeal_comap`). Thus this is the stated locality condition.
- Compatibility is `q.comp a = b.comp (f.stalkMap z).hom`, with the same actual
  stalk homomorphism as in the node.
- The lift is `∃ c : Z.presheaf.stalk z →+* C', IsLocalHom c ∧ q.comp c = b ∧
  c.comp (f.stalkMap z).hom = a`. This includes locality and both triangular equations.
- The conclusion after the lifting implication is
  `∃ U : Z.Opens, z ∈ U ∧ Smooth (U.ι ≫ f)`: an open subscheme containing the
  specified point, whose restriction of the original morphism is smooth over `T`.

Recorded statement dependencies, whose full signatures and docstrings were read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.

All recorded proof dependencies are imported, publicly where already statement dependencies:

- `Algebra.FiniteType.isNoetherianRing` in `Mathlib.RingTheory.FiniteType`.
- The affine-open stalk localization and germ declarations in
  `Mathlib.AlgebraicGeometry.AffineScheme`, including
  `IsAffineOpen.fromSpec_app_self`, `IsAffineOpen.isOpenImmersion_fromSpec`,
  `IsAffineOpen.fromSpec_primeIdealOf`, `IsAffineOpen.isLocalization_stalk`.
  The open-immersion stalk isomorphism and `Scheme.Hom.germ_stalkMap` are available
  through these imports and `Mathlib.AlgebraicGeometry.Scheme`.
- `IsLocalization.isNoetherianRing` in `Mathlib.RingTheory.Localization.Submodule`.
- `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`.
- `AlgebraicGeometry.smooth_near_iff_artinian_lifting_at_point` in
  `WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint`; its exact live
  statement was read, including its `Type u` Artinian tests and length-one kernel.
- `AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso` and
  `AlgebraicGeometry.Spec.algebraMap_stalkIso_inv` in
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing` in `Mathlib.AlgebraicGeometry.Stalk`;
  its full map and the closed-point stalk isomorphism were read.
- `AlgebraicGeometry.Scheme.Hom.germ_stalkMap` and `Scheme.Hom.stalkMap_comp`
  in `Mathlib.AlgebraicGeometry.Scheme`.

The source was checked directly in `literature/stacks-project/more-morphisms.tex`,
`lemma-lifting-along-artinian-at-point`, and `literature/stacks-project/algebra.tex`,
`definition-small-extension`. The source uses length-one kernels; the residue-field
module condition here is equivalent and follows the node's explicit formulation.

Edge cases checked before writing:

- An empty source has no choice of `z`, hence asserts no nonexistent neighbourhood.
  A nonempty source point cannot map to an empty target.
- Scheme stalks and Artinian local test rings are nonzero through `IsLocalRing`;
  the zero ring is correctly excluded without an extra assumption.
- The zero kernel of an isomorphism, including the identity extension, cannot be
  isomorphic to the nonzero residue field. Such maps are correctly excluded from
  small extensions.
- For dual numbers over a field, the quotient to the field has the expected
  one-dimensional annihilated kernel, so these basic tests are included.
- The small extension `ℤ/4 → ℤ/2` is included: its kernel is isomorphic as an
  `ℤ/4`-module to the residue field. A field embedding into `ℤ/4` is neither needed
  nor assumed. Mixed and positive characteristic are retained.
- No finite presentation of the stalk map, closedness of `z`, fixed residue field,
  residue-field isomorphism, or reducedness is imposed.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder` with query “Smoothness at a point from lifting local
  ring homomorphisms out of the stalks through small Artinian local ring extensions”:
  eight results, including affine smoothness and formal-smooth-stalk criteria;
  no exact stalk small-extension statement.
- `msearch.py ... loogle "IsLocalHom, IsArtinianRing"`: zero hits.
- `msearch.py ... grep 'small_extension|artinian_lifting|smooth.*[Ss]talk|[Ss]talk.*smooth'
  AlgebraicGeometry`: five hits in Mathlib's smoothness module, on formal smoothness
  of stalks, not the Artinian local-map criterion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id and for
  `SmallExtension|smallExtension|small_extension|artinian_lifting|ArtinianLifting|stalk.*[Ss]mooth|[Ss]mooth.*stalk`:
  no exact declaration; the upstream scheme-square criterion was found and reused
  as a proof dependency, while the fixed-residue test theorem has different tests.
- Direct reads of Mathlib local ring homomorphisms and residue-field modules confirm
  existing notions suffice. No new node or duplicated definition is needed.

Validation: prescribed `scompile.py` compiled both the sandbox and intended library
module successfully (2.9 s and 2.0 s), with no error or warning. `autoImplicit false`
ensures all variables and universes are explicitly bound.

## Second reading by Q59

A separate second pass by the same dispatcher-started worker reopened the node and the
Lean file. No second agent was started, as required by this assignment. The review
matched the hypotheses and conclusions above, particularly the actual stalk map,
locality of all three test maps, both lift equations, the unconditional Noetherian
stalk assertions, and the final restriction `U.ι ≫ f`. It checked that the residue
field has its quotient `C'`-module structure, not a chosen coefficient-field structure,
and that the isomorphism is existential rather than a specified basis. The Noetherian
conjuncts precede the lifting implication to retain their unconditional status.
No mismatch, statement dispute, added hypothesis, or omitted clause was found;
no changes were needed after this second pass.
