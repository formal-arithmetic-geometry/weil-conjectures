## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinSinglePointObstruction` states
`AlgebraicGeometry.artin_single_point_obstruction`, with `sorry` as its entire proof.
It introduces no definitions or auxiliary theorems. The node's statement and proof
are unchanged. Its statement dependencies gain the already landed
`def-sfb-stable-pointed-moduli-groupoids`, which owns the existing general predicate
`CategoryTheory.IsFibredInGroupoids` used here.

Source read: Stacks `artin.tex`, Tag 0G2J (`lemma-single-point`), statement and proof.
The DAG already spells out the affine ring construction and the Artinian lifting
condition, so no completion or formal-object construction is needed to state it.
The `CompactObject` example at the prescribed Sheaf path is withdrawn; its node
points to the upstream `WeilConjectures.CategoryTheory.CompactObject`. The new file
uses the required module header, public section, explicit universes and source
and proof docstrings.

Hypotheses, matched individually:

- Commutative Noetherian base: `(Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]`.
  The base scheme is literally `Spec (.of Λ)` throughout.
- Schemes over this base: `Over (Spec (.of Λ))`. The big fppf site's underlying
  category is exactly this category. A fibred category over a site is over its
  underlying category; no descent condition is asserted by the node or added here.
  The site's existing module is imported.
- Category fibred in groupoids: `F : BasedCategory.{v, w} ...` and
  `hF : IsFibredInGroupoids F`. Fibres are the existing `Functor.Fiber F.p T`;
  `F.p.IsHomLift f a` means the actual total-category arrow lies over `f`.
  Mathlib's fibre construction retains automorphisms. The existing predicate
  requires base-arrow lifts and strong cartesianness of every arrow, which gives
  the coherent pullbacks of the node, without imposing a chosen cleavage.
- Universe convention: `u` is the ring/scheme universe; all test rings and the
  output ring are in that same universe. `v` and `w` are independent total-category
  morphism and object universes. No size equality with the scheme universe is imposed.
- Square-zero gluing: `hglue` quantifies over arbitrary base algebras and their
  cospans `A → B ← B'`, with the right leg onto and kernel square zero. `algSpec`
  is the existing contravariant affine base-algebra functor. Given a pushout of
  these affine schemes, `hglue` asks that every lifted span has a pushout over it
  in the total category. This is the invariant, cleavage-free expression of the
  displayed equivalence of groupoids, not just existence of a glued isomorphism
  class. A span `z → xA`, `z → xB'` specifies the actual identification of the two
  restrictions to B. A total-category pushout includes uniqueness for all maps
  to every test object, hence full faithfulness as well as essential surjectivity.
  Conversely the groupoid comparison equivalence supplies that pushout: for a
  compatible cocone to an object over Q, first descend the base maps uniquely
  through the scheme pushout, pull the object back to the pushout, and use full
  faithfulness in its fibre. Every triple admits the displayed span by fibredness.
  Quantifying over any pushout is equivalent to the node's canonical affine
  pushout by uniqueness of pushouts. No stack/descent or limit-preserving
  assumption occurs.
- Affine finite type U: `R₀ : CommAlgCat.{u} Λ`, with `U = Spec (.of R₀)` as the
  underlying scheme of `(algSpec (.of Λ)).obj (op R₀)`, and instances
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism.
- Object and finite type point: `x : Functor.Fiber ...` and `u₀ : Spec (.of R₀)`;
  `hft` is exactly the conjunction of locally finite type and quasi-compact for
  the canonical `fromSpecResidueField u₀` morphism.
- Nonversality: `hnonversal` negates the complete inline lifting condition.
  `A'`, `A` are commutative Artinian local rings; `q` is onto with nilpotent kernel.
  Their base-algebra structures are encoded equivalently by `s'` and its
  composite with `Spec.map q`. The surjection `ρ : A → κ(u₀)` specifies the
  residue identification: because A is local and the target is a field, its
  kernel is the unique maximal ideal. The composite `ρ q` supplies the common
  marking for A', whose kernel is also maximal. Thus no coefficient-field
  embedding or splitting is assumed. The arrow `a` is over the base and the
  equality `Spec.map ρ ≫ a.left = ...fromSpecResidueField u₀` says it reduces to
  precisely the marked point. `yA'` is the given object; the arrows `b`, `c`
  through `yA` retain its specified restriction isomorphism with the pullback
  of x. The conclusion quantifies over a base-map lift `a'` and arrow `d`,
  with `Spec.map q ≫ a'.left = a.left` and `b ≫ d = c`. The latter is precisely
  extension of the given isomorphism. Surjections between these marked local
  rings are automatically local and respect the induced residue identifications.

Conclusion, matched clause by clause:

- A commutative base algebra R: the existential `R : CommAlgCat.{u} Λ`.
- A surjection `R → R₀` and square-zero ideal: `p : R ⟶ R₀`,
  `Function.Surjective p.hom`, and `RingHom.ker p.hom.toRingHom ^ 2 = ⊥`.
- The induced first order thickening: the base arrow `j` is tied by equality
  to `(algSpec (.of Λ)).map p.op`, and `IsFirstOrderThickening j.left` is the
  dependency's existing sheaf-ideal predicate. Thus j is not an arbitrary map.
- The ideal is κ(u₀) as an R₀-module: the additive equivalence `e` and
  `e (r • i) = evaluation (p.hom r) * e i`. Here evaluation is
  `Spec.preimage (...fromSpecResidueField u₀)`, the actual canonical ring map
  `R₀ → κ(u₀)`. This is precisely R₀-linearity: since p is onto and its kernel
  squares to zero, the usual R-action on its kernel factors through R₀, and
  the displayed equation for all r checks linearity for every scalar of R₀.
  This avoids installing an arbitrary module structure on the kernel. It is
  neither only an additive isomorphism nor an isomorphism for an unrelated action.
- Object over T and theta: `y : Functor.Fiber F.p (algSpec ... R)` and `c : x.val → y.val`
  over j. All arrows of this fibred groupoid are cartesian; c is exactly the
  specified isomorphism `theta : x ≅ j* y`.
- No local retraction with compatible isomorphism: for each actual open W of
  `Spec R` containing `j.left u₀`, `yW` and `aW` express restriction of y to W.
  `z` is over the pullback `U ×_T W = U ∩ W`; `aU` and `aUW` lie over its two
  projections. The equation `aU ≫ c = aUW ≫ aW` says that `aUW` is the restriction
  of the specified arrow c. The conclusion forbids any `beta : yW.val → x.val`
  with `aUW ≫ beta = aU`. This is exactly the node's final equivalent formulation.
  Applying the projection to this equation gives the identity for a retraction
  on `U ∩ W`; the arrow beta over that retraction is the isomorphism required in
  the preceding formulation, with restriction theta inverse. Quantification
  over all choices of restrictions changes nothing: they exist by hF and are
  uniquely isomorphic respecting their arrows. Nothing is required on an
  unrelated neighbourhood or for an arbitrary unconstrained map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
- The added landed dependency's module
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `CategoryTheory.IsFibredInGroupoids`.
- `Mathlib.AlgebraicGeometry.Group.Affine`: `algSpec` supplies canonical base maps;
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage` is used for evaluation.
- Mathlib's existing `BasedCategory`, `Functor.Fiber`, `Functor.IsHomLift`,
  `IsPushout` and `pullback` supply the total-category and restriction language.
- Proof-only import: the recorded module
  `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory` for
  `def-sfb-artin-deformation-test-category` (its `TestCategory` and `IsSmallExtension`).
  The proof dependency `lem-sfb-artin-local-test-algebra` has no Lean record yet,
  so it has no module to import. The source proof is recorded completely in the
  theorem docstring. Closed immersions and all other recorded proof dependencies
  are already available through the statement imports.

Edge cases checked:

- Empty U or the zero base ring gives no point u₀; no nonempty scheme or field
  hypothesis is added. An empty W cannot satisfy the neighbourhood condition.
- A zero kernel test is an isomorphism and cannot supply a nonversality witness.
  The conclusion's ideal is nonzero because it is isomorphic to a residue field.
- No reducedness, characteristic restriction, separability, finite residue degree,
  stack descent, or coefficient-field section is assumed.
- For the terminal fibred groupoid over a field k and
  `U = Spec(k[t]/(t²))`, the identity map of the Artinian ring does not lift through
  `k[t]/(t³) → k[t]/(t²)`. Any possible lift of t is `t + c t²`, whose square is
  nonzero t² in every characteristic. The latter ring gives the promised witness,
  with square-zero ideal `(t²) ≅ k` and no local retraction. This also checks the
  orientation of the arrow equation and the residue-field scalar action.
- The universe of test algebras is the same as that of Λ and R₀, so tests cannot
  become vacuous through a smaller independent universe.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `Nonversality at a finite type point is detected by a square zero thickening with kernel the residue field`:
  eight results on formal smoothness/unramifiedness and residue fields; no theorem
  on fibred-groupoid nonversality or this obstruction.
- `msearch.py ... loogle` with query `"versal"`: twelve unrelated Ore-localization
  universal-map results; no exact statement.
- `msearch.py ... grep` with query
  `IsVersal|[Ff]ibredInGroupoids|[Ff]iberedInGroupoids|singlePointObstruction`:
  zero Mathlib hits.
- `rg` of `lean/WeilConjectures` for the item id: no hits. Exact declaration-name
  searches in Mathlib, WeilConjectures and `dag/lean_names_upstream.json`: no match.
- `rg` of `lean/Sheaf` for fibred-groupoid and versality language found the
  general existing `IsFibredInGroupoids`, reused here; `ProperCurveVersality`
  concerns only proper-curve families; `StackVersalFiniteResidueExtension`
  concerns formal objects; `ArtinRepresentableDiagonalCriterion.IsVersalAt`
  and its `RimSchlessinger` concern only the integer base and the latter only
  Artinian finite-type diagrams. Their full definitions and docstrings were read;
  none states this theorem or provides its arbitrary-base, arbitrary-algebra
  gluing hypothesis. The two lifting hypotheses are therefore written explicitly,
  using the existing total-category primitives, without a second named definition.

No statement dispute or source correction was needed. All variables and universes
are explicitly bound; every theorem proof is `sorry`. Validation uses only the
prescribed per-file `scompile.py` and delivery wrappers.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
