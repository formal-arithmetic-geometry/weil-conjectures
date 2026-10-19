## Worker report

The module `Sheaf.CategoryTheory.Sites.PullbackInjectiveEvaluationAcyclic` states
`CategoryTheory.sitePullback_injective_evaluation_isZero`. Its only theorem has
whole proof `by sorry`; it introduces no definition and proves nothing. The node
changes only in `lean`. Read the complete source lemma and proof in
`literature/stacks-project/sites-cohomology.tex`, label
`lemma-pullback-injective-pre-limp` (Stacks 0D6X), lines 9277–9313.

Hypothesis and conclusion correspondence:

- Small sites in a common universe: `{C D : Type u} [SmallCategory C]
  [SmallCategory D]`, `(J : Precoverage C) (K : Precoverage D)` and
  `hJ : J.IsSiteForCoverings`, `hK : K.IsSiteForCoverings`. These are the
  dependency's current actual-covering axioms, without the old extra indexed
  composition class. Abelian sheaves take values in `AddCommGrpCat.{u}`.
- The functor `u : C → D` is `(f : C ⥤ D)`.
- Stacks continuity 00WV(a) is `hcover`, mapping covering presieves to covering
  presieves; 00WV(b) is `hpullback`, preserving the pullback of each covering
  arrow against every arrow to the same object. Neither condition is discarded
  in favor of Mathlib's sheaf-theoretic continuity.
- `[f.IsContinuous J.toGrothendieck K.toGrothendieck]` is the sheaf-theoretic
  interface of that same continuity, needed to type Mathlib's functor. It is a
  consequence of the site's covering continuity, not a further mathematical
  restriction. On a source covering, preservation of covering pullbacks
  transports the target sheaf equalizer, proving that precomposition is a sheaf;
  this is precisely Stacks 00WW. The generated-topology sheaf condition is the
  equivalent covering-presieve condition. In particular no preservation of all
  finite limits of the site is assumed.
- Cocontinuity, and only part (1) of the special-cocontinuous dependency, is
  `[f.IsCocontinuous J.toGrothendieck K.toGrothendieck]`. There are no local
  fullness, local faithfulness, cover-density or equivalence hypotheses.
- The geometric morphism associated to `f` has canonical inverse image the
  precomposition functor `f.sheafPushforwardContinuous AddCommGrpCat.{u}
  J.toGrothendieck K.toGrothendieck`. Despite Mathlib's name, this is inverse
  image for the cocontinuous morphism (00XR); its value is literally
  `f.op ⋙ I.obj`, with the original abelian operations and restriction maps.
  This uses the dependency adjunction's precomposition identification and the
  abelian operations, exactly the first proof step. The geometric morphism is
  specified canonically by `f`, so there is no independent `g` or arbitrary
  functor datum that could lose the association. The conclusion concerns this
  canonical model of `g⁻¹ I`, hence all canonically isomorphic choices.
- `I` injective in `Ab(D)`: `(I : Sheaf K.toGrothendieck AddCommGrpCat.{u})
  [Injective I]`, using the dependency's Mathlib `Injective`.
- Every site object: unrestricted `(U : C)`.
- Every integer `p > 0`: `(p : ℕ) (hp : 0 < p)`. Ordinary right derived
  functors are naturally indexed, and the positive naturals correspond
  bijectively to the positive integers. This omits no degree named in the node.
- `H^p(U,g⁻¹ I) = 0`: `IsZero` of the `p`-th ordinary `rightDerived` of
  `sheafToPresheaf ... ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)`,
  evaluated at the canonical inverse image. This is exactly evaluation on
  abelian sheaves and its ordinary right derived functor; no total derived
  category or Ext normalization is substituted. The standard Grothendieck
  abelian sheaf instances supply injective resolutions; no extra existence
  hypothesis or chosen Abelian structure is imposed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its docstring also specifies
  Mathlib sheaves and cohomology as the remaining interfaces of the node.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`,
  `CategoryTheory.Functor.IsSpecialCocontinuousForCoverings`; its docstring
  identifies clause (1) with Mathlib `Functor.IsCocontinuous`. Read the current
  source through `scompile.py --source` because the older checkout lacks it.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`: inverse/direct functors, adjunction and
  inverse-image finite-limit preservation. Its canonical inverse-image model
  here is supplied by 00XR, rather than an arbitrary datum.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`; also read the full signature and docstring of
  `InjectiveResolution` in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- `def-weil-size-convention` is explicitly a convention, not a Lean object;
  its recorded instruction is implemented by the explicit common universe.

The four proof steps are present in the theorem docstring: the canonical
precomposition identification, induction identifying covering nerves and their
projections, the Cech-complex isomorphism and injective Cech vanishing, and the
all-objects/all-coverings Cech criterion. Recorded proof-dependency modules are
imported without `public`: the current `ContinuousCocontinuousToposAdjunctionForCoverings`,
and upstream `SiteCechComplex`, `SiteInjectiveCechAcyclic` and
`SiteCechVanishingCriterion`. The last two sources were read through
`scompile.py --source`, ensuring the current upstream versions are imported and
avoiding the retired library-side duplicate declarations.

Edge cases checked: an empty source category gives no `U` and is allowed; an
empty covering gives empty products and is not excluded by any Nonempty
hypothesis; all covering pullbacks and higher fibre products are restricted to
covering arrows, with no global pullback assumption; the zero sheaf and the
identity functor are included; `p = 1` is included and `p = 0` correctly excluded;
no terminal object, nonempty category or special-cocontinuous equivalence is
assumed. Both site and coefficient universes are the node's common universe.
The inverse image is not assumed injective.

Searches for an existing statement (all via the authorized wrapper where noted):

- LeanFinder: `Inverse image by a continuous cocontinuous site functor of an
  injective abelian sheaf has vanishing positive right derived evaluation`.
  Eight hits: injective derived vanishing, Grothendieck sheaves, and local
  injectivity of maps; none concerns the inverse-image object's evaluation.
- Loogle: `"Sheaf", "Injective", "rightDerived"`. Zero hits.
- LeanSearch: `continuous cocontinuous inverse image injective sheaf acyclic
  evaluation`. Eight hits, notably `sheafAdjunctionCocontinuous` and the
  continuity classes; none states the desired higher vanishing.
- Mathlib grep through `msearch.py`, query
  `cocontinuous.*(injective|acyclic)|isZero_rightDerived_obj_injective`,
  subdirectory `CategoryTheory`. Three hits: `isZero_rightDerived_obj_injective_succ`
  and local injectivity of morphisms, not acyclicity of inverse images.
- `rg` on the upstream `WeilConjectures` and side `lean/Sheaf` trees for the node
  id, cocontinuous/injective combinations, and evaluation acyclicity. The
  ringed-site direct-image result has additional morphism-of-sites/scalar data
  and different objects; it is not this statement. No exact existing match.
- `rg` of the proposed declaration name in `dag/lean_names_upstream.json`,
  Mathlib, upstream and side source: no name collision.

Validation: prescribed `scompile.py Q12
lem-trf-site-pullback-injective-evaluation-acyclic <module>` passed both sandbox
and library-path compilation, without errors or warnings.

No new nodes, dependency repairs, statement correction, or disputed statement.

## Second reading by Q12

Self-check after compilation, with the original node and the complete module
open; the maintainer supplies the independent review required by this direct
worker brief. I checked both site binders, covering axioms, both continuity
clauses, cocontinuity alone, the actual injective sheaf category, unrestricted
source object, positive degrees, canonical inverse-image variance, and the
ordinary derived evaluation expression against the node. In particular the
Mathlib functor's name does not reverse the inverse image: it takes sheaves on D
to sheaves on C by `f.op ⋙ _`. The typeclass continuity binder is the interface
of the already stipulated covering continuity, not an assumption that `f`
preserves all site finite limits. The derived functor is taken on C after
pullback, not the derived functor of evaluation on D or of the pullback itself.
No mismatch or change was found during this second reading.
