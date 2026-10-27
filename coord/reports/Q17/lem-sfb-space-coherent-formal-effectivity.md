## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentFormalEffectivity` states
`AlgebraicGeometry.AlgebraicSpace.coherentFormalRestriction_isEquivalence`, exactly
the fixed-A groupoid equivalence of Stacks 08W9, using Situation 08KB. Nothing is
proved. All four named theorem proofs are `sorry`; every definition has real data.
The original statement, proof, proof dependencies, and other existing node fields
are unchanged. Only `lean` and the permitted additional statement dependencies change.

The source was read in quot.tex, situation-coherent and lemma-coherent-existence,
and artin.tex, definition-formal-objects (07X4) and equation-approximation (07X6).
The source explicitly defines an S-algebra as a ring with a map Spec(A) → S, so
the binder `a` permits an arbitrary scheme base, without requiring S affine.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base is `S : Scheme.{u}`. The spaces are `X B : AlgebraicSpace S`, the
  existing full subcategory of fppf sheaves with representable diagonal and an
  etale surjective scheme atlas. `f : X ⟶ B` is the required morphism.
- Finite presentation is `hfp : ProperQuotFinitePresentation f`: local finite
  presentation on etale charts, quasi-compactness, and quasi-compact diagonal.
  Separatedness is independently `hsep : MapIsSeparated f`, the representable
  closed-immersion diagonal. Neither properness nor flatness of f is assumed.
- Local Noetherianity is `[IsLocallyNoetherian S]`, Mathlib's every-affine-open
  definition, equivalent to the node's affine-Noetherian-cover definition by
  `isLocallyNoetherian_iff_of_affine_openCover`.
- A is `A : Type u` with `[CommRing A]`, `[IsLocalRing A]` and
  `[IsNoetherianRing A]`. Its unique maximal ideal is
  `IsLocalRing.maximalIdeal A`. The specified S-algebra structure is the scheme
  map `a : Spec (CommRingCat.of A) ⟶ S`.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`, the ordinary
  separated and complete maximal-ideal-adic condition. This is equivalently the
  displayed isomorphism with the inverse limit of the positive quotients.
- `hres` is `LocallyOfFiniteType` AND `QuasiCompact` of the actual composite
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ≫ a`.
  Thus it says finite type over S of Spec(A/m), including quasi-compactness;
  there is no chosen coefficient field or additional field extension.
- The objects (b,M) are the existing `CoherentModuli f`. Its `base` is a
  `ProperQuotTest B`, i.e. a scheme over S with its map b to B, and its `module`
  lives on `properQuotFibre f base`, the actual sheaf fibre product X ×_B T.
  Its `quasiCoherent` and `finitePresentation` fields use Mathlib's small-etale
  module predicates. Finite presentation is locally finite generators AND
  relations, not finite type alone.
- `CoherentModuli.flat` tests `Scheme.Modules.IsFlatOver` on every etale scheme
  chart via `schemeRestriction`. For quasi-coherent modules this is the recorded
  affine-local equivalent of stalk flatness over the base local ring.
- `CoherentModuli.properSupport` is verbatim the closed-carrier convention:
  there exist Z and a representable closed immersion i, `MapIsProper (i ≫ p)`,
  a quasi-coherent finite type module G on Z, and an isomorphism i_*G ≅ M.
  No properness of the whole ambient fibre is imposed.
- Arrows are `CoherentModuli.Hom`: a map of test schemes over B and the actual
  isomorphism `(moduleTensorPullback (properQuotFibreMap f base)).obj M₁ ≅ M`.
  The existing category uses the canonical normalized tensor identity and
  composition isomorphisms. Its fibre over T is Mathlib's `Functor.Fiber`, so
  vertical arrows and all automorphisms are retained.
- The source groupoid in the conclusion is
  `Functor.Fiber (CoherentModuli.category f).p (Over.mk a)`.
- `coherentAdicBase a n` is Spec(A/m^(n+1)) over S. The natural-number index
  0 is therefore positive power 1, with no extra Spec(A/m^0) level. Its transition
  from n to m for n ≤ m is Spec of the actual quotient factor homomorphism.
  The identity/composition/inclusion laws are stated as named theorem obligations.
- `FormalDiagram (CoherentModuli.category f) (coherentAdicTower a)` is the fibre
  of postcomposition on functor categories over that precise base diagram.
  A functor ℕ → CoherentModuli f specifies x_n and every transition with identity
  and composition laws; since its arrows already ARE pullback isomorphisms,
  these are precisely the systems in the node. A natural transformation over
  the identity tower is exactly a compatible family of vertical isomorphisms.
- `coherentFormalRestriction` is the canonical restriction functor, not an
  unconstrained functor whose equivalence could be asserted independently of
  restriction. `FormalRestrictionModel` retains arrows from every level to x,
  strongly cartesian over the actual closed inclusion, commuting with every
  transition and natural in x. Their universal property characterizes tensor
  pullback in this category. `coherentFormalRestrictionModel_exists` includes
  existence and uniqueness of a natural isomorphism preserving ALL these arrows.
  Its `.choose` is consequently the unique-universal-property choice authorized
  by AGENTS §5, rather than choice from mere existence of an unrelated object.
- The conclusion `.IsEquivalence` includes full faithfulness and essential
  surjectivity. In particular every formal system is isomorphic in the formal
  groupoid to the restriction of an actual object, respecting the specified
  transitions. The statement is stronger than mere existence of algebraizations
  on isomorphism classes, as the source requires.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
  The size-convention node has no declaration; explicit universe u is used for
  schemes and rings, and the existing site/module universe conventions are kept.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its Modules,
  `IsRepresentableWith`; `AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` for the sheaf products used by the existing family.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  `SheafOfModules.IsQuasicoherent`. The Mathlib finite-presentation predicate in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` is used unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, with their recorded universal properties and adjunction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, used by the existing CoherentModuli fields.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`,
  `properQuotFibre`, `properQuotFibreMap`, `properQuotSnd`,
  `ProperQuotFinitePresentation` and the proper-support conventions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`, `MapIsProper`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`; `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`: only the existing
  `CoherentModuli` definitions and category are consumed. The new definition
  record identifies their notion without a mathematical dependency on the
  downstream algebraicity theorem. Importing the effectivity module back into
  that shared module would create an import cycle; that proof import must be
  omitted under stages/2-statements §3(7). No source file is edited here.
- `Mathlib.CategoryTheory.FiberedCategory.BasedCategory`, `.Fiber`, `.Cartesian`
  and `Mathlib.CategoryTheory.Whiskering` give `BasedCategory`, `Functor.Fiber`,
  `Functor.IsStronglyCartesian`, and `Functor.whiskeringRight`. These construct
  the new formal category and its normalized restriction interface directly.

Already stated proof dependencies are imported plainly: SpaceQuasiCompactAffineTests,
SpaceLocalPropertiesChartTest, AlgebraicSpaceAdicFlatnessNearClosedFibre,
SpaceModuleBaseChangeFlatProperSupport and Mathlib.RingTheory.FiniteStability.
The recorded finite-presentation ring lemmas are `Algebra.FinitePresentation.baseChange`
and `Algebra.FinitePresentation.trans`. The complete-local-map-effectivity,
separated-fp-composition and supported-adic-existence proof nodes currently have
no Lean record, so no invented module is imported for them. They are needed only
for the postponed proof, not to state the present result. The full five-step
natural-language proof remains in the theorem docstring.

Edge cases checked before writing: A a field has m=0 and a constant positive
tower; Artinian A has an eventually constant tower; neither case is excluded.
The zero module and empty support satisfy the intended object conditions. Empty
X is allowed. Nonproper X with proper-support M is allowed. Nonrepresentable B
and nonaffine locally Noetherian S are allowed. No separatedness or finite-type
condition is imposed on B. There is no flatness assumption on f. IsLocalRing
excludes the zero ring because a ring with a unique maximal ideal is nontrivial.
All n≥1 occur, without any nilpotence assumption. A and schemes share universe
u, while module/category universes are inherited rather than forced equal;
the new category interface has six explicit independent universe levels.

Searches: msearch.py LeanFinder query “Grothendieck existence equivalence flat
coherent families proper support algebraic spaces” returned scheme Flat and
flat-descent/locality lemmas, no match. Loogle “Functor.IsEquivalence,
IsAdicComplete” returned zero hits/unknown identifier; no result was inferred
from that failed name query. Mathlib grep “coherent.*effectiv|coherent.*existence|
FormalSystem” returned unrelated coherent-site results. LeanSearch for the
coherent-family groupoid returned only module presentation declarations. Exact
query strings and full results for the new notions are in their mathlib_searches.
Project rg searches for CoherentModuli, CoherentFamily, Cohstack, FormalSystem,
FormalDiagram, FormalRestrictionModel and the item id found the existing family
category and base-specialized Artin FormalSystem types, but no formal-category
restriction construction or effectivity theorem. Both WeilConjectures and Sheaf
were searched. DAG searches and blueprint_refs.py search “formal objects” (zero
blueprint nodes) and “coherent” (166 candidates inspected by relevance) found no
definition node for the algebraic-space category or formal-diagram interface.
The existing flat-coherent-moduli definition is scheme-only. The existing adic
module system is a different category of coherent module diagrams on a fixed space,
not coherent families with varying b and their base arrows.

Both delivered modules compiled separately in dependency order via scompile.py;
the final run reported no errors or warnings (0.9s for the interface and 3.5s for
the theorem module's final library check). No global build was run. Every new
declaration has a source/blueprint docstring. There is no statement correction,
no STATEMENT-DISPUTED finding, and no dependency repair module.

## New nodes

`def-sfb-formal-diagram-restriction` supplies the category of lifted diagrams and
the cartesian normalization of restriction. Its source is artin.tex 07X4/07X6.
It uses the existing Mathlib fibre of a postcomposition functor, with natural
transformations over the identity. The project has base-specialized FormalSystem
object types, but no formal groupoid or restriction functor interface. Searches
and exact tool results are recorded; the new module contains only definitions.

`def-sfb-space-coherent-moduli-groupoid` is an existing:true attachment to
`AlgebraicGeometry.AlgebraicSpace.CoherentModuli.category` in
`Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`. It introduces no Lean module
or duplicate notion. Situation 08KB supplies its statement. Searches found these
existing helper declarations and the scheme-only FlatCoherentModuli node. The
only existing DAG owner of the general declarations is the downstream
coherent-stack algebraicity theorem, whose proof uses this item. Citing that
theorem would make a cycle, so the new definition node attaches just the already
available definitions and depends on their genuine defining notions. A path
check confirms none of these definition dependencies returns to this item.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
