## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentPushout` states
`AlgebraicGeometry.AlgebraicSpace.coherent_pushout` and
`AlgebraicGeometry.AlgebraicSpace.coherent_pushout_affine`, with sorry proofs.
It creates no definitions and makes no statement correction.

Read Stacks `quot.tex`, Situation 08KB (lines 879–910) and Lemma 08LQ
(lines 1137–1180). The source allows any thickening. The accepted node deliberately
asks for a nilpotent one; this delivery retains exactly that special case.

Hypothesis and clause correspondence:

- The scheme S and size convention are `{S : Scheme.{u}}` with explicit universe u.
  X and B are `{X B : AlgebraicSpace S}`, the existing fppf-sheaf full subcategory.
  There is no separatedness, Noetherianity, or ambient flatness hypothesis.
- The morphism is `f : X ⟶ B`. Finite presentation is precisely
  `hfp : ProperQuotFinitePresentation f`, i.e. local finite presentation,
  quasi-compactness, and quasi-compact diagonal.
- The family category is the existing `CoherentModuli.category f`. Its underlying
  `CoherentModuli f` stores `base : ProperQuotTest B`, hence the pair T and b:T->B,
  and `module : (properQuotFibre f base).Modules`. `properQuotFibre` is the actual
  sheaf pullback with algebraic-space validity from `fibreProduct_isAlgebraicSpace`.
- Each object's `quasiCoherent` is `module.IsQuasicoherent`; `finitePresentation`
  is `module.IsFinitePresentation` (finite-free presentations locally on the site).
  Its `flat` field tests `Scheme.Modules.IsFlatOver` on every etale scheme chart,
  using the chart restriction functor and the actual structural map to T. For a
  quasi-coherent module this is exactly the stalkwise convention in the node.
- Each object's `properSupport` supplies a closed immersion `i:Z->X_T`, properness
  of its composite to T, a quasi-coherent finite type G on Z, and an isomorphism
  `(moduleDirectImage i).obj G ≅ module`. This is the node's closed-carrier condition,
  including the zero module and empty carrier, without assuming support flatness.
- `CoherentModuli.Hom` stores a map of tests over B and an isomorphism from the
  specified tensor pullback to the source module. Identity and composition use
  `moduleTensorPullbackId` and `moduleTensorComposition`, as required by the node.
  The forgetful based category projects to schemes over S, not schemes over B;
  hence varying b is retained. Fibres over T therefore are exactly C(T).
- `{Z Y Z' P : Over S}` and `i,v,j,k` are the four S-schemes and actual square maps.
  `hi : IsFiniteOrderThickening i.left` means a closed immersion whose defining
  ideal sheaf has a globally nilpotent power. It is not merely a topological
  thickening. `[IsAffineHom v.left]` is the required affine overlap arrow.
  `hp : IsPushout v.left i.left j.left k.left` is the stipulated scheme pushout.
  The maps already lie over S, so this is also the pushout over S.
- `x,y,z` are objects of the fibres over Z,Y,Z'. `a,b` are actual arrows and
  `ha,hb` say they lie over v,i. Since an arrow is a cartesian module isomorphism,
  this is precisely a pair of objects with specified overlap identification.
  Conversely any specified overlap identification gives such a span by taking
  the canonical restriction of y as x and composing its identification with the
  restriction of z. Every overlap iso is retained, not just existence of an iso.
- The existential `t` is a family over P. `c,d` are its identifications on both
  pieces, and the two `IsHomLift` clauses place them over j,k. `IsPushout a b c d`
  includes their equality on the specified overlap, and unique gluing of every
  compatible pair of arrows. Restricting its universal property to targets over P
  proves full faithfulness on the fibre groupoid, including every automorphism.
  Together with existence of t this is essential surjectivity and full faithfulness
  of the canonical restriction, hence exactly its equivalence.
- This total-category formulation is conversely implied by the node's equivalence:
  for a target over any Q, first glue the two base maps P->Q using hp, then pull
  the target back to P and use full faithfulness in the fibre. Thus the pushout
  formulation adds no conclusion beyond the equivalence and its base pushout.
  Arbitrary tensor pullback preserves the four family conditions by the recorded
  base-change lemma, so all the fibre restrictions used in this equivalence exist.
- The affine declaration quantifies over all `A,D,D' : CommRingCat.{u}`, maps
  `alpha:A->D`, `q:D'->D`, surjectivity of q, and square-zero `RingHom.ker q.hom`.
  The pushout's coordinate ring is the concrete `CommRingCat.pullbackCone q alpha`:
  D' times_D A is canonically the same matching-pairs ring as A times_D D'. The
  order is recorded in the projection equations, not hidden in an arbitrary iso.
  `sZ,sY,sZ',sP` are all S-structures, and i,v,j,k lie over them with exactly
  `Spec.map q`, `Spec.map alpha`, and Spec of the two coordinate projections as
  underlying maps. These binders express the supplied compatible S-structure;
  they impose no extra finiteness or ring condition. The conclusion is the same
  gluing equivalence for these particular spectra, without assuming hp again.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.Modules`, structure sheaf and small etale site.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (through `properQuotFibre`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh` and the site instances for the Mathlib predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleDirectImage`, their normalized adjunction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, the chartwise affine-local flatness predicate.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`:
  `ProperQuotFinitePresentation`, `ProperQuotTest`, `properQuotFibre`, projections,
  `properQuotFibreMap`. The existing `CoherentModuli` reuses these exact constructions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsProper`, local finite presentation, quasi-compactness and separatedness.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFiniteOrderThickening`, whose
  definition is `∃ n, IsClosedImmersion i ∧ i.ker^(n+1)=⊥`.
- `Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`:
  `CoherentModuli`, `CoherentModuli.Hom`, identity, composition, `category`, and p.
  Only these concrete definitions and category laws are used; the downstream
  theorem `coherent_stack_general` is neither assumed nor used. That module's
  future proof import of this item must be omitted to avoid a module import cycle
  (stages/2-statements.md §3(7)). It already defines the correct category, and the
  one-definition rule forbids making a private replacement. No downstream theorem
  has been added as a DAG dependency and no mathematical dependency cycle is added.

The stated proof dependencies are imported plainly, including chart test,
proper-support base change, etale-chart support, affine-thickening pushouts and
closed pinching. Mathlib proof leaves are imported via FinitePresentation,
FiniteStability, and Support. The remaining proof-only nodes have no current
recorded Lean module, so no nonexistent import is invented.

Edge cases checked before writing: the identity thickening has zero defining
ideal; the zero module admits the empty closed proper carrier; empty test schemes
and empty X give the same groupoid formulation; arbitrary overlap automorphisms
are retained by a,b and the pushout equation. Zero rings are allowed in the affine
clause. The affine q may be an isomorphism (kernel zero). There is no nonempty,
finite-type-over-Z, or fixed characteristic assumption. Independent site/section
universe constraints are not added; the existing universe-polymorphic algebraic
space and module interfaces are used unchanged.

Searches made for an existing statement (2026-10-24):

- msearch leanfinder: `flat finitely presented quasi coherent sheaves proper support
  glue nilpotent pushout equivalence groupoid`. Eight hits, including
  `SheafOfModules.quasicoherentDataOfIsFinitePresentation`, local finite-presentation
  predicates and unrelated scheme flatness; none states this gluing equivalence.
- msearch leansearch: `coherent sheaves flat proper support infinitesimal pushout
  gluing`. Eight hits on ideal-sheaf supports, Mayer–Vietoris and ordinary sheaf
  gluing; none states this theorem.
- msearch loogle: `CategoryTheory.Functor.IsEquivalence, CategoryTheory.IsoComma`.
  Zero hits, IsoComma unknown. Used the existing total-category pushout formulation
  already illustrated by `AlgebraicStackRimSchlessinger.lean`, not a copied iso-comma.
- msearch grep: `CoherentFamily|coherentFamily|IsoComma|IsNilpotentThickening`.
  No Mathlib hits.
- rg in live WeilConjectures for the item ID: no occurrence. Concept/name rg in
  WeilConjectures and Sheaf found curve moduli but no coherent-family pushout.
  Inspection of DAG records found `lem-sfb-space-coherent-stack-general` with the
  exact reusable CoherentModuli definitions, which were read in full. Its theorem
  is algebraicity and is not this node's equivalence. No declaration is duplicated.

## Second reading by Q80

Performed a separate source-to-signature pass after drafting, with the node, Stacks
08KB/08LQ, and the final module open. This is a worker self-check; the dispatch
explicitly forbids starting another agent, and maintainer review is independent.
Checked that the source's maps to B are retained in `CoherentModuli.base`, that
finite presentation/flatness/proper support use the exact existing fields, that
all arrows carry the required tensor iso, and that the overlap is not quotiented
by isomorphism classes. Verified the total-category universal property is
mathematically equivalent to the canonical restriction equivalence, including
unique compatible arrows and targets over a different base. Checked nilpotence
uses finite order, not just a homeomorphism, and that the ring specialization
has precisely the four Spec maps and the two correct projection orientations.
No mismatch required a node correction. Added explicit dependency imports during
this pass. No use of the downstream algebraicity theorem occurs.
