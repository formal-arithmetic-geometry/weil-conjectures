## Worker report

The module `Sheaf.CategoryTheory.RingedToposSitePresentation` states
`CategoryTheory.ringedTopos_sitePresentation`, with a single `sorry` proof.
Source: Stacks Project, Modules on Sites, Tag 03CR, clauses (1)-(6), read in
`literature/stacks-project/sites-modules.tex`; the proof also follows the supplied
node's seven steps. No definition, helper theorem, or new node is introduced.

Hypothesis and clause correspondence:

- The small sites C,D are `{C D : Type u} [SmallCategory C] [SmallCategory D]`,
  with precoverages `J,K` and all four recorded site-axiom instances for each.
  Their sheaf topoi are `Sheaf J.toGrothendieck (Type u)` and its K analogue.
- The commutative ring sheaves are the binders `A,B : Sheaf ... CommRingCat.{u}`.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` only forgets commutativity
  to use the existing ringed-topos interface; it changes no sections or operations.
- The geometric morphism and its ring map are `f : RingedToposMorphism ...`:
  `f.inverse`, `f.direct`, `f.adj`, `f.leftExact`, and `f.ringMap`.
  This previously landed interface includes its induced module direct image;
  that is determined by the geometric morphism and ring map, not an additional
  restriction on them. Its generalized-element identities express preservation
  of all ring operations, so the input is an actual ring-object map.
- The replacement small sites are existential `C',D'`, their `SmallCategory`
  structures and precoverages `J',K'`, with the same four axioms each.
  The existential `HasFiniteLimits C'` and `HasFiniteLimits D'` include terminal
  objects, pullbacks, equalizers, and all other finite limits.
- Their commutative coefficient rings are existential `A',B'`.
  The existential ringed-topos morphisms `g,e,h` have exactly the directions
  in the node. `g.direct.IsEquivalence` and `e.direct.IsEquivalence`, together
  with their adjunctions, give the asserted equivalences of topoi.
- The functor presenting h is `v : D' ⥤ C'`, with
  `PreservesFiniteLimits v`. The covering condition is the displayed
  `∀ T R, R ∈ K' T → R.map v ∈ J' (v.obj T)`.
  The second Stacks continuity condition (preservation of pullbacks along a
  covering arrow) follows from preservation of every finite limit.
  The existential `v.IsContinuous ...` is the resulting Mathlib sheaf-continuity
  instance and makes its specified direct image typeable.
- `h.direct = v.sheafPushforwardContinuous (Type u) ...` specifies the actual
  precomposition functor. Since h includes an adjunction and a left exact inverse
  image, it is the site-induced geometric morphism. Its left adjoint preserves
  colimits automatically, so it satisfies the recorded morphism-of-sites notion.
  `h.ringMap` is precisely the structural map `h^{-1} B' → A'`.
- Transported coefficients and canonical structural maps are stated via the
  underlying-sheaf isomorphisms `a : |A'| ≅ g.direct.obj |A|` and
  `b : |B'| ≅ e.direct.obj |B|`, followed by the two counit equations
  `g.ringMap = g.inverse.map a.hom ≫ g.adj.counit.app |A|` and its e analogue.
  This is the transport reading of the node's `A' = g_* A`, `B' = e_* B`:
  a finite-limit equivalence transports ring objects, and these equations
  uniquely characterize the transported ring operations under a and b.
  Specifically the left-hand maps preserve operations by the existing
  RingedToposMorphism fields; transposition along the equivalence then says
  a and b preserve the transported operations. The counits and a,b are
  isomorphisms, hence g and e have canonical structural ring isomorphisms.
  This uses no arbitrary ring map or unconstrained coefficient lift.
- `alpha : e.inverse ⋙ f.inverse ≅ h.inverse ⋙ g.inverse` is the inverse-image
  isomorphism between `e ∘ f` and `h ∘ g`. Its adjunction mate is the direct-image
  isomorphism. The final equality
  `f.inverse.map e.ringMap ≫ f.ringMap = alpha.hom.app |B'| ≫
  g.inverse.map h.ringMap ≫ g.ringMap` is exactly compatibility of the composite
  structural ring maps. Thus this is an isomorphism of ringed-topos morphisms,
  including the ring condition, not just an equivalence of their set functors.

Dependencies used:

- `def-weil-pbc-sites-and-cohomology`: the recorded Mathlib `Precoverage`,
  `Precoverage.HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`,
  `HasPullbacks`, `toGrothendieck`, `Sheaf`, `Functor.IsContinuous`,
  `Functor.sheafPushforwardContinuous`. Their signatures and docstrings were read
  in Mathlib's Precoverage, PrecoverageToGrothendieck, Sheaf and Continuous modules.
  The primary recorded module `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
  is imported; its `Sheaf.H'` is not needed to state this theorem.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  module `Sheaf.CategoryTheory.RingedSiteModules`, imported publicly through
  RingedToposMorphism. Read its full declaration and the Mathlib `SheafOfModules`
  structure, morphisms and `toSheaf` on which the ringed-topos interface relies.
- Added the already landed `def-weil-pbc-ringed-topos-morphism` to stmt_deps,
  using `CategoryTheory.RingedToposMorphism` from
  `Sheaf.CategoryTheory.RingedToposMorphism`. Read the full structure and docstring.
  This is reuse of the existing notion, with no dependency repair.
- The already recorded proof modules Sheafification, SiteInverseImageTensor,
  and SheavesAlgebraicStructuresObjects are imported without `public`.
  Unrecorded proof-only nodes supply no import yet. No import cycle is introduced.

Edge cases checked: no nonempty-site assumption (empty presented sites are allowed);
zero and terminal ring sheaves are allowed; no faithfulness, flatness or invertibility
of f's structural ring map is assumed. Identity and equivalence morphisms are allowed
without imposing that the chosen presentation be the identity. Empty covering families
are included in the quantified presieves. All objects, arrows, sections and replacement
sites use the same arbitrary universe u, exactly as the reused small-site interface;
there is no extra equality between independently specified universes. Finite-limit
closure indexed by natural numbers and small ambient Hom sets gives a small indexed
presentation in this universe, despite the ambient sheaf category having larger objects.

Searches for an existing statement:

- msearch LeanFinder: "Every morphism of ringed topoi admits a presentation by a
  continuous finite limit preserving functor of small sites": eight hits about
  finite-presentation module sheaves, none a ringed-topos site presentation.
- msearch Loogle: `"IsContinuous", "PreservesFiniteLimits"`: zero hits.
- msearch grep: `ringed.*topo|topo.*presentation|good.*site` in
  `CategoryTheory/Sites`: zero hits.
- msearch LeanSearch: "Every morphism of ringed topoi admits a finite limit
  preserving continuous small site presentation": unavailable, Internal Server Error.
- rg of the upstream WeilConjectures tree for the node id: no occurrence.
- rg of the upstream and Sheaf trees for `site.presentation|presentation.*ringed|
  ringed.*presentation`: only unrelated module presentations and section comparisons.
- rg for RingedToposMorphism/geometric morphisms found the existing general
  RingedToposMorphism interface, reused here. DAG searches for ringed-topos and
  ring-object notions found that node and the algebraic transport theorem nodes;
  no existing theorem states this presentation.

Validation: the delivered file compiled cleanly through scompile.py on the server
(nice 19, two threads, 60 seconds per file). The successful compile took 7.7 seconds
for this module. There are no node faults or STATEMENT-DISPUTED issues.

## Second reading by NC

Read the node, its seven proof steps, the worker module, and Stacks
sites-modules.tex, definition-ringed-topos and
lemma-morphism-ringed-topoi-comes-from-morphism-ringed-sites (03CR), together
with sites.tex, 03CI and 03A2. The node extracts the finite-limit presentation
conclusion; it does not request the additional special-cocontinuous witnesses,
prescribed representables, or identity refinement also available in 03CR.
The source imposes no geometric finiteness, nonemptiness or flatness assumption.

Object/hypothesis/conclusion checklist (all verdicts: matches):

1. Small sites C,D: `{C D : Type u} [SmallCategory C] [SmallCategory D]`,
   `J K : Precoverage`, and HasIsos, IsStableUnderComposition,
   IsStableUnderBaseChange, HasPullbacks on each. Read the Mathlib Precoverage
   classes and toGrothendieck: these encode the recorded site's covering axioms.
2. Commutative structure sheaves: `A,B : Sheaf ... CommRingCat.{u}`.
   The `forget₂ CommRingCat RingCat` preserves the same operations and sections.
3. Arbitrary geometric morphism and structural ring map: `f : RingedToposMorphism`.
   Read the entire dependency structure in RingedToposMorphism.lean. Its inverse,
   direct, adj, leftExact, ringMap and generalized-element ring laws give exactly
   the adjunction, left exactness and ring-object map. Preservation of negation
   follows from preservation of zero and addition; it is not missing data.
   Its modules, underlying and module_linear fields specify the induced module
   pushforward, not an extra property of the geometric morphism. Read also
   RingedSiteModules.lean and Mathlib SheafOfModules, Hom and toSheaf: this is the
   recorded general-site module category, not the scheme-specific category.
4. Replacement small sites: existential `C',D'`, their SmallCategory structures,
   `J',K'` and the same four site axioms. `HasFiniteLimits C'` and its D' analogue
   include the empty finite limit, so terminal objects are included.
5. Transported commutative rings: existential `A',B'`. The underlying-sheaf
   isomorphisms `a,b` and the two equations with `g.adj.counit` and `e.adj.counit`
   express the prescribed transported rings up to canonical ring isomorphism.
   To check that underlying-set isomorphisms suffice, transpose g.ringMap through
   its adjunction: it is exactly a.hom by the counit equation and the triangle
   identities. Transposition respects all ring operations because the left
   adjoint preserves finite products. Hence a.hom is a ring-object map, and
   similarly b.hom. Their inverses preserve the operations as well. Thus these
   are not arbitrary set identifications with unrelated ring structures.
6. Equivalences of topoi: `g,e` have the stated directions; their direct-image
   IsEquivalence conjuncts, together with their adjunctions, make the inverse
   images equivalences and the displayed counits isomorphisms. Accordingly the
   structural ring maps are the canonical transported isomorphisms.
7. Ringed-site presentation: `h` has direction C' to D'; `v : D' ⥤ C'` and
   PreservesFiniteLimits v give the required finite-limit functor. The covering
   conjunct `∀ T R, R ∈ K' T → R.map v ∈ J' (v.obj T)` is Stacks' cover
   preservation. Finite-limit preservation supplies its pullback condition.
   Read Mathlib IsContinuous and sheafPushforwardContinuous: the existential
   continuity instance types the actual precomposition functor. The equation
   `h.direct = v.sheafPushforwardContinuous ...` and h.adj identify h.inverse
   with the site inverse image. Its left exactness is h.leftExact; finite
   colimits are preserved since it is a left adjoint. `h.ringMap` supplies h♯.
8. Commutative square as ringed topoi: `alpha : e.inverse ⋙ f.inverse ≅
   h.inverse ⋙ g.inverse` compares the correct composite inverse images.
   The final equality has source f.inverse.obj (e.inverse.obj |B'|) and target
   |A|, and equates the two composite structural maps after alpha. The mate
   is the corresponding natural direct-image isomorphism. No independent mate
   datum or additional coherence hypothesis is necessary.

Edge cases: empty input sites are allowed, though replacement sites with finite
limits have terminal objects. Degenerate topoi, zero commutative rings, identity
morphisms and arbitrary noninvertible structural ring maps remain included.
Empty covering presieves are quantified, so empty families are not excluded.
There is no degree, characteristic, field or Noetherian restriction. All site
objects and arrows and ring sections share the arbitrary chosen universe of the
recorded RingedToposMorphism interface. A small index type for each closure stage
and their countable union indexes the replacement objects in Type u; Hom sets
between u-valued sheaves on a u-small site are u-small. Shrinking this indexed
full subcategory yields the displayed SmallCategory. Thus the large type of all
sheaves does not force replacement objects into Type (u+1), and no extra equality
between independent universes was imposed.

Independent searches: msearch LeanFinder `geometric morphism equivalent sites
finite limits ring sheaves` returned eight module-pushforward, site-pullback and
sheafification results, none the arbitrary-geometric-morphism presentation.
Loogle `"sheafPushforwardContinuous", "IsEquivalence"` returned three dense-subsite
or affine-etale equivalence instances; these do not quantify over an arbitrary
geometric morphism. msearch grep `topos|topoi|geometric` in CategoryTheory/Sites
returned fourteen documentation or special-site results, no matching theorem.
LeanSearch `Every geometric morphism has an equivalent presentation by finite
limit sites` was unavailable (Internal Server Error). Independent rg in Mathlib
Sites, upstream WeilConjectures and project Sheaf for ringed presentation,
topos-site-presentation, good-site and morphism-topoi-sites terminology found
only unrelated module presentations. No duplicate notion or theorem found.

There are no new nodes or dependency modules to review. Read the existing
proof-import declarations siteInverseImage_tensor and
sheaves_algebraicStructures_objects; they are proof infrastructure rather than
extra hypotheses of this theorem. Every bound variable and universe is explicit.
The module has one named postponed theorem, its source/blueprint docstrings,
and all seven natural-language proof steps; there is no definition with postponed
data and no proof supplied in this stage. The node lean.statement was compared
verbatim to the file's signature. No mathematical or Lean mismatch found; the
module and signature are retained unchanged. This reading adds the independent
clause audit and search evidence only.
