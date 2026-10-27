## Worker report

The module `Sheaf.CategoryTheory.RingedToposInjectivePushforwardGlobalAcyclic` states
`CategoryTheory.RingedToposMorphism.isZero_rightDerived_globalSections_obj_injective`.
Its only proof is `sorry`; it introduces no new definition. The original node is changed
only in `lean`. Source read: `literature/stacks-project/sites-cohomology.tex`,
lemma-direct-image-injective-sheaf (072Z), lines 2211 onward, and lemma-limp-acyclic
(0731), especially part (3) and its proof taking K to be the final sheaf.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Sites small relative to one coefficient universe: explicit `universe u`,
  `{C D : Type u} [SmallCategory C] [SmallCategory D]` and Grothendieck topologies
  `{J : GrothendieckTopology C} {K : GrothendieckTopology D}`. This is precisely the
  universe-sized encoding used by the recorded ringed-topos interface. Sites of smaller
  size fit the chosen common universe; a Grothendieck topology encodes the covering
  sieves and their sheaves. No terminal object of either site is assumed.
- Sheaves of commutative rings: `A : Sheaf J CommRingCat.{u}` and
  `B : Sheaf K CommRingCat.{u}`. The existing `sheafCompose ...
  (forget₂ CommRingCat RingCat)` supplies their ring-sheaf types to the recorded module
  category and ringed-topos morphism; it does not replace commutativity by noncommutativity.
- The geometric morphism and structural ring map: the binder `f : RingedToposMorphism ...`.
  Its `inverse`, `direct`, `adj`, `leftExact`, and `ringMap` express the underlying
  geometric morphism and ring map. Its `modules`, `underlying`, and `module_linear`
  specify precisely the induced additive direct image and its scalar action. There is
  no functor between C and D, and there is no flatness or exact tensor-pullback hypothesis.
- Every source module sheaf: `I : ringedSiteModules.{u,u,u,u} ... A` after the existing
  commutative-to-ring forgetful functor. Its injectivity is exactly `[Injective I]`,
  the extension-along-monomorphisms class of the dependency node.
- Every integer p > 0: `(p : ℕ) (hp : 0 < p)`. Positive integers and positive naturals
  index exactly the same right-derived degrees. Degree zero is deliberately excluded:
  global sections of an injective module need not vanish.
- Global sections with the induced abelian group structure: the existing composite
  `SheafOfModules.toSheaf B_ring ⋙ Sheaf.Γ K AddCommGrpCat.{u}`. Mathlib
  `Sheaf.ΓNatIsoLim` identifies it with compatible families of module sections, with
  pointwise abelian operations. The underlying compatible families are exactly natural
  maps from the terminal set sheaf to the underlying set sheaf. Thus the composite is
  the specified Hom(1,-) functor, canonically, with its specified group structure.
- Derivation in target modules: `.rightDerived p` applies to that whole composite,
  whose domain is target module sheaves. In particular this is NOT the right-derived
  functor on abelian sheaves applied after forgetting scalars. Mathlib
  `Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj` compute it with
  injective resolutions in its domain, as the node requires.
- Vanishing on the direct image: `.obj (f.modules.obj I)` is exactly f_* I and
  `IsZero (...)` is zero in `AddCommGrpCat`, i.e. the displayed zero cohomology group.

Dependency declarations read and used:

- `def-weil-size-convention` is explicitly a metatheoretic convention with no
  declaration; it is rendered by the explicit common universe and small categories.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read in full and imported for the
  recorded site convention. The statement uses its associated standard
  `GrothendieckTopology` / `Sheaf` encoding; no new notion of site is introduced.
- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`,
  including its full generalized-element ring/module axioms, and
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `CategoryTheory.Injective`,
  and `.Resolution`, `CategoryTheory.InjectiveResolution` (both available through
  `Mathlib.CategoryTheory.Abelian.RightDerived`). Their full signatures and docstrings
  were read. No unusable dependency repair is needed.
- `def-sp-left-exact-additive` has no lean record and needs none: its mathlib_match
  is `CategoryTheory.Functor.rightDerived` in `Mathlib.CategoryTheory.Abelian.RightDerived`,
  with additivity `Functor.Additive` and left exactness `PreservesFiniteLimits`.
  The recorded `InjectiveResolution.isoRightDerivedObj` was also read.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections`, `Sheaf.Γ_additive`,
  provides additivity for Mathlib `Sheaf.Γ`. All instances are inferred without adding
  hypotheses about sheafification, resolutions, or additivity.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`,
  `SheafOfModules.isGrothendieckAbelian`, supplies the intrinsic Grothendieck structure;
  the module registers this existing theorem as an instance, just as the landed Leray
  module does. `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
  supplies enough injectives, and Mathlib's abelian resolution construction supplies
  `HasInjectiveResolutions`.

Proof dependency `lem-sfb-injective-pushforward-totally-acyclic` was read, including its
statement and absence of a Lean record/mathlib match in this checkout. It is needed only
for the postponed proof; no module import is available for it. The theorem's docstring
carries the node's proof: take K to be the terminal set sheaf, identify its pointwise
abelian sections with global sections, and compute both derived functors by target
module injective resolutions. No duplicate proof or total-acyclicity definition is added.
`def-sp-left-exact-additive` is imported through its Mathlib declaration as above.

Edge cases checked mathematically: identity geometric morphism (ordinary injective
acyclicity), zero module and zero coefficient ring, and the non-flat point-topos example
with structural map Z to Z/2. The conclusion claims acyclicity, not injectivity of f_* I,
so the non-flat case is retained. A site without a terminal object is covered because
`Sheaf.Γ` uses global sections by adjunction/limits. The empty site gives the zero module
category and zero cohomology. All positive degrees are included, and no p = 0 vanishing
is asserted. The statement has no extra size equality between unrelated universes: it
uses the existing small-site common-bound convention, which may be enlarged.

Searches (all against the prescribed current read clone / live published build):

- msearch.py leanfinder: "Direct image of injective modules on arbitrary ringed topoi
  is acyclic for global sections"; eight hits on local injectivity and vanishing on an
  injective input, none on the possibly noninjective module direct image.
- msearch.py loogle: `SheafOfModules.pushforward, CategoryTheory.Functor.rightDerived`;
  zero hits.
- msearch.py grep in CategoryTheory: `globalSections|[Tt]otally[Aa]cyclic|
  [Ii]njective.*pushforward`; no matching theorem for arbitrary ringed topoi.
- msearch.py grep in Algebra/Category/ModuleCat:
  `isZero.*rightDerived|globalSections.*[Aa]cyclic`; zero hits.
- msearch.py leansearch: "Direct image of injective sheaves of modules is acyclic for
  global sections"; eight hits including existing `SheafOfModules.sectionsFunctor`
  (Type-valued), no matching theorem.
- rg of `globalSections`, `totallyAcyclic`, and injective/pushforward in
  `lean/WeilConjectures` and `lean/Sheaf`: many scheme/ringed-space specializations,
  coefficientSections and a general-site Leray statement, but no matching theorem for
  arbitrary geometric morphisms. The existing constructions are used directly rather
  than defined again. Also searched the exact node id in `lean/WeilConjectures`; no hit.
- rg of the proposed module/declaration name in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no clash.

Validation: prescribed scompile.py checked the module separately as a sandbox module and
at its final library module name; both passed (2.3 s each), without errors or unexpected
warnings. No new nodes, dependency modules, statement correction, or statement dispute.

## Second reading by Q83

Author's self-check; independent review is performed by the maintainer, as specified by
the dispatcher brief. Re-read the node and final signature together: C,D,J,K,A,B and f
have the required types, I has source coefficients and injectivity, f.modules gives the
specified target coefficients, and rightDerived is taken AFTER forming the module-to-Ab
sections composite. The latter order is essential for the required resolution category.
Positive natural degrees cover the node's positive integer degrees. The theorem adds no
flatness, terminal-site-object or induced-site-functor assumption. No mismatch found and
no node text was changed. The only sorry belongs to the named target theorem, whose
proof docstring records the terminal-sheaf specialization of the total-acyclicity node.
