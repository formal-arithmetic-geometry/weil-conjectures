## Worker report

The delivery states `CategoryTheory.closed_complement_site_construction` in
`Sheaf.CategoryTheory.Sites.ClosedComplementSiteConstruction`. Its only theorem has `sorry`
as its proof. No definitions, new nodes, dependency repairs or statement corrections are needed.
The node copy changes only `lean`; its complete stage-1 proof is preserved.

The previous dispatch reported that N1 had already promoted this item. Reading the current
node and N1's report showed that this was the stage-1 split, not a Lean statement: the node had
no `lean` field. This delivery supplies stage 2 rather than resubmitting the stage-1 split.

Clause-by-clause correspondence:

- The small site is `(C : Type w) [SmallCategory C] (J : GrothendieckTopology C)`.
  The objects, morphisms and values of sheaves all belong to universe `w`, as in the recorded
  small-site convention. `w` is explicitly bound and arbitrary.
- Finite limits are `[HasFiniteLimits C]`. The named terminal object is `(X : C)` with
  `(hX : IsTerminal X)`. No particular choice of terminal object is imposed.
- Subcanonicity of the original topology is `[J.Subcanonical]`; this supplies the actual
  representable sheaf `J.yoneda.obj U`, with underlying presheaf `Hom(-,U)`.
- The represented subterminal is `(U : C) (i : U ⟶ X) [Mono i]`. Its map to the terminal
  representable is `J.yoneda.map i`; the map need not be an isomorphism. No separate hypothesis
  on the representable or its monomorphism is added.
- `∃ Jc : GrothendieckTopology C` asserts that the modified covering families define a
  Grothendieck topology on precisely the same category.
- For each `V` and `R : Presieve V`, the biconditional says that `Sieve.generate R` covers
  for `Jc` exactly when
  `Sieve.generate (R ⊔ Presieve.singleton (pullback.snd i (hX.from V)))` covers for `J`.
  The displayed arrow is exactly `U ×_X V → V`. A presieve records the arrows of a family;
  sup is union and `Sieve.generate` is its generated sieve. Repeated family members do not
  change either generated sieve. Conversely every presieve is the family of its member arrows,
  so this includes all covering families, including empty ones, and determines all covering
  sieves. No separate topology is chosen without its defining rule.
- The functor `I` is `q.direct`, for
  `q : GeometricMorphism (Sheaf Jc (Type w)) (Sheaf J (Type w))`.
  The equality
  `q.direct ⋙ sheafToPresheaf J (Type w) = sheafToPresheaf Jc (Type w)`
  makes it the identity on all underlying presheaves AND natural transformations. This can
  be strict equality: the inclusion changes only the sheaf-condition proof, and both
  composites with the forgetful functor are definitionally the same functor.
- `Nonempty q.direct.FullyFaithful` is precisely full faithfulness.
- `GeometricMorphism` already contains an inverse image, its adjunction to the direct image,
  and preservation of finite limits by the inverse image. Both sheaf categories are small-site
  presentations, so this is a geometric morphism of topoi in the recorded convention.
- For EVERY `G : Sheaf J (Type w)`, `q.direct.essImage G ↔ IsIso (prod.fst :
  J.yoneda.obj U ⨯ G ⟶ J.yoneda.obj U)` is the exact essential-image assertion.
  `prod.fst` is the prescribed projection, not just the existence of an unrelated isomorphism.
  Mathlib's `Functor.essImage` includes all objects isomorphic to direct-image objects.
- The only subcanonical binder is on `J`; no representability or subcanonicity is asserted
  for `Jc`. There are no supplementary assumptions on the coefficient category.

Dependencies read and used:

- `def-weil-pbc-topos`: `Sheaf.CategoryTheory.Sites.GrothendieckTopos`,
  `CategoryTheory.IsGrothendieckTopos`. Its docstring explicitly delegates sieves, topology,
  sheaf condition and sheaf category to Mathlib; the statement uses these exact notions.
  The module is imported through the geometric-morphism module.
- `def-trf-geometric-morphism`: `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`, with its actual fields `inverse`, `direct`, `adj`,
  `leftExact`; the signature and docstring were read in full.
- The proof's three Mathlib leaves are already recorded without Lean records. Their exact
  declarations and source interfaces were read: `CategoryTheory.Sheaf.createsLimitsOfShape`
  in `Mathlib.CategoryTheory.Sites.Limits`,
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` in
  `Mathlib.CategoryTheory.Sites.Pullback`, and the `PreservesFiniteLimits (presheafToSheaf J A)`
  instance in `Mathlib.CategoryTheory.Sites.Sheafification`, with `Type w` sheafification
  supplied by `Mathlib.CategoryTheory.Sites.LeftExact`. Those proof interfaces are imported;
  `Limits` is public because its sheaf products are used in the signature. No unstated
  project theorem or downstream complement-factorization theorem is imported.

Source and proof: I read Tag 08LY in `literature/stacks-project/sites.tex`, including the
modified covers, identity direct image, and its singleton criterion. The theorem docstring
contains all eight steps of the node's proof: the support sieve, topology axioms,
family/sheaf convention and inclusion, sectionwise projection criterion, empty-cover
necessity, matching-family extension and unique gluing, identity Kan extension and adjunction,
and left exactness. In particular the argument omitted in the printed source is supplied
by the node and retained in the docstring. Nothing is proved in this stage-2 module.

Edge cases checked before writing:

- `i = 𝟙 X`, `U = X`: the added arrow is an isomorphism at every object, so every presieve
  covers for `Jc`; its sheaves are terminal. Since `h_U` is terminal, the projection criterion
  likewise says `G` is terminal. The formula includes `R = ⊥`.
- On an open-set site with `U = ∅`, the added empty-open member does not alter coverings,
  hence `Jc = J`; `h_U × G → h_U` is invertible for every sheaf. No strict initial object is
  presumed for a general category.
- A domain admitting a map to `U` has an empty `Jc` cover. Unique empty-family amalgamation
  forces exactly one section, not an empty section set. This is the essential-image criterion.
- An object already empty-covered for `J`, a maximal original topology, and the one-object
  terminal category cause no exception. A finite-limit category with a terminal object cannot
  be empty, and that is already in the node's hypotheses.
- All presieves, all sheaves and all small categories in `w` are quantified; there is no
  inhabitedness assumption on families or on section types, and no unrelated universe equality.

Searches for an existing statement, all actually run with `msearch.py` under this item:

- LeanFinder: "Closed complement topology of a subterminal representable on a small site,
  whose sheaves satisfy h_U times G isomorphic to h_U". Eight hits concerned canonical
  topology, representables being sheaves and `classifier_isSheaf`; none is this construction.
- Loogle: `CategoryTheory.GrothendieckTopology, CategoryTheory.Sheaf`. Twelve hits gave basic
  sheaf-category/forgetful/terminal interfaces, not the modified topology or essential image.
- Mathlib grep, CategoryTheory: `closed.?[Ss]ubtopos|closedComplement.*[Tt]opology|closed_complement_site`.
  Zero hits.
- LeanSearch: "Closed complement of a representable subterminal sheaf by a finer
  Grothendieck topology". Eight hits concerned subcanonical/finest topology, closed sieves,
  and sheaf monotonicity, not the closed-complement construction. Closed sieves in the
  subobject classifier are not the modified site in this node.
- Direct `rg` in upstream `WeilConjectures` for `closedComplement`, closed-subtopos terminology,
  and the exact node id found only scheme open/closed complements and their sheaf operations;
  the exact id had no hit.
- Direct `rg` in project `lean/Sheaf` found `closedComplementObjects` and the downstream
  `topos_complement_factorization`, which presupposes this site's construction. Neither states
  its defining covering rule. They are not imported and do not produce an import cycle.
- Exact proposed declaration search `closed_complement_site_construction` in Mathlib,
  upstream sources, the project and `dag/lean_names_upstream.json` had no hits.

Validation: `scompile.py N3 lem-trf-closed-complement-site-construction` compiled the sole
module in both its sandbox and library module paths, cleanly, without errors or warnings
(11.4 s and 3.3 s respectively). Every binder and the universe are explicit; line width is
at most 100. There is no `STATEMENT-DISPUTED` flag or remaining node fault.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
