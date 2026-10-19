## Worker report

The delivery states `CategoryTheory.topos_complement_module_stalks` in
`Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks`. Its only postponed proof
is that theorem. All three helper declarations have real bodies and are listed
in `lean.declarations`: `ToposComplementModules.Lift` abbreviates the published
normalized constant-module lift, `IsCompositionComparison` pins a comparison to
the inverse-image mate of a specified factorization, and `PointAssertion` spells
out the point clauses and their natural adjunction-map identities. These helpers
package clauses of this node; they introduce no independent mathematical notion.

### Objects, hypotheses, and presentations

* A Grothendieck topos is, by the recorded `IsGrothendieckTopos` definition, a
  category equivalent to `Sheaf J (Type w)` for a `w`-small site. Accordingly the
  theorem quantifies over arbitrary `C D O : Type w` with `SmallCategory`
  structures and topologies `J K L`. This is a presentation of every ambient,
  closed, and open topos, respectively. It does not assume that the original
  topos itself has equally sized object and morphism universes. All assertions
  are invariant under equivalences, so passing to its defining small-site
  presentation excludes no Grothendieck topos.
* `U : Sheaf J (Type w)` and `IsSubterminal U` render the subterminal object.
  `j` and `k` are the recorded geometric morphisms. The condition
  `∃ e : Sheaf L (Type w) ≌ Over U,
  Nonempty (j.inverse ⋙ e.functor ≅ Over.star U)` identifies `j` with the open
  slice embedding. Full faithfulness of `k.direct` and
  `k.direct.essImage A ↔ closedComplementObjects U A` identify `k` with the
  complementary closed embedding of the recorded factorization lemma. These
  are the precise meaning of “its open embedding” and “the complementary
  closed embedding”; unrelated geometric morphisms do not satisfy the binders.
* `Λ : Type w` with `[CommRing Λ]` is any coefficient ring in the same universe
  of sets as the topos. `Modules J Λ` is the published abbreviation for
  `ringedSiteModules ((constantSheaf J RingCat).obj (RingCat.of Λ))`.
  Thus all categories are actual modules over constant ring sheaves, rather
  than abstract additive categories or copies of the module notion.
* A point is written on an arbitrary small-site presentation of its source:
  `S : GrothendieckTopology P`, `eSet : Sheaf S (Type w) ≌ Type w`, and
  `p : GeometricMorphism (Sheaf S (Type w)) (Sheaf J (Type w))`.
  Composing with the geometric equivalence associated to `eSet` gives exactly
  a point `Set → E`. Conversely every such point can be transported to a
  fixed singleton-site presentation. The equivalence to `Type w` is essential:
  it guarantees the nondegenerate source needed for the exclusive dichotomy.
  Stalks are modules over the constant ring on this presentation of sets,
  hence the usual Λ-modules under that equivalence. No arbitrary fibre functor
  replaces the geometric inverse image.

### Each conclusion

1. The first conjunct quantifies over every geometric morphism between small
   presenting sites and concludes `Nonempty (ToposComplementModules.Lift Λ f)`.
   This is exactly the existing `ConstantLeftModuleInverseImageLift`: its
   `moduleFunctor` has `preservesFiniteLimits`, `preservesFiniteColimits` and
   `additive`, so inverse image is exact. Its ring, underlying-set, scalar,
   and unit normalizations specify the induced constant-Λ inverse image.
2. In the second conjunct, the witnesses `dj` and `dk` are those normalized
   module lifts for the actual embeddings. The witness `jShriek` and
   `adj : jShriek ⊣ dj.moduleFunctor` give the module left adjoint to `j^*`.
   `dk.moduleAdj` supplies `k^* ⊣ k_*`; these adjunctions are conclusions,
   not hypotheses about arbitrary functors.
3. `dk.moduleDirect.Full ∧ dk.moduleDirect.Faithful` is fully faithful `k_*`.
   `dk.moduleDirect.essImage F ↔ IsZero (dj.moduleFunctor.obj F)` is exactly its
   support characterization, including closure under isomorphism.
4. `openUnit : 𝟭 _ ≅ jShriek ⋙ dj.moduleFunctor`, with
   `openUnit.hom = adj.unit`, makes the actual open unit invertible; its inverse
   is `j^*j_!G ≅ G`. `closedCounit : dk.moduleDirect ⋙ dk.moduleFunctor ≅ 𝟭 _`,
   with `closedCounit.hom = dk.moduleAdj.counit`, is the actual `k^*k_*H ≅ H`.
   Both are natural isomorphisms, not merely objectwise isomorphism classes.
5. The next two clauses are respectively
   `IsZero (dk.moduleFunctor.obj (jShriek.obj G))` and
   `IsZero (dj.moduleFunctor.obj (dk.moduleDirect.obj H))`, giving the two zero
   restrictions without a conservativity hypothesis on points.
6. `PointAssertion` supplies a normalized module lift `dp` of every point and
   asserts `Xor (Nonempty (IsTerminal (p.inverse.obj U)))
   (Nonempty (IsInitial (p.inverse.obj U)))`. Under `eSet` these are exactly
   `p^{-1}U ≅ 1` and `p^{-1}U ≅ 0`, exclusively and exhaustively.
7. In the terminal case there are a geometric point `po` of the open topos,
   `q : (po.comp j).direct ≅ p.direct`, and its normalized module lift `dpo`.
   `openStalk : jShriek ⋙ dp.moduleFunctor ≅ dpo.moduleFunctor` is the natural
   identification `p^*j_! ≅ p_o^*`; the separate `IsZero` clause gives
   `p^*k_*H = 0`.
8. In the initial case the analogous `pc`, `q`, `dpc` and
   `closedStalk : dk.moduleDirect ⋙ dp.moduleFunctor ≅ dpc.moduleFunctor`
   give `p^*k_* ≅ p_c^*`, and the `IsZero` clause gives `p^*j_!G = 0`.
9. Each `c : dp.moduleFunctor ≅ dj.moduleFunctor ⋙ dpo.moduleFunctor` (or its
   closed counterpart) satisfies `IsCompositionComparison`. Unfolding it, its
   forgotten component composed with the two supplied set comparisons equals
   `dp.moduleSetIso.hom.app F` followed by the inverse-image mate of `q`.
   Hence it is precisely the canonical composition comparison. In the open
   case `openStalk.hom.app G` is pinned to
   `c.hom.app (jShriek.obj G) ≫ dpo.moduleFunctor.map (openUnit.inv.app G)`.
   In the closed case `closedStalk.hom.app H` is pinned to the corresponding
   `c` followed by `dpc.moduleFunctor.map (closedCounit.hom.app H)`.
10. The open equation
    `dp.moduleFunctor.map (adj.counit.app F) ≫ c.hom.app F =
    openStalk.hom.app (dj.moduleFunctor.obj F)` says the stalk of the actual
    counit becomes the identity under those same two natural identifications.
    The closed equation
    `dp.moduleFunctor.map (dk.moduleAdj.unit.app F) ≫
    closedStalk.hom.app (dk.moduleFunctor.obj F) = c.hom.app F`
    says the same for the actual unit. Thus “identity” is not weakened to
    mere invertibility under freely chosen identifications.
11. Exactness of each point inverse image, including `po` and `pc`, is contained
    in the normalized lifts `dp`, `dpo`, and `dpc`, whose finite-limit and
    finite-colimit preservation fields are part of the conclusion.

### Dependency declarations and sources read

* `Sheaf.CategoryTheory.Sites.ToposComplementFactorization`:
  `CategoryTheory.closedComplementObjects` and
  `CategoryTheory.topos_complement_factorization`, including their full
  signatures and docstrings. The first gives the exact closed object property;
  the second supplies the complementary geometric embeddings and factorization.
* `Sheaf.CategoryTheory.Sites.GrothendieckTopos`:
  `CategoryTheory.IsGrothendieckTopos` (the small-site presentation definition).
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism`, `.comp`, and `.inverseIso`. The last
  constructs the inverse-image mate of a direct-image isomorphism; its
  direction is `p.inverse ≅ (po.comp j).inverse` for the `q` used here.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`, sheafification of the constant presheaf.
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
* `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `ConstantLeftModuleInverseImage.Modules`, `.W`,
  `ConstantLeftModuleInverseImageLift`, and
  `CategoryTheory.constant_left_module_inverse_image`, including the scalar,
  addition, unit, composition, and presentation normalization fields.
  Its already landed node is added to `stmt_deps` because these declarations
  are now used in the statement as well as in the proof plan.
* Proof-only imports are the recorded modules of
  `lem-trf-oriented-closed-base-localization`,
  `lem-trf-topos-localization-site-presentation`,
  `lem-pur-site-restriction-module-adjunction-exact`,
  `def-weil-extension-by-zero-presheaf`, and
  `def-weil-presheaf-modules-sheafification`.

Read the actual Stacks statements and proofs at `sites-modules.tex`
`lemma-extension-by-zero`, `lemma-stalk-exact-modules`, and
`lemma-stalk-j-shriek`, and at `sites.tex` `lemma-closed-subtopos` and
`lemma-closed-immersion`. The natural map identities are their adjunction
triangle-identity consequences, as the node's ten-step proof explains.
There is no repair note for this item and no numbered return entry for it.

### Edge cases and searches

* U initial: the open topos is degenerate, the closed topos is the ambient
  topos, and only the closed factorization of any point occurs.
* U terminal: the open embedding is the identity and the closed topos is
  degenerate; only the open point case occurs.
* Λ is the zero ring: all the module categories are zero, but the set-valued
  point dichotomy remains the same. No nonzero or nonempty assumptions occur.
* The ambient topos is degenerate or has no points: the point clauses quantify
  over points when they exist, while support and zero restrictions remain
  categorical statements. Nothing uses enough points.
* Object and morphism universes of an arbitrary original topos need not agree;
  the equal universes here concern only its defining small-site presentation.
  `w` is arbitrary and the coefficient ring lies in that universe of sets.

Actual searches in this session (in addition to the node's recorded searches):

* `msearch.py ... leanfinder "Modules over a constant ring on complementary
  open closed subtopoi stalk formulas adjunction"`: eight hits including
  `ModuleCat.Tilde.toStalk`, `ModuleCat.Tilde.toOpen_germ`, and
  `stalkSkyscraperSheafAdjunction`; their displayed types concern affine
  scheme modules or topological stalks, not the general theorem here.
* `msearch.py ... loogle "CategoryTheory.GeometricMorphism"`: zero hits;
  the service reported that this project declaration is unknown.
* `msearch.py ... grep "closedComplement|extensionByZero|moduleStalk"
  CategoryTheory/Sites`: zero hits.
* `msearch.py ... leansearch "exact module sheaf inverse image geometric
  morphism open closed complement stalk"`: eight hits, including the scheme
  restriction stalk isomorphism and topological `stalkPullbackIso`; no match.
* `rg` through the pinned Mathlib sites source, the read-only
  `WeilConjectures/`, the upstream name index, and shared `lean/Sheaf/` found
  the normalized module inverse-image and closed-localization declarations
  used above, but no theorem with all of this node's clauses. The upstream
  search by this node's exact id returned no declaration.

No new DAG nodes or dependency repairs are needed. The mathematical statement
is unchanged; selecting presentations and normalizing its maps is an encoding,
not a statement correction. There is no STATEMENT-DISPUTED flag.

## Second reading by Q153

This is a separate self-review after reopening both the target JSON and the
revised module; no independent agent was started, as the dispatcher forbids it.
The first draft was rejected in this review: arbitrary module-category data did
not characterize the actual functors, and an unrestricted identity predicate
lost the specified comparisons. That draft is removed entirely from delivery.

In the final module the module categories unfold to the recorded constant-ring
`SheafOfModules` categories. The embeddings are explicitly identified with the
open slice and closed essential image. The lift type is the published normalized
interface, not a new arbitrary functor. Both module adjunctions occur in the
existential conclusion. The open and closed natural isomorphisms equal their
actual unit and counit. Every one of the support, two zero restrictions,
exclusive point dichotomy, factorization, four point formulas, and two map
identities appears in the theorem or its transparent `PointAssertion` body.

Checked the directions of the composition mate and the four displayed
compositions by their domains and codomains. In particular the open counit
identity compares maps from `p^*j_!j^*F` to `p_o^*j^*F`, and the closed unit
identity compares maps from `p^*F` to `p_c^*k^*F`. Each stalk comparison is a
natural isomorphism pinned by the preceding composition normalization and
unit/counit formula. No conclusion is moved to an assumption or supplied as
unconstrained data, and no axiom, `let`, private notation, or local instance is
introduced. All variables and the universe are explicitly bound.

Validation: `scompile.py Q153 lem-trf-topos-complement-module-stalks
lean/Sheaf/CategoryTheory/Sites/ToposComplementModuleStalks.lean` compiled the
sandbox file and its delivery-path module cleanly (18.3 s and 18.0 s), with no
errors or warnings. Required side-only dependencies also compiled cleanly.
