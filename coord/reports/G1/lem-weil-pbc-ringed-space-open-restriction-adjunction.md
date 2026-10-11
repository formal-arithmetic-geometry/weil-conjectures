## Worker report

Module: `Sheaf.Topology.OpenRestrictionAdjunction`, declaration
`TopologicalSpace.Opens.exists_openRestrictionAdjunction`.
It states the open-restriction adjunction and specifies both directions of its hom-set
bijection. Its only proof is `sorry`; it introduces no definitions or instances.

Hypotheses and clauses, in the order of the node:

- A topological space: `(X : TopCat.{u})`, with no separation or nonemptiness assumptions.
- A sheaf of commutative rings: `(O : X.Sheaf CommRingCat.{max u v})`.
  `sheafCompose _ (forget₂ CommRingCat RingCat)` forgets only commutativity to use
  Mathlib's existing module-sheaf category; it does not change sections or restrictions.
  The maximum universe satisfies the size requirement of this sheaf composition.
  The module universe `w` is independent. All variables and universes are explicit.
- An open subset: `(U : Opens X)`, including bottom and top.
- The restricted ring is `R.over U`, where `R` denotes the above ring-valued sheaf.
  We encode the open subspace by its site `Over U`: an object `W` is an open `W.left`
  of X with an inclusion `W.hom : W.left ⟶ U`. The site is equivalent to `Opens ↥U`
  by `U.overEquivalence`; `U.sheafOfModulesEquivOver R` identifies its modules with
  modules of `U.sheafRestrict.obj R`. Thus these are exactly the opens and modules
  in the node, not a different class of ringed spaces or sheaves.
- Restriction of M: `SheafOfModules.overFunctor R U`, whose object is `M.over U`.
  It evaluates on `W` as `M(W.left)` with the original restrictions and ring action.
  Its map evaluates a module morphism on `W.left`, hence is precisely `α|_U`.
  This is also the restriction used by the recorded finite-type/presentation dependency.
- Direct image: `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)`.
  Its base functor is `Over.star U`, taking V to the product `U ⨯ V` over U.
  In the preorder of opens this product is canonically the intersection `U ∩ V`.
  `pushforwardOver U` has components `R.obj.map prod.snd.op`: the ring restriction
  from V to U ∩ V. The module action is restriction of scalars along this map,
  and the direct-image morphism components are the original ones on U ∩ V.
  The functor types in the existential assert the domains, codomains and functor laws.
- The adjunction is `∃ adj : overFunctor R U ⊣ pushforward (pushforwardOver U), ...`.
- Every pair of modules: both conjuncts quantify `M : SheafOfModules R` and
  `G : SheafOfModules (R.over U)` without finite-type or finite-presentation assumptions.
- Forward bijection and its specified formula: the first conjunct quantifies
  `α : M.over U ⟶ G`, every `V : Opens X`, and every section `s : M.val.obj (op V)`.
  Its left side is `((adj.homEquiv M G) α).val.app (op V) s`.
  Its right side is `α.val.app (op ((Over.star U).obj V))`
  applied to `M.val.map (prod.snd : U ⨯ V ⟶ V).op s`, exactly restriction followed
  by α on the intersection. `adj.homEquiv` is an `Equiv`, so bijectivity is included.
- Naturality in both modules is part of the adjunction, expressed by Mathlib's
  `Adjunction.homEquiv_naturality_left` and `Adjunction.homEquiv_naturality_right`.
- Inverse: the second conjunct quantifies every direct-image morphism β, every
  `W : Over U`, and every section of M on `W.left`. Its left side is
  `((adj.homEquiv M G).symm β).val.app (op W) s`.
  The right side applies `β.val.app (op W.left)` and the canonical identification
  `G.val.map ((Over.forgetAdjStar U).unit.app W).op`.
  The unit has underlying inclusion `W.left ⟶ U ⨯ W.left`, namely
  `prod.lift W.hom (𝟙 _)`. Since W.left is contained in U, these opens coincide.
  This restriction is exactly the identification `(j_*G)(W) = G(W)` used in the node.
  It is not an extra operation: it accounts for Mathlib's chosen categorical product
  rather than assuming its definitional equality with intersection.

Dependency declarations read and used:

- `def-weil-sheaf-of-modules-category`: Mathlib.Algebra.Category.ModuleCat.Sheaf,
  `SheafOfModules`, `SheafOfModules.Hom`, and its category instance. Read full
  declarations: module-valued presheaf, underlying abelian sheaf condition, linear maps.
- `def-weil-pbc-module-finite-type-presentation`: its Mathlib match is
  `SheafOfModules.IsFiniteType` (Generators) and `SheafOfModules.IsFinitePresentation`
  (Quasicoherent), with presentation/cokernel translations. Read both class signatures
  and docstrings. Neither finiteness hypothesis belongs in this statement; the part of
  that dependency used here is its explicit restriction `M.over U` / `overFunctor`,
  from Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous. No replacement
  of the dependency or redundant finiteness import is needed.
- Additional existing library machinery, all via the sole import
  `Mathlib.Topology.Sheaves.Module`: `SheafOfModules.pushforward`, `pushforwardOver`,
  `Over.star`, `Over.forgetAdjStar`, `Opens.overEquivalence`, and
  `Opens.sheafOfModulesEquivOver`. Read their definitions and docstrings. The existing
  `overPushforwardOverAdj` supplies the construction route at stage 3, but the new
  theorem additionally specifies the precise forward and inverse section formulas.

Source checked online because the local Stacks TeX checkout is absent:
[0096](https://stacks.math.columbia.edu/tag/0096) gives the adjunction;
[00A0](https://stacks.math.columbia.edu/tag/00A0) gives the open-restriction sections
and inverse identities for modules;
[00A1](https://stacks.math.columbia.edu/tag/00A1) defines the ringed open subspace
and module restriction;
[0095](https://stacks.math.columbia.edu/tag/0095) defines module direct image.
No statement correction or dispute is needed.

Edge cases checked before writing: X empty; U empty; U = X; zero sheaves and the
zero ring sheaf; empty intersections; an open W contained in U (the inverse's
identification is the isomorphism of equal opens). All are admitted by the binders.
No point, generator, nonzero section, or nonempty open is selected. Rings can live
in a universe larger than X and modules in their own universe; smaller rings can
be viewed in the containing universe without changing the mathematical statement.

Searches made with `/home/ubuntu/weil-launcher/msearch.py G1 <item>`:

- leanfinder, `restriction of sheaves of modules to an open subset is left adjoint to
  direct image`: eight hits, including scheme-only `restrictAdjunction` and general
  `pullbackPushforwardAdjunction`, no declaration specifying both formulas here.
- loogle, `SheafOfModules.overPushforwardOverAdj`: one hit, the adjunction on Over U.
  Read it and its underlying `pushforwardPushforwardAdj`, unit/counit component lemmas.
  This gives a construction route but not a statement containing both section formulas.
- grep, `overPushforwardOverAdj|sheafOfModulesEquivOver|openRestrictionAdjunction`:
  eight hits in the scheme, topology module and module pushforward files, no theorem
  specifying the formulas of this node.
- leansearch, `restriction of sheaves of modules to an open subset adjunction direct
  image`: UNAVAILABLE, Internal Server Error; no verdict inferred from the outage.
- `rg` with the same notions in source `WeilConjectures` and repository `lean/Sheaf`:
  source Tilde uses the module equivalence, and the project's extension-by-zero module
  uses it too; DerivedHomMayerVietoris uses `overFunctor`. No duplicate statement.
- `grep -rn` of this exact node id in `WeilConjectures`: no hit.

Validation: server `scompile.py` passed cleanly. The initial separate ring universe
was rejected by the universe condition of `sheafCompose`; the ring universe was
changed to `max u v`, without introducing any mathematical hypothesis. All lines
are at most 100 characters. Delivery dry run is the final mechanical check.


## Second reading by G1

I independently read the node, its six proof steps, the entire delivered module,
and both statement dependency nodes and their recorded Mathlib declarations.
No statement mismatch was found; the Lean module and node record are unchanged.

Source reading: the local literature checkout is absent. I fetched the actual
Stacks `sheaves.tex` into this item's `scratchpad/sheaves.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex and read
lines 3048–3060 (ringed spaces), 3117–3184 (0095 and 0096), and 4453–4517
(00A0 and 00A1), including the proofs and surrounding assumptions. The source
requires only a topological space, a ring sheaf, and an open inclusion here.
The node's commutative-ring specialization agrees with the source; there are no
implicit separation, Noetherian, or finiteness hypotheses.

Object/hypothesis/conclusion checklist (all verdicts: exact):

| Node item | Lean rendering and verification |
| --- | --- |
| Arbitrary topological space X | `(X : TopCat.{u})`; no extra instance binder. |
| Sheaf of commutative rings O_X | `(O : X.Sheaf CommRingCat.{max u v})`; `sheafCompose` with `forget₂` retains exactly its rings and restrictions, forgetting commutativity only. |
| Open U of X | `(U : Opens X)`; openness is bundled, with no nonemptiness assumption. |
| O_U(W) = O_X(W), W contained in U | `R.over U`, where R is the displayed forgotten ring sheaf; `Over U` consists of precisely these W and inclusion proofs. |
| Category of O_X-modules and linear morphisms | `SheafOfModules R` and its `Hom`, read in `Sheaf.lean:33–55`; the underlying module presheaf has semilinear restrictions and a sheaf condition. |
| Restricted modules and morphisms | `overFunctor R U`, with object `M.over U`; `PushforwardContinuous.lean:59–74` retains components at `W.left`. |
| Open-subspace category Mod(O_U) | `SheafOfModules (R.over U)`; `overEquivalence` identifies the over site with `Opens U` including its topology, and `sheafOfModulesEquivOver` identifies the module categories. Their definitions were opened, not inferred from names. |
| Direct image sections G(V intersect U) | `pushforward (pushforwardOver U)`; `Over.star U` has underlying product `U ⨯ V`, canonically the intersection in the preorder of opens. |
| Direct image scalar action | `pushforwardOver U` is explicitly `R.obj.map prod.snd.op` at V, so scalars act through restriction from V to its intersection with U. |
| Direct image morphisms | The `pushforward` map retains G's components at `Over.star U`, exactly the prescribed components on intersections. |
| Both rules are functors, restriction left adjoint | The existential's two terms are existing functors with the required domains/codomains, and `adj : overFunctor ... ⊣ pushforward ...` asserts the adjunction. |
| All M, G, alpha, V, s in the forward formula | First conjunct quantifies these in that order with no added module properties; `adj.homEquiv M G` is an equivalence from restricted-module morphisms to direct-image morphisms. |
| Forward formula alpha(s restricted to V intersect U) | RHS is `α.val.app (op ((Over.star U).obj V)) (M.val.map prod.snd.op s)`, exactly restriction followed by alpha. |
| Bijectivity and naturality in both modules | `Adjunction.homEquiv` is an `Equiv`; its left and right naturality laws are part of the adjunction API. |
| Inverse beta_W for every W contained in U | Second conjunct quantifies M, G, beta, W, s; `(adj.homEquiv M G).symm` evaluates beta on `W.left`, then maps along the unit of `forgetAdjStar`. |
| Identification (j_*G)(W) = G(W) | The unit's underlying map is `prod.lift W.hom (𝟙 _)`, read in `Comma/Over/Pullback.lean:165–178`; it identifies W with U intersect W. Its opposite induces precisely the canonical restriction identification, with the correct direction. |

Dependency audit: `def-weil-sheaf-of-modules-category` records Mathlib's
`SheafOfModules`, which is used directly. The other dependency's recorded
`IsFiniteType` and `IsFinitePresentation` signatures (Generators:142 and
Quasicoherent:267) were opened; they describe local finite generators and finite
cokernel presentations. The only part needed by this item is their existing
`M.over U` restriction. No finiteness hypothesis is imported into the theorem.
Neither dependency needs replacement. There are no new nodes or dependency modules.

Edge cases: X empty, U bottom, U top, V intersect U empty, zero modules, and a
zero ring sheaf are all permitted. No section or point is selected and no
nonzero or characteristic hypothesis is present. There is no index or n binder
in this node. Universes u, v, w are explicitly bound; the ring universe max u v
permits rings of arbitrary larger size and cumulative smaller ring carriers,
while the module universe w is independent. No test-object quantifier is confined
to a smaller independent universe. The categorical products and site equivalence
exist for every topological space; they impose no additional assumptions.

Independent searches through `msearch.py G1 <item>` (recorded in searches.jsonl):

- LeanFinder: `module sheaf restriction adjunction hom equivalence section formula open`:
  eight hits, including scheme-only unit/counit formulas and unrelated unitHomEquiv;
  no theorem containing this general-space adjunction and both specified formulas.
- Loogle: `SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app`: one hit.
  I read the general adjunction and both its unit/counit formula lemmas as well
  as `overPushforwardOverAdj` in PushforwardContinuous:274–350. These provide the
  construction, but none is the delivered existential with both hom-equivalence formulas.
- Grep: `homEquiv.*over|openRestriction|overPushforwardOverAdj`: fourteen hits,
  including the existing general over adjunction and unrelated over-category results;
  no duplicate of this statement.
- Independent `rg` on source WeilConjectures and project lean/Sheaf for
  `openRestrictionAdjunction|overPushforwardOverAdj|restrictAdjunction|sheafOfModulesEquivOver`:
  scheme specializations and uses of the over equivalence, no duplicate theorem.

H5/H6/H8/H9: no definitions or instances are introduced; the sole theorem has
exactly `by sorry`. Both docstrings carry the source and blueprint id, and the
theorem docstring matches all six proof steps. Sole import is used; lines are
within 100 characters; no variables or universes are unbound. The node's
`lean.statement` agrees verbatim with the declaration signature.

Changes: appended this independent reading only; no mathematical or Lean repair needed.

Second-reader validation: server scompile passed cleanly (2.0 seconds);
`deliver2.py --no-push` printed OK, with preflight and compilation passing.
