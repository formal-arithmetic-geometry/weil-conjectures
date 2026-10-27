## Worker report

The delivery records an existing declaration family, headed by
`CategoryTheory.StageSystem.Morphism.functor` in
`WeilConjectures.CategoryTheory.StageSystem.Functor`
(`lean/WeilConjectures/CategoryTheory/StageSystem/Functor.lean`). No Lean library module,
definition, theorem, new DAG node, dependency repair or statement correction is introduced.
The item's statement, statement dependencies and nine-step proof are unchanged. The
`lean.declarations` list records the constructions and formulas for every clause, rather
than attaching only the functor and leaving the transformation/composition clauses unrecorded.
The primary signature is verbatim from the existing source before `where`.

I read the whole item, its dependency's statement and Lean record, and the full signature and
docstring of `CategoryTheory.StageSystem.ExactStagePairData` in
`Sheaf.CategoryTheory.ExactStagePairData`. That structure's `system` is the existing
`CategoryTheory.StageSystem`. This item uses the general stage system and pair category
from the dependency's first paragraph, not the optional exact-stage pair datum in its
second paragraph. In particular this attachment imposes no preadditivity, zero object,
shift, pretriangulation, exactness or faithfulness hypotheses.

I also read `StageSystem.Basic` at the `StageSystem`, transport, `PairCategory`,
representative/equivalence, inclusion and canonical comparison definitions, and the whole
`StageSystem.Functor` file, including the proofs of its existing theorems. Its data and
constructions have no `sorry`. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`
was read: its clause 4 gives the coefficient two-colimit context. The item's source refers
to the retained old argument 7 and explicitly names the generic StageSystem implementation;
I do not claim that the historical argument occurs verbatim in the current unit.

### Hypotheses and every conclusion clause

In the following all short names belong to `CategoryTheory.StageSystem`, and all
`Morphism.*` declarations are in `WeilConjectures.CategoryTheory.StageSystem.Functor`.
Lean's `f ≫ g` means first `f`, then `g`, whereas the node writes compositions right to left.

1. An arbitrary nonempty directed preorder is rendered by `I : Type w`, `[Preorder I]`,
   `[IsDirectedOrder I]`, with `[Nonempty I]` when restricting to the node's stated setting.
   The existing construction actually works without a nonemptiness assumption: it chooses
   upper bounds only for indices already present. This does not exclude the nonempty case.
   The object/morphism universes are independently `u,v`, `u',v'`, and `u'',v''`; no
   relation to `w` is imposed. `C : I → Type u` with `[∀ i, Category.{v} (C i)]`, and the
   corresponding `D,E`, are the node's category families. `S : StageSystem C`,
   `S' : StageSystem D`, and `S'' : StageSystem E` are precisely its stage systems.
2. `StageSystem.T`, `.assoc`, and `.cocycle` are exactly the transition functors,
   associator isomorphisms and pentagon. The structure has no unitor field and no field
   normalizing reflexive transitions or repeated-index associators. The category is the
   literal `S.PairCategory`, with pairs `⟨i,x⟩`, quotient morphisms and `S.ι i` as inclusions.
3. `F : Morphism S S'` has `F.Φ i : C i ⥤ D i` and
   `F.β h : F.Φ i ⋙ S'.T h ≅ S.T h ⋙ F.Φ j`. Its field `F.coh h h' x` is verbatim the
   node's tower equation after reversing composition notation:
   `(S'.T h').map ((F.β h).hom.app x) ≫
   (F.β h').hom.app ((S.T h).obj x) ≫
   (F.Φ k).map ((S.assoc h h').hom.app x) =
   (S'.assoc h h').hom.app ((F.Φ i).obj x) ≫ (F.β (h.trans h')).hom.app x`.
   There is no further identity or exactness condition in this structure.
4. `F.functor : S.PairCategory ⥤ S'.PairCategory` is an actual quotient-map construction,
   not a choice from an existence statement. `Morphism.functor_obj` says
   `F.functor.obj X = ⟨X.stage, (F.Φ X.stage).obj X.obj⟩`; it is `rfl` in the existing source.
   Thus the object formula is literal, as required.
5. `F.mapAt u` is the explicit composite
   `(F.β hi).hom.app x ≫ (F.Φ n).map u ≫ (F.β hj).inv.app y`.
   This is exactly `b_jn,y⁻¹ ∘ Φ_n(u) ∘ b_in,x`. `Morphism.functor_map_mkHom` says that
   `F.functor.map (PairCategory.mkHom n hX hY u)` is `PairCategory.mkHom` at the very same
   stage with that composite. `Morphism.tr_mapAt` proves compatibility with the existing
   transport, and the actual functor definition uses it to respect representative equality.
6. `F.ιCompFunctorIso i : S.ι i ⋙ F.functor ≅ F.Φ i ⋙ S'.ι i` is the requested inclusion
   comparison, in exactly the node's orientation. `ιCompFunctorIso_hom_app` and
   `ιCompFunctorIso_inv_app` both give `𝟙 _`. `Morphism.functor_map_ι` is the literal
   equality on stage arrows; it uses naturality of the actual supplied `β (le_refl i)`.
7. For `F,G : Morphism S S'`, `τ : Morphism.Hom F G` consists of
   `τ.τ i : F.Φ i ⟶ G.Φ i` and the equation
   `(S'.T h).map ((τ.τ i).app x) ≫ (G.β h).hom.app x =
   (F.β h).hom.app x ≫ (τ.τ j).app ((S.T h).obj x)`.
   This is exactly the node's transformation compatibility, with no extra condition.
   `Morphism.descNatTrans τ : F.functor ⟶ G.functor` is an actual natural transformation;
   `descNatTrans_app` gives its component
   `(S'.ι X.stage).map ((τ.τ X.stage).app X.obj)`. This is the requested inclusion of η.
8. `Morphism.Hom.id` and `Morphism.Hom.comp` are the compatible identity and vertical
   composition families. `descNatTrans_id` states `descNatTrans (Hom.id F) = 𝟙 _` and
   `descNatTrans_comp` states
   `descNatTrans (τ.comp τ') = descNatTrans τ ≫ descNatTrans τ'`.
   Equations between families are preserved because `descNatTrans` is a function; equality
   of stage transformations is equality of `Hom` by its generated extensionality theorem
   (the compatibility fields are proofs). For compatible inverse families, `descNatIso`
   takes the two inverse equations `τ.comp τ' = Hom.id F` and `τ'.comp τ = Hom.id G`
   and constructs the isomorphism whose hom and inv are their actual descents. Also
   `isIso_descNatTrans` says that a stagewise invertible transformation descends invertibly.
   Together these give the equation and inverse clauses without any faithful inclusion.
9. `Morphism.id S` has `Φ i := 𝟭 _` and `β h := Iso.refl _`, with the tower verified.
   `id_β_hom_app` gives the identity comparison component. `functorIdIso` has type
   `(Morphism.id S).functor ≅ 𝟭 S.PairCategory`; its hom and inv components are identities
   by `functorIdIso_hom_app` and `functorIdIso_inv_app`. `functor_id_map` also records
   literal equality on every arrow.
10. For a third independent family and system, `G : Morphism S' S''`, `F.comp G` has
    stage functors `F.Φ i ⋙ G.Φ i`. The theorem `comp_β_hom_app` states that its comparison
    is `(G.β h).hom.app ((F.Φ i).obj x) ≫ (G.Φ j).map ((F.β h).hom.app x)`, exactly
    `Γ_j(b_ij,x) ∘ d_ij,Φ_i x`. The definition's `coh` verifies the analogous tower using
    the two supplied towers and naturality. `functorCompIso F G` has type
    `(F.comp G).functor ≅ F.functor ⋙ G.functor`; `functorCompIso_hom_app` and
    `functorCompIso_inv_app` give identity components. `functor_comp_map` gives literal
    equality of its arrow map with successive descent.
11. All index comparisons are weak inequalities and permit repeated indices. No field
    or theorem used above requires strict inequalities, faithful transitions, exact
    transitions, unitors, or any normalization of `T (le_refl i)` or `β (le_refl i)`.

These existing declarations jointly supply the full multi-clause node. In particular this
is not an attachment to a normalized pseudofunctor result or to the normalized neighboring
node `lem-sbc-coherent-pair-functor-descent`.

### Edge cases and existing-proof correspondence

I checked singleton indices with identity transitions, singleton indices with nonidentity
idempotent transitions (including the zero functor when the category has a zero object),
and repeated indices in the tower and representative formulas. The latter are explicitly
allowed in `coh`, `mapAt`, `Hom.comm` and `comp`. None of these calculations cancels a
transition functor. Identity transformations, zero arrows where present, invertible
transformations, and identity/composite family comparisons are covered by the declarations
listed above. Empty individual stages cause no extra hypothesis; empty I is outside the
node's stated hypothesis and is harmless in the existing more general API.

The existing `tr_mapAt` proof performs the node's steps 1--2: it rearranges `coh` and
`coh_inv`, then uses naturality and cancellation. The quotient functor's `map_id` and
`map_comp` give step 3. `mapAt_map`, `functor_map_ι` and `ιCompFunctorIso` give step 4.
`S'.ι_map_eq` in Basic supplies the common-stage component formula of step 5.
`Hom.mapAt_naturality` and `descNatTrans` implement step 6. `Hom.id`, `Hom.comp`,
`descNatTrans_id`, `descNatTrans_comp`, `descNatIso` and `isIso_descNatTrans` implement
step 7. The definitions `id`, `comp`, `functorIdIso` and `functorCompIso` and their component
formulas implement steps 8--9. This correspondence uses the current source, not an old
unverified sorry-map or a prior attachment recommendation.

### Searches and prior attachment

The prescribed `msearch.py` searches were run for this item; their actual receipts remain
in the sandbox's `searches.jsonl`:

- LeanFinder: "Coherent functors and natural transformations descend to an unnormalized
  directed stage pair category with identity and composite comparisons". Eight hits,
  including `Functor.IsLocallyDirected` and indization/small-object constructions; none
  constructs this quotient functor and the complete transformation/composition interface.
- Loogle: `CategoryTheory.NatTrans, CategoryTheory.Functor`. Twelve hits on natural
  transformations, identities, vertical composition and extensionality; these are the
  underlying categorical notions, not the directed-stage descent construction.
- Mathlib grep in `CategoryTheory`: `StageSystem|descNatTrans|functorCompIso`. The 25
  reported substring hits are unrelated `shiftFunctorCompIsoId`, fiber and essential-image
  comparisons. No Mathlib stage-system descent declaration was found.
- LeanSearch: "Functor and natural transformation descent for associative nonunital
  directed systems of categories, including identity and composition comparisons".
  Eight hits including pseudofunctor descent data, sigma-category descent, and ordinary
  natural transformations. These use different input data or different categories.
- Local `rg` in `lean/WeilConjectures` for the item id found no blueprint-tag match.
  Searching `StageSystem/Functor.lean` by the construction names found all declarations
  recorded here. Their full signatures, docstrings and bodies were read, rather than
  treating an absent tag as evidence that no implementation exists.
- Local `rg` in `lean/Sheaf` found users of the exact upstream `StageSystem.Morphism`
  construction, including `StageSystemAdjunction` and `SfFrameworkCommonStageDescent`;
  no separate definition of the generic nonunital construction is needed. The dependency's
  `ExactStagePairData` is reused as recorded and not copied.

The stage-1 report `coord/reports/NP/lem-pur-associative-stage-family-descent.md` says the
prior attachment could not be verified against the earlier supplied tree. It does not
identify a mathematical defect in these declarations. The current read clone contains
the implementation in full. This delivery retains the accepted stage-1 split and checks
the recorded declarations in the current server environment using `scompile.py`.
No item-specific repair note was present. No `STATEMENT-DISPUTED` issue was found.

### Validation

A module-mode scratch probe imports both the existing descent module and the dependency's
recorded `Sheaf.CategoryTheory.ExactStagePairData` module, sets `autoImplicit false`, and
checks all 31 names in `lean.declarations` with their full types. The prescribed
`scompile.py` completed successfully with exit code 0, no warnings, and a reported
compile time of 1.5 seconds. The probe is not a delivered library module. The required dry run and
delivery also compile the wrapper-generated existing-declaration probe and run the server
preflight. The maintainer provides the independent review; no independent second reading
by this worker is claimed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
