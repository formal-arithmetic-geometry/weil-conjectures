## Worker report

Item: `lem-sp-tensor-counit-exchange-calculus`, group Q123, stage 2.
Module: `Sheaf.CategoryTheory.Adjunction.TensorCounitExchangeCalculus`.
Main declaration: `CategoryTheory.tensorCounitExchangeCalculus`.
Restricted-domain clause: `CategoryTheory.tensorCounitExchangeCalculus_restricted`.

The module states the entire categorical calculation, including equality of the
arrows, the formula for BOTH inverse transposes, and the full-subcategory clause.
Both theorem proofs are `sorry`. Five supporting definitions contain actual data,
constructed solely from the imported categorical interfaces. There are no new
nodes, dependency repairs, or changes to the informal statement.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, paragraph (2).
It transposes the pulled-back tensor map and the tensor map for the base-changed
morphism, uses compact-support base change and projection compatibility, and
identifies the counit at the coefficient unit. The inherited node is the explicit
categorical interface for that paragraph. Its expanded five-step proof is carried
into both theorem docstrings. The node's historical `source` field is preserved.

### Hypotheses and clauses, ordinary adjunctions

Write omega = `G.obj (𝟙_ D)` and omega' = `G'.obj (𝟙_ D')` in this report only;
there are no file-local abbreviations, notations, or let-bound statement terms.

| Node text | Lean rendering |
| --- | --- |
| Four arbitrary monoidal categories | Explicit section binders `C`, `D`, `C'`, `D'`, each with `Category.{v...}` and `MonoidalCategory`, with eight independent object and morphism universes. |
| `F : C -> D`, `F ⊣ G`; likewise primed | The four functor binders and `adj : F ⊣ G`, `adj' : F' ⊣ G'`. Mathlib's adjunction includes the actual unit, counit and triangle identities. |
| `H`, `H'`, `U`, `V` strong monoidal | Four functor binders with `[H.Monoidal]`, `[H'.Monoidal]`, `[U.Monoidal]`, `[V.Monoidal]`. There is no monoidal hypothesis on `F`, `G`, `F'`, or `G'`. |
| Monoidal natural isomorphism `UH ≅ H'V` | `θ : H ⋙ U ≅ V ⋙ H'`, `[NatTrans.IsMonoidal θ.hom]`. Mathlib composition is in diagrammatic order. |
| Specified tensor and composition comparisons | `tensorCounitSourceIso H H' U V θ K M`, built as `tensorIso (θ.app K).symm (Iso.refl _)` followed by `Functor.Monoidal.μIso U _ _`. It is the precise comparison `H'VK ⊗ UM ≅ U(HK ⊗ M)`. Functor composition has the usual definitional object and map identifications. |
| `β : VF ≅ F'U` | `β : F ⋙ V ≅ U ⋙ F'`; no monoidal compatibility of beta is added. |
| `e_K` is the transpose of `V ε_K` after `β_GK^-1` | `(mateEquiv adj adj' β.inv).app K`. The recorded dependency's mate convention gives exactly this transpose; it is not a supplied arbitrary morphism. |
| Projection maps in both variables | `P : ∀ K M, K ⊗ F.obj M ⟶ F.obj (H.obj K ⊗ M)` and the primed version. |
| Both projection transformations are natural | `hP`, `hP'`: `(f ⊗ₘ F.map g) ≫ P K' M' = P K M ≫ F.map (H.map f ⊗ₘ g)`, and its primed analogue. These are joint naturality, for arbitrary arrows in both arguments. |
| Fix `K` | `(K : D)`. |
| Invertibility at exactly the three stated pairs | The three `IsIso` binders for `P K omega`, `P' (V.obj K) (U.obj omega)`, and `P' (V.obj K) omega'`. No global invertibility of either projection family is assumed. |
| `q` and `q'` are the corresponding inverses | Mathlib's `inv` at these three `IsIso` instances. No independently chosen inverse is used. |
| Projection/exchange equation at `M = omega` | `hEx`: first `F'.map` of the source comparison, then `β.inv.app (H.obj K ⊗ omega)`, then `V.map (inv (P K omega))`, then the INVERSE tensorator of V, then `V.obj K ◁ β.hom.app omega`, equals `inv (P' (V.obj K) (U.obj omega))`. This is the displayed node equation with every comparison inserted. |
| `e_1`, including `V1 ≅ 1` | `tensorCounitMateUnit adj adj' β`: the mate component at `𝟙_ D`, followed by `G'.map (Functor.Monoidal.εIso V).inv`. |
| `t_K` is the specified transpose | `tensorCounitTranspose adj H K (P K omega)`, defined as `adj.homEquiv _ _` applied to `inv P ≫ (K ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ K).hom`. |
| Primed tensor-counit transpose | The same definition using `adj'`, `H'`, `V.obj K`, and `P' (V.obj K) omega'`. |
| Equality of maps, with the common source identified | First conjunct: source comparison, then `U.map` of the first tensor-counit transpose, then the mate at K, equals `H'.obj (V.obj K) ◁ tensorCounitMateUnit ...` followed by the primed tensor-counit transpose. Both sides have source `H'VK ⊗ Uomega`. |
| Both inverse transposes are the displayed common map | Second and third conjuncts apply `(adj'.homEquiv _ _).symm` to the respective sides and identify EACH with `tensorCounitCommonTranspose`. |
| Formula for that common map | `tensorCounitCommonTranspose` is `inv (P' VK Uomega)`, followed by `VK ◁ (β.inv.app omega ≫ V.map ε_1 ≫ (εIso V).inv)`, then `(ρ_ VK).hom`. Thus the omitted unit comparison in the informal display is explicit. |
| No invertibility of `e_1`, no faithfulness of evaluation | Neither is a hypothesis; there is no evaluation functor. |

The source comparison is an isomorphism in its stated direction. In particular,
the inverse tensorator of V in `hEx` goes from `V(K tensor Fomega)` to
`VK tensor V(Fomega)`, as required. The right unitor in the common transpose
has source `VK tensor 1_D'`, following the inverse unit comparison of V.

### Full-subcategory clause

This is stated separately by `tensorCounitExchangeCalculus_restricted`, not
inferred by requiring the full subcategories to be tensor closed.

* `PC`, `PD`, `PC'`, `PD'` are arbitrary `ObjectProperty` predicates. Their
  Mathlib `FullSubcategory` categories have the ambient Hom sets, wrapped by
  the induced-category interface.
* Explicit `hF`, `hG`, `hF'`, `hG'` bind the ordinary functors' restrictions to
  those domains. `adj` and `adj'` are adjunctions of the actual restrictions
  constructed by `ObjectProperty.lift`. No ambient adjunction is assumed.
* `tensorCounitRestrictedHomEquiv` composes the inverse Hom equivalence of the
  full inclusion, the specified restricted adjunction's `homEquiv`, and the
  Hom equivalence of the other inclusion. It is precisely the ambient reading
  of the specified Hom bijection, with actual forward and inverse functions.
* `hK`, `h1`, `h1'` put K and both units in the counit domains.
  `hA`, `hB`, `hA'` put `HK tensor omega`, `H'VK tensor Uomega`, and
  `H'VK tensor omega'` in the corresponding transpose domains.
  `hUA`, `hUGK`, `hU1`, `hVK`, `hV1` give the remaining endpoints of the
  restricted Hom naturality and unit-comparison squares. These are exactly
  the node's proviso that every displayed object and map lies in its Hom
  domain; they impose no monoidal closure on a full subcategory.
* `H`, `H'`, `U`, `V`, `θ`, `β`, `P`, `P'`, joint naturality, the three
  `IsIso` hypotheses and `hEx` have the same signatures as in the main theorem.
* `t`, `t'`, `eK`, `e1` are bound together with `ht`, `ht'`, `heK`, `he1`.
  Each equation fixes its arrow by the specified restricted Hom bijection.
  Thus these binders introduce the node's defined transposes and mate
  components, not unconstrained maps or strengthened compatibility assumptions.
  The counits used are `(adj.counit.app ...).hom`, respectively primed.
* The conclusion again has three conjuncts: the equality of the two composites,
  then each inverse restricted Hom transpose equal to the node's common arrow.
  The inverse unit comparison of V and the right unitor are explicit in both
  common-arrow formulas. There is still no invertibility of `e1` or evaluation
  functor. All arrows between objects of a full subcategory are automatically
  arrows of that subcategory, so no map-preservation condition is omitted.

### Dependencies used

All four statement dependencies are Mathlib leaves and have no required project
Lean records to repair. I read their complete `mathlib_match` records and the
actual signatures/docstrings in the pinned source:

* `def-nagata-category`: `Mathlib.CategoryTheory.Category.Basic`,
  `CategoryTheory.Category` and `CategoryStruct` (identities, composition, laws).
* `def-sfb-monoidal-category`: `Mathlib.CategoryTheory.Monoidal.Category`,
  `CategoryTheory.MonoidalCategory` and its structural fields/axioms.
* `def-sfb-strong-monoidal-functor`: `Mathlib.CategoryTheory.Monoidal.Functor`,
  `CategoryTheory.Functor.CoreMonoidal`, its unit/tensor isomorphisms and all
  naturality/coherence fields. `Functor.Monoidal`, `εIso` and `μIso` give its
  Mathlib typeclass interface; these are the same strong-monoidal data.
* `def-weil-pbc-adjunction-mate`: `Mathlib.CategoryTheory.Adjunction.Mates`,
  `CategoryTheory.mateEquiv`. Its `toFun` and `mateEquiv_counit` have exactly the
  node's orientation, and are used directly for the exchange component.

The proof leaves are `CategoryTheory.Adjunction.mkOfHomEquiv` and
`Adjunction.homEquiv_counit` in `Mathlib.CategoryTheory.Adjunction.Basic`
(`lem-weil-pbc-adjunction-of-natural-bijection`), and
`CategoryTheory.mateEquiv_counit` in `Mathlib.CategoryTheory.Adjunction.Mates`
(`lem-amb-mate-unit-counit`). Their modules are already exposed by the statement
imports. The extra imported standard interfaces are
`NatTrans.IsMonoidal` from `Monoidal.NaturalTransformation`, and
`ObjectProperty.FullSubcategory`, `.lift`, `.fullyFaithfulι` from
`ObjectProperty.FullSubcategory`. No private replacement of these notions occurs.

### Searches

The prescribed `msearch.py Q123 lem-sp-tensor-counit-exchange-calculus` calls:

* LeanFinder: "Adjunction mate compatible with inverse projection formula
  intertwines tensor counit transposes". Eight hits, including
  `Adjunction.map_μ_comp_counit_app_tensor`, `mateEquiv_counit`,
  `mateEquiv_counit_symm`, and rigid-category evaluation mate lemmas. None is
  the projection/exchange statement for arbitrary projection families.
* Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv`.
  Zero hits.
* grep: `projection.*(mate|counit)|mate.*projection`, `CategoryTheory`.
  Zero hits in Mathlib.
* LeanSearch: "Naturality of tensor counit transpose under base change
  adjunction mate and inverse projection formula". Eight hits: counit
  naturality, internal-Hom coevaluation naturality, monoidal counit, tensor
  naturality. None states this comparison of projection inverses.

Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed
`grep -rn` for the item id in `lean/WeilConjectures`, found no existing statement
for this node. I also searched the seven proposed declaration names in Mathlib,
WeilConjectures and Sheaf. There is no collision of fully qualified names.

Nearby declarations were opened, not just counted as search hits:

* `WeilConjectures.CategoryTheory.Adjunction.UnitProjection`,
  `Adjunction.map_unitProjection_comp_mateEquiv`, concerns the special
  `unitProjection` associated to a monoidal adjunction. It additionally assumes
  monoidal adjunction structures and comonoidal beta compatibility, and does
  not allow arbitrary H and the projection families of this node.
* `Sheaf.CategoryTheory.CompositeTensorTranspose`,
  `SecSmoothPurity.tensorCounitTranspose`, uses a globally invertible
  `S.ProjectionFormula P` and handles composition of two projections. Here
  only the three specified component inverses exist; replacing them with a
  global projection-formula structure would add a hypothesis. The current
  definition takes a single component, and the theorem takes the jointly
  natural noninvertible families, as the node states.
* `Sheaf.SixFunctors.TensorProjectionAdjunct` concerns a geometric derived
  tensor and a symmetrized projection. Its hypotheses and conclusion differ.
* Mathlib `Adjunction.restrictFullyFaithful` restricts an ALREADY ambient
  adjunction. This node also allows an adjunction that only exists on its
  full subcategories. The restricted Hom helper composes existing Hom
  equivalences of the full inclusions and the given restricted adjunction;
  it does not reconstruct an ambient adjunction or duplicate restriction data.

Thus no exact existing declaration can replace the module. All helpers belong
to the arrows of this node and are listed in `lean.declarations`, as authorized
by the dispatch brief; none introduces an independent mathematical notion.

### Edge cases and validation

* Eight independent universes retain categories with different object/Hom
  sizes. No equality between site sizes or coefficient sizes is introduced.
* No symmetry or braiding is used. All tensors retain their displayed order.
* Only the three named projection components are invertible. `hEx` is assumed
  only at omega. Arbitrary noninvertible components elsewhere remain allowed.
* If all functors are identity functors on vector spaces, projections and theta
  are identities and beta is minus identity, then the mate and e1 are minus
  identity. Both resulting composites are minus the tensor-counit map and both
  transposes are the displayed minus projection. Thus no sign/inverse convention
  silently drops this nontrivial beta case.
* Zero objects and noninvertible e1 are allowed: there is no cancellation by
  e1. The proof only cancels the three stated projection isomorphisms and uses
  injectivity of the actual adjunction Hom bijection.
* Full subcategories need not be tensor closed: the restricted theorem binds
  membership only for the displayed tensor objects, not a global closure
  instance. Empty domains cannot contain the required units/K; this is exactly
  the node's domain proviso, not an extra nonemptiness assumption.
* Both maps have source `H'VK tensor Uomega` and target `G'VK`. Their inverse
  transposes both have source `F'(H'VK tensor Uomega)` and target `VK`.

`set_option autoImplicit false` applies throughout. All universes and variables
are explicitly bound. No let or show appears in a statement. Each declaration
has a source and blueprint docstring; each theorem has the full proof plan.
No Lean line exceeds 100 characters. All writes are in the assigned sandbox.
Compilations use only `scompile.py`, per-file; no global build or direct git
operation was run in the read-only repository.

No `STATEMENT-DISPUTED` issue or statement correction was needed.

## Second reading by Q123

This is a separate second pass by the same dispatched worker: the dispatcher
explicitly forbids starting other agents. I do not claim another worker reviewed
it. The maintainer's independent delivery review remains the independent review.

I reread the node's five proof steps, latest blueprint paragraph (2), and the
complete final module. The first draft had extra monoidal hypotheses on F/G,
which were removed; the node only requires H/H'/U/V strong monoidal. I checked
that joint naturality quantifies over arbitrary first- and second-variable maps,
that the tensorator of V is used in its inverse direction, and that adjunction
forward/inverse transpose directions are correct. I also added both explicit
common-transpose conjuncts; equality alone would omit a clause. Finally I added
the restricted theorem, since a mere instantiation on tensor-closed full
subcategories would not cover the node's weaker domain proviso.

Final clause matching: four monoidal categories and the two adjunctions appear
unchanged; the specified monoidal theta and arbitrary beta are bound with their
correct orientations; hP/hP' render all naturality; the three IsIso binders and
hEx render exactly the specified invertibility and exchange hypotheses;
tensorCounitMateUnit, tensorCounitTranspose, and tensorCounitCommonTranspose
insert the missing source/tensor/unit comparisons explicitly. The three
conjuncts render equality and each common transpose. The restricted theorem uses
only actual restricted adjunctions and explicit endpoint membership; its t/t'/eK/
e1 binders are uniquely fixed by their transpose equations. No inverse of e1,
faithful evaluation, ambient adjunction in the restricted theorem, tensor
closure of its subcategories, monoidal adjunction, or global projection inverse
has been added. I found no remaining mismatch.
