## Worker report

The module `Sheaf.AlgebraicGeometry.QuotientMapFppfLocalModels` states
`AlgebraicGeometry.Scheme.quotient_map_fppf_local_models`, with its sole theorem
proof `sorry`. Its helper `AlgebraicGeometry.Scheme.quotientMapFibre` constructs
exactly the presheaf of lifts named G in the node. All its data are explicit:
sections are a subtype of maps to U, and restrictions precompose those maps.
Naturality supplies the equality proof, and the functor laws follow from
identity and associativity. There are no postponed auxiliary theorems.
The helper belongs to the notion explicitly introduced in this item's own
statement, so it is recorded in `lean.declarations`, not as a new independent
notion. No new node, dependency repair or statement correction is needed.

Source read: `literature/stacks-project/spaces.tex`,
`lemma-presentation-quasi-compact`, Tag 0265, especially the first
representability step and its displayed fibre-product computation. The node
interchanges s and t relative to that display and assumes the separatedness
and local quasi-finiteness of s explicitly. The Lean preserves that orientation.
The example CompactObject module in the current clone is withdrawn and contains
no declarations; the current brief's module-mode conventions are followed.

Hypotheses and clauses, in order:

- The base scheme is `{S : Scheme.{u}}`. Schemes over S are `{R U : Over S}`;
  their structural maps and all over-S compatibilities are part of that category.
- The two projections are `(s t : R ⟶ U)`.
  `[Mono (prod.lift s t)]` is the monomorphism into U ×_S U: the product in
  `Over S` is precisely that fibre product.
- `hrel` quantifies over every `W : Over S` and asserts `Equivalence` of the
  relation `∃ r : W ⟶ R, r ≫ s = b ∧ r ≫ t = c`. This is the stated
  pointwise equivalence relation, including reflexivity, symmetry and transitivity.
- `[Etale s.left] [Etale t.left]` are the two étale assumptions, on the
  underlying scheme maps.
- `F : Sheaf (Scheme.fppfTopology.over S) (Type u)` is the sheaf of sets.
  The presheaf `coequalizer (yoneda.map s) (yoneda.map t)` is the pointwise
  quotient U(W)/R(W). `η` and `hη` specify its sheafification by the defining
  universal property: precomposition with η bijects maps to each sheaf H.
  Thus this is the same sheafification as the node, with no extra assumption
  that every Type-u-valued presheaf on the big site admits sheafification.
  This is exactly the interface of `etale_relation_kernel_pair`.
- Everywhere q is the actual composite
  `coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η`; no arbitrary quotient
  map or assumed representability substitutes for this canonical map.
- `[IsSeparated s.left]` and `hs : Scheme.Hom.IsLocallyQuasiFinite s.left`
  are precisely the final two hypotheses on s. The latter is the recorded
  Stacks predicate, including local finite type, rather than Mathlib's weaker
  `LocallyQuasiFinite` alone.
- `(T : Over S)` and `(a : yoneda.obj T ⟶ F.obj)` are arbitrary.
- For `W : Over T.left`, `(Over.map T.hom).obj W` is W as an S-scheme.
  The objects of `quotientMapFibre T F q a` are exactly S-maps b:W→U with
  `q.app ... b = a.app ... (Over.homMk W.hom)`. The right side is a restricted
  to W. The first conclusion `Presheaf.IsSheaf ...` is exactly the claimed
  sheaf condition on the big fppf site of T.
- `I`, `Tᵢ`, and `f` specify a family over T. Membership of the underlying
  `Presieve.ofArrows` in `Scheme.fppfPrecoverage T.left` says that it is
  jointly surjective and its maps are flat and locally of finite presentation.
- `aᵢ : ∀ i, Tᵢ i ⟶ U` are the local lifts. The equality of natural
  transformations `yoneda.map (aᵢ i) ≫ q = yoneda.map (f i) ≫ a` is precisely
  q(a_i)=a restricted to T_i, by Yoneda and naturality.
- The specified model is literally `pullback (aᵢ i).left s.left`, over T_i
  by `pullback.fst`. Its representable presheaf is
  `yoneda.obj (Over.mk (pullback.fst (aᵢ i).left s.left))` on `Over T_i`.
  Restriction of G is `(Over.map (f i).left).op ⋙ quotientMapFibre ...`.
  The existential natural isomorphism e identifies these two presheaves.
- The equation for every W and every x:W→X_i identifies the underlying
  U-map of `e.hom.app ... x` with
  `x.left ≫ pullback.snd (aᵢ i).left s.left ≫ t.left`. It specifies exactly
  the map through t on the R-factor, not merely an unspecified isomorphism.
  Using the inverse orientation h_X_i→G is equivalent to G≃h_X_i.
- The final conjunction gives `IsSeparated` and the recorded
  `Scheme.Hom.IsLocallyQuasiFinite` for every first projection X_i→T_i.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; their instances for schemes come from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies
  `GrothendieckTopology.over`, `Over.map` and restriction.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`; their universal property is
  rendered by η,hη, following the already recorded kernel-pair interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated`, exported
  from `Morphisms.Separated`; no properness hypothesis is introduced.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `Precoverage.IsSiteForCoverings` is the general site-axiom convention.
  Here the concrete fppf topology and `Presheaf.IsSheaf` instantiate the
  node's site and sheaf notions; no redundant site-axiom hypothesis is added.
- The size-convention node has no mathematical declaration. Explicit `u`
  fixes schemes in `Scheme.{u}`, morphisms and quotient sections in `Type u`,
  and covering indices in `Type (u+1)`, as in the kernel-pair and sibling
  quotient-diagonal interfaces. No independent smaller test universe is used.

Proof-only imports are `Sheaf.AlgebraicGeometry.EtaleRelationKernelPair`
(`Scheme.etale_relation_kernel_pair`),
`WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`
(`AlgebraicGeometry.separated_lqf_base_change`), and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
(`CategoryTheory.sheafification_sections_local`). The two Mathlib proof leaves,
`Scheme.fppfPrecoverage_le_fpqcPrecoverage` and fpqc subcanonicity, are already
in the publicly imported Fpqc module. The theorem docstring reproduces all four
proof steps and names their nodes. The generic local-sections theorem uses a
larger value universe on this big site; a proof using the small-valued universal
interface can transport from large-valued sheafification or use the local-image
argument already used in the neighbouring quotient modules. No such transport
is assumed as an additional hypothesis of this statement.

Edge cases checked: T may be empty, the cover index may be empty, and there
are no Nonempty, affine, quasi-compact or Noetherian assumptions on T or U.
For empty U, a section of the quotient can only occur on the empty part, which
is allowed. The diagonal relation s=t=id produces the expected singleton lift
fibres and models T_i. G can have many sections for a nontrivial relation, so
it is a subtype of maps to U, not the subterminal equality-witness construction
used for quotient diagonals. The pullback is along s and the U-projection is t.
No characteristic or coefficient restriction is present.

Searches for reuse (2026-10-24):

- msearch leanfinder, query “For an etale equivalence relation of schemes the
  fppf quotient map has local pullbacks represented by base changes of the
  relation projection”: 8 hits, including étale pullback stability, topology
  and covering results; none states this local model theorem.
- msearch loogle, query `AlgebraicGeometry.Scheme, CategoryTheory.Limits.pullback`:
  12 hits, concerning open immersion pullbacks and pullback restrictions;
  none states the theorem.
- msearch grep, query `quotient.*sheaf|equivalenceRelation|kernelPair` in
  AlgebraicGeometry: 4 hits (EffectiveEpi, IdealSheaf/Subscheme, OpenImmersion),
  none a quotient-sheaf fibre local-model construction.
- msearch leansearch, query “The fibre of the fppf quotient map of an etale
  equivalence relation is a sheaf locally represented by pulling back the
  source projection of the relation”: 8 hits, primarily ordinary scheme
  fibres and setoid/discrete quotient facts; none states this result.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for quotient-sheaf,
  equivalence-relation and kernel-pair names found the existing kernel-pair,
  representable quotient presentation, relation-incidence and quotient-diagonal
  modules. Their declarations were read: none is this statement or this
  presheaf of lifts. In particular the diagonal helper is an equality witness
  and has a different section type. Searches for `quotientMapFibre` and
  `quotient_map_fppf_local_models` in the project and upstream name index
  found no existing declaration. The required item-id search in upstream
  `WeilConjectures` found no attachment.

Validation: scompile.py compiled both the sandbox and destination module names
cleanly (2.2 s and 2.7 s). All variables and the universe are explicit;
`autoImplicit` is false. Every Lean line is at most 100 characters. The existing
node is changed only by adding its lean record. No statement dispute found.

## Second reading by Q60

Author self-check, under the dispatcher's direct-delivery brief; the maintainer
performs the independent review. Reopened the node and the completed module and
matched the hypotheses and conclusions listed above. Checked especially that
hη is the sheafification universal property of the actual quotient coequalizer,
that all test objects are over S, that restriction is to the big site of T_i,
that the model uses s, and that the sectionwise formula uses t. The natural
isomorphism is quantified together with its projection formula, so the map to U
is part of the assertion. Empty covers are allowed and local quasi-finiteness
uses the recorded finite-type-inclusive definition. No mismatch found and no
node fields beyond lean were changed. Compiler fixes concerned naturality
orientation and the functor-law fields of the explicit helper; they changed no
mathematical clause.
