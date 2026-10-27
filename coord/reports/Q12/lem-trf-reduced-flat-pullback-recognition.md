## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedFlatPullbackRecognition` states
`AlgebraicGeometry.reduced_flat_pullback_recognition`, with one `sorry` and no new
construction. The returned delivery's H2 is repaired by adding the existing owning node
`def-sfb-tensor-pullback-structure-sheaf-map` to `stmt_deps` and citing it at the
canonical map, with a §1(C) `statement_change` and complete two-citer audit.
The mathematical statement and Lean module are unchanged. There are no new nodes,
dependency modules, or disputed mathematical assertions.

Clause-by-clause correspondence:

- Schemes T, X, Y: `{T X Y : Scheme.{u}}`, with explicitly declared universe `u`.
- Closed immersion i:T→X: `(i : T ⟶ X) [IsClosedImmersion i]`.
- Its ideal I=ker(O_X→i_*O_T): `i.ker`, with its module `i.ker.toModules`
  and inclusion `i.ker.toModulesι`. A closed immersion is quasi-compact, so the
  existing `Scheme.Hom.ker_apply` gives the actual kernel ideal on each affine open.
- Closed image Z=i(T): `Set.range i`. For the closed-set argument to vanishingIdeal,
  the statement uses the existing bundled closed subset `i.ker.support`.
  `Scheme.Hom.support_ker i` identifies it with `closure (Set.range i)`;
  `i.isClosedEmbedding.isClosed_range` makes this equal to `Set.range i`.
- Flat g:Y→X: `(g : Y ⟶ X) [Flat g]`, with no surjectivity assumption.
- P=T×_X Y and q:P→Y: `pullback i g` and `pullback.snd i g`, respectively.
- P reduced: `[IsReduced (pullback i g)]`. There is no reducedness binder on T,
  X, or Y, and no Noetherian or finiteness binder.
- q closed: the first conjunct `IsClosedImmersion (pullback.snd i g)`.
- q(P)=g^{-1}(Z): the second conjunct
  `Set.range (pullback.snd i g) = g ⁻¹' Set.range i`.
- The canonical arrow g*I→O_Y is the composite
  `(Scheme.Modules.tensorPullback g).map i.ker.toModulesι ≫
    Scheme.Modules.tensorPullbackObjUnitToUnit g`.
  Its second factor is the existing canonical adjoint of g-sharp under the
  section-normalized tensor adjunction, not an arbitrary chosen map.
- Injectivity: the third conjunct asserts `Function.Injective` for this
  composite's `.app U` on EVERY `U : Y.Opens`, including nonaffine opens.
- Its sheaf image equals I_{g^{-1}(Z)}: the fourth conjunct is equality of
  `imageSubobject` of this composite with `Subobject.mk` of the existing
  vanishing ideal's inclusion into O_Y. This is equality of subsheaves, not
  merely an isomorphism of their underlying modules or an equality of supports.
  The bundled inverse image is `i.ker.support.preimage g.continuous`, which
  is g^{-1}(Z) by the preceding identification of `support`.
- Unique isomorphism over Y: the last conjunct is `∃! e` of type
  `pullback i g ≅ (vanishingIdeal ...).subscheme`, with compatibility
  `e.hom ≫ (vanishingIdeal ...).subschemeι = pullback.snd i g`.
  The order of categorical composition renders i_W composed with e exactly.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`, its affine
  kernel formula, `Scheme.Hom.support_ker`, and `Scheme.IdealSheafData.vanishingIdeal`
  (def-sbc-closed-immersion-ideal-sheaf and the reduced-induced dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (def-weil-flat-morphism); its documentation explains equivalence to stalkwise flatness.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (def-pc-reduced-scheme), the sectionwise equivalent of reduced local rings.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, with its public imported
  `WeilConjectures.AlgebraicGeometry.TensorPullback` functor
  `Scheme.Modules.tensorPullback` (def-pc-module-pullback).
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, read in full,
  including the ideal equality and unique compatible isomorphism in clause (3).
  Its public ideal-module infrastructure supplies `toModules`, `toModulesι`,
  `subscheme`, and `subschemeι`. Only this upstream version is imported.
- `def-sfb-tensor-pullback-structure-sheaf-map` (Q73, landed 2026-10-23):
  `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`,
  `Scheme.Modules.tensorPullbackObjUnitToUnit` and its documented normalization.
  This is the already existing structure-sheaf comparison, not a replacement.
- Supporting categorical import: `Mathlib.CategoryTheory.Subobject.Limits`
  provides `imageSubobject` and the subobject language.
- Proof-only imports are the recorded `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`
  and `Mathlib.AlgebraicGeometry.PullbackCarrier`; the latter contains
  `Scheme.image_preimage_eq_of_isPullback` (the mathlib_match for the image node).
  Record diagnostic: lem-pc-closed-imm-base-change currently points to
  `IsVeryAmple.pullback_of_field`, which is only a field-extension ampleness result,
  not its general ideal formula. It is retained as the prescribed proof-dependency
  import, but no statement relies on that narrower signature. The general ideal-image
  interface also exists as `AlgebraicGeometry.closedSubscheme_baseChange_ideal_image`
  in `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`.
  No repair of a proof-only node is included in this statement delivery.

Sources checked locally: `literature/stacks-project/schemes.tex`, labels
`lemma-fibre-product-immersion` (01JU), `lemma-points-fibre-product` (01JT),
`lemma-reduced-closed-subscheme` (01J3), and `definition-reduced-induced-scheme`
(01J4). They give the ideal image, point-image formula, and reduced recognition
with uniqueness. The module docstring gives the node's complete three-step proof.

Edge cases checked before writing:

- Empty T: the original ideal is the unit ideal, its flat pullback maps
  isomorphically onto O_Y, and the target reduced subscheme is empty.
- Empty Y or empty P: no nonemptiness binder excludes these cases. If P is
  empty, its ideal is the unit ideal and the unique isomorphism is between
  the empty schemes over Y.
- Nonreduced ambient Y: take X=Y=Spec(k[ε]/ε²), g=id, and i:Spec(k)→X.
  P is reduced; its ideal and the vanishing ideal of the whole topological
  space are both (ε). The statement includes this case.
- Nonreduced T is genuinely allowed: take i=id on the disjoint union of
  Spec(k) and Spec(k[ε]/ε²), with g the open inclusion of the reduced component.
  P is reduced while T is not, and all conclusions hold.
- Non-Noetherian X: X=Spec(k[x₁,x₂,...]), i=V(x₁), g=id has reduced P and
  satisfies the statement, with no finite-generation condition on X.
- Flatness is necessary for injectivity: i=g:Spec(k)→Spec(k[t]) at t=0
  gives the zero map k≅g*(t)→k, which is not injective.
- Reducedness of P is necessary for the vanishing ideal identification:
  g=id and i=V(t²) in Spec(k[t]) has kernel (t²), while the reduced ideal is (t).
- Zero ideal/full closed subset and unit ideal/empty closed subset use the
  existing vanishingIdeal construction, including ambient nilpotents.

Searches (2026-10-24):

- msearch.py leanfinder: "flat base change closed immersion ideal pullback
  injective reduced induced closed subscheme": eight hits, including Flat,
  Flat.isStableUnderBaseChange, IsClosedImmersion.Spec_iff and
  IsClosedImmersion.isIso_of_injective_of_isAffine. None is the full statement.
- msearch.py loogle: "AlgebraicGeometry.Scheme.Hom.ker,
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal": zero hits.
- msearch.py grep: "ker.*pullback|pullback.*ker|vanishingIdeal" restricted to
  AlgebraicGeometry/IdealSheaf: ten hits; vanishingIdeal and the comap/kernel
  formulas exist, but not the full recognition statement with the flat ideal map.
- msearch.py leansearch: "flat pullback closed immersion ideal reduced induced
  subscheme unique isomorphism": eight hits, including isIso_lift,
  isIso_of_ker_eq, ker_fst_of_isClosedImmersion, and the closed-immersion/ideal
  equivalence. None includes this statement's three clauses together.
- rg in lean/WeilConjectures and lean/Sheaf for canonical ideal/base-change
  names and reduced pullback found IdealTensorPullbackComparison,
  ClosedSubschemeBaseChangeIdealImage, FlatClosedFamilyIdealBaseChange,
  EtaleReducedCartierDescent, and ReducedInducedClosedSubscheme. Their full
  signatures were inspected: the first two supply the general image comparison,
  the family result has different hypotheses, and the etale result is specialized.
  The exact item is not already declared.
- rg for the item id in lean/WeilConjectures gave no hit; rg for
  `reduced_flat_pullback_recognition` in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json gave no hit. The module introduces no notion.

Validation: scompile.py Q12 lem-trf-reduced-flat-pullback-recognition compiled the
sandbox and final library module separately, cleanly, in 2.0 s and 2.1 s.
All variables and the universe are bound explicitly; there are no local notations,
local instances, auxiliary theorem proofs, or hidden data sorries.

## Second reading by Q12

I reopened the node and final Lean module for a separate clause-by-clause pass;
no additional agent was started, as required by the dispatcher brief. Independent
review is the maintainer's delivery review.

I checked the direction of the fibre product and projection (`pullback i g`,
`snd`, not `fst`), the domain of tensor pullback (the ideal on X), and the
normalization of the final structure-sheaf comparison. I checked that the
injectivity quantifier ranges over every open of Y, and that image equality is
in the subobjects of the very same O_Y. The vanishing ideal uses the inverse
image of i.ker.support, not an arbitrary closed subset; support_ker and closedness
of the image identify it with exactly the node's g^{-1}(i(T)). I checked that
`∃!` quantifies over isomorphisms and that its commuting equation expresses
compatibility over Y. The only geometric hypotheses are the closed immersion,
flatness, and reducedness of the chosen pullback. No clause or edge case is lost.
On repair I reopened the added dependency node and its upstream declaration.
It owns exactly the second factor `tensorPullbackObjUnitToUnit g` already used
in the canonical ideal map. The missing ownership citation and statement-dependency
edge are now present. All binders and clauses in the Lean file remain identical
to the reviewed version; both citers retain their applications.

## Statement corrected

Repair of H2 in the maintainer return for immutable head `ea215bf4c973`.
The old statement, verbatim:

Let $i:T\hookrightarrow X$ be a closed immersion of schemes [def-pc-scheme, def-weil-closed-immersion], with ideal sheaf $\mathcal I=\ker(\mathcal O_X\to i_*\mathcal O_T)$ [def-sbc-closed-immersion-ideal-sheaf] and closed image $Z=i(T)$. Let $g:Y\to X$ be flat [def-weil-flat-morphism], and write $P=T\times_XY$ and $q:P\to Y$ for the pullback and its projection [def-pc-fibre-product]. Assume that $P$ is reduced [def-pc-reduced-scheme]. Then $q$ is a closed immersion with image $g^{-1}(Z)$, and the canonical map $g^*\mathcal I\to\mathcal O_Y$ [def-pc-module-pullback] is injective with image equal to the vanishing ideal $\mathcal I_{g^{-1}(Z)}$ [lem-weil-pbc-reduced-induced-closed-subscheme]. There is a unique isomorphism $e:P\xrightarrow{\sim}(g^{-1}(Z))_{\mathrm{red}}$ over $Y$, so that $i_{g^{-1}(Z)}\circ e=q$, where $i_{g^{-1}(Z)}$ is the reduced induced closed immersion. No reducedness of $T$ or Noetherian hypothesis on $X$ is assumed.

What was wrong: the canonical ideal arrow's second factor is the existing
`Scheme.Modules.tensorPullbackObjUnitToUnit`, owned by
`def-sfb-tensor-pullback-structure-sheaf-map`. The original statement cited only
`def-pc-module-pullback` at that map; its record does not own the comparison.
The corrected citation is `[def-pc-module-pullback,
def-sfb-tensor-pullback-structure-sheaf-map]`, and `stmt_deps` gains the latter
node. This is a citation/interface correction only. The Lean source, proof,
proof dependencies, and every mathematical hypothesis and conclusion are retained.

Source checked: Stacks Schemes Tag 01JU, `lemma-fibre-product-immersion` (1),
uses the canonical arrow g*I→O_Y; Sheaves Tag 0096,
`lemma-adjoint-pullback-pushforward-modules`, supplies its adjoint
structure-sheaf comparison. The added dependency states exactly that canonical
comparison and records the existing upstream declaration. Its defining expression
is the inverse Hom adjunction bijection applied to `unitToPushforwardObjUnit`.

Complete citer audit, from the recursive item-id search in `dag/nodes` followed
by checking `stmt_deps` and `proof_deps` of every hit:

- `lem-trf-etale-reduced-cartier-descent`: holds true. Step 1 still applies recognition to the flat etale pullback with reduced source; the canonical-map citation adds no hypothesis and changes no conclusion.
- `lem-trf-resolution-word-finite-history-comparison`: holds true. Step 6 still identifies the extended stratum ideal under smooth flat pullback; the additional citation only records the existing canonical structure-sheaf map.

No citer is edited. `statement_change.old_stmt_deps` preserves the old list;
`old_proof` and `old_proof_deps` are absent because neither field changes.
There was no previous statement_change to preserve. Current main and the retained
returned node were compared field by field before the repair: their only difference
was the returned `lean` attachment. Current main's remaining fields are preserved.
The delivery wrapper performs its normal refresh and builds the repair on current
main; no direct Git command or shared-repository write was performed.
