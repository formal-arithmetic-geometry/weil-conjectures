## Worker report

The module states the termwise computation of the derived exchange morphism on a bounded-below
complex.  For a commutative square `sq : CommSq g' f' f g` and a bounded-below complex `K`,
the left side applies the derived inverse image to the right-derived direct-image unit and
then the derived exchange map.  The right side is the comparison isomorphism for the
termwise inverse image, followed by the image under `Q` of the underived base-change map,
and then the right-derived direct-image unit for `f'`.

The hypotheses are rendered by the explicit binders `A`, its category, abelian and
Grothendieck-ab-elian instances, `HasSmallSiteSheafify`, the schemes and morphisms
`X' X Y' Y`, and the commutative square `sq`.  The object clause is the binder
`K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)`.  The displayed equality in the
node is rendered verbatim by the conclusion of `derivedExchangeTermwise`; all functors and
comparison maps are the recorded declarations from the derived base-change development.
The proof is intentionally `sorry` at stage 2.

Dependencies used are `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`,
`AlgebraicGeometry.Etale.baseChangeMap`, and the derived-category constructions imported
from `WeilConjectures.SixFunctors.BaseChange.Derived`.  The statement is the canonical
component formula supplied by the existing derived-base-change API; it is the concrete
encoding of the node's `sigma_src`, `sigma_tgt`, and `Q(e)` comparison.

Edge cases checked: the bounded-below object is arbitrary (including the zero complex and
empty schemes), and no nonemptiness, finiteness, or degree restriction is introduced.
Universes are explicit and no auto-bound variables are used.

Searches: `rg` over `WeilConjectures/SixFunctors` for derived exchange and termwise
construction; `rg` over `lean/Sheaf` for existing declarations; and the recorded node
mathlib searches (LeanFinder, Loogle, and Mathlib grep), all finding no separate theorem
for the termwise comparison.  The source declaration
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app` is the underlying API formula;
the present declaration records the node under its own blueprint name.

## Earlier second reading (a previous round; superseded)

The module and node were reread independently.  The binders match the square and bounded
below complex in the source encoding, and each displayed composition is present in the same
order.  No mismatch was found; the only stage-2 omission is the proof, which is correctly
left as `sorry` for the next stage.

## Second reading by G1

Independent review of the node, the delivered module, every statement dependency and its
recorded declaration, and the sources. The original Worker report above describes the
superseded file; its claim that the unit-factorization formula renders all of the node is
incorrect. I rewrote that formula, without changing the node's statement or dependencies.
There is no statement correction, new definition node, or dependency module in this delivery.

Source reading: I read the blueprint source on the server at the node's exact recorded path
(the local literature tree is not populated), and Stacks `sites-cohomology.tex` at
`lemma-base-change-map-flat-case` (0736) and `remark-base-change` (07A7), and `derived.tex`
at `lemma-pre-derived-adjoint-functors` (0DVC), `lemma-K-injective` (070I),
`lemma-bounded-below-injectives-K-injective` (070K). The Stacks .tex was available locally
in `/home/ubuntu/c1-stacks-review/`. 0736 assumes a commutative diagram of ringed topoi,
a bounded-below complex, and flat horizontal maps; in this node the topoi are the small
etale topoi and both inverse images on abelian sheaves are exact, so there is no extra
flatness condition on the scheme morphisms. 07A7 gives the derived mate for an arbitrary
derived object. Neither source assumes properness, Noetherian schemes, a field, torsion,
or finite coefficients for construction of the map. The comparison between the two
constructions is the agent-written seven-step proof in the node, not a purported verbatim
Stacks theorem. I checked that proof as well as its stated hypotheses.

Objects, hypotheses and conclusions, matched individually:

| Node item | Lean rendering and verdict |
| --- | --- |
| Schemes X', X, Y', Y and four arrows | The explicit `Scheme.{u}` and morphism binders have exactly the displayed directions. Pass. |
| Cartesian square, chosen identification, and its equality | `sq : IsPullback g' f' f g`; `sq.toCommSq` supplies the equality used by the recorded `squareUpperStarIso`. The universal identification with the pullback is encoded by `IsPullback`; neither exchange depends on additional choices. Pass. |
| Abelian sheaves on the small etale sites | `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, exactly the encoding of the abelian-sheaf and derived-category dependency records. The original generic coefficient category `A` was removed. Pass. |
| Sheaf inverse and direct images, with adjunctions | `G`, `G'`, `F`, `F'` abbreviate the recorded `Etale.upperStar` and `Etale.lowerStar`. Their recorded `upperStarLowerStarAdjunction` gives the mates in `baseChangeMap`. These are the actual functors, not private copies. Pass. |
| Localization Q on complexes and on homotopy classes | `q`, `q'`, `qY` are the homotopy quotient functors; `DerivedCategory.Qh` localizes their images. `DerivedCategory.quotientCompQhIso` canonically identifies these composites with `DerivedCategory.Q`. The statement consistently uses this identification for s, j and e. Pass. |
| Derived inverse images and comparisons phi | `G.mapDerivedCategory` and `G'.mapDerivedCategory`, with `mapDerivedCategoryFactorsh`. The latter's hom is phi and its inverse is used in sigma_src. On D+ these are the recorded `mapDerivedCategoryPlus`; its compatibility with inclusion is `Iso.refl`. Pass. |
| Derived direct images on D+ | `F.rightDerivedFunctorPlus` and `F'.rightDerivedFunctorPlus`, the same functors used by the recorded `Etale.rightDerivedLowerStarPlus`. The chosen injective representative is exposed using the existing `injectiveObjectEquivalence`, not a second derived functor. Pass. |
| Chosen bounded-below K-injective I(L) and rho_L | `P` and `P'` are the images of `E.inverse.obj K` and `E'.inverse.obj K'` under `InjectiveObject.ι`; `ρ` and `ρ'` are the inclusions of the inverses of the equivalences' counit isomorphisms. They are actual bounded-below complexes of injectives. Pass. |
| Unique homotopy class h with Q(h) t = rho_L | `∃! h : ((q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj))` together with `s.hom ≫ Qh.map h.1 = ρ` and `t ≫ Qh.map h.2 = ρ'` gives exactly the two comparisons needed here, with uniqueness in the homotopy category. The generic preamble defines how to form these comparisons; it is not an extra unrelated assertion about all functors. Pass. |
| h is a homotopy equivalence | `IsIso h.1 ∧ IsIso h.2` in the homotopy categories. No extra equivalence hypothesis is assumed. Pass. |
| chi_(P,t) = Q(u_*h), an isomorphism | `χ` and `χ'` apply termwise direct image to the respective h and then `Qh`. The final factor is the canonical identification of the chosen-representative output with the existing right-derived functor: `rightDerivedFunctorPlusUnit.app P ≫ rightDerivedFunctorPlus.map (E.counitIso.hom.app K)` (and its primed analogue). This is the inverse of `rightDerivedFunctorPlusIsoInjectiveObject`, by `rightDerivedFunctorPlusIsoInjectiveObject_inv_app`. `IsIso χ` and `IsIso χ'` state the claimed invertibility. Pass. |
| K in D+(X_et), not a selected bounded-below complex | `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`; `Plus` means bounded below in cohomology. Pass. |
| Arbitrary K-injective complex I and isomorphism s:K ≅ QI | `I : CochainComplex ... ℤ`, `[I.IsKInjective]`, and `s : Plus.ι.obj K ≅ Qh.obj (q.obj I)`. There is no degree bound or degreewise-injective condition on I. Pass. |
| K-injective resolution j:g'^{-1}I → J | `J : CochainComplex ... ℤ`, `[J.IsKInjective]`, actual complex map `j`, `[QuasiIso j]`. This is exactly the dependency's `QuasiIso j ∧ J.IsKInjective` clause, using the recorded Mathlib notions directly; its module-specific abbreviation is for ModuleCat sheaves, whereas this node is about abelian sheaves. No competing resolution predicate is introduced. Pass. |
| (a) termwise underived exchanges form a complex map | `ex₀ := (NatTrans.mapHomologicalComplex (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I` has the required complex-morphism type. The first conclusion explicitly states `∀ n : ℤ, ex₀.f n = (Etale.baseChangeMap B sq.toCommSq).app (I.X n)`. Pass. |
| (a) e = f'_*(j) composed with Ex^0_I | `e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j`. Lean composition runs left to right, so this is exactly the displayed mathematical composite. Pass. |
| (b) t = Q(j) phi_(g',I) g'^{-1}(s) | `t := G'.mapDerivedCategory.map s.hom ≫ G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫ Qh.map (q'.map j)`. It is automatically an isomorphism from s and QuasiIso j; no extra assumption about t is made. Pass. |
| (b) sigma_src = g^{-1}(chi) composed with phi^-1 | `σsrc := G.mapDerivedCategoryFactorsh.inv.app (F.mapHomotopyCategory ... .obj (q.obj I)) ≫ G.mapDerivedCategory.map χ`; `IsIso σsrc` states the source identification is an isomorphism. Pass. |
| (b) sigma_tgt = chi_(J,t) | `χ'` is exactly this comparison; its codomain is the inclusion of `F'.rightDerivedFunctorPlus.obj K'`, with `K' := G'.mapDerivedCategoryPlus.obj K`. Pass. |
| (b) Ex_K sigma_src = sigma_tgt Q(e) | Final equality `σsrc ≫ Plus.ι.map ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) = Qh.map (qY.map e) ≫ χ'`. Both sides are in the unbounded derived category so arbitrary I and J are accepted. `Plus.ι` is fully faithful: this is the node's equality, not just a cohomological consequence. Pass. |

The unique comparison pair is packaged together with its isomorphism properties and the
exchange equality. Uniqueness of the pair is precisely uniqueness of each lift in 070I;
the remaining clauses are conclusions, not stronger hypotheses. The choices of P and P'
instantiate the node's chosen I(L), rather than requiring the user to supply new data.

Dependency signature reading: I opened `WeilConjectures/SixFunctors/BaseChange/Square.lean`
(`squareUpperStarIso`, `baseChangeMap` and its counit lemma),
`SixFunctors/Etale/UpperLowerStar/Defs.lean` (`lowerStar`, `upperStar`,
`upperStarLowerStarAdjunction`), the source's and Mathlib's
`Algebra/Homology/DerivedCategory/ExactFunctor.lean` (unbounded and Plus functors and
factorizations), the source's `RightDerivedFunctorPlus.lean` (shift and triangulated
instances, injectiveObjectEquivalence, the representative comparison), Mathlib's
`DerivedCategory/Basic.lean`, `Plus.lean`, `KInjective.lean` (Q, Qh, inclusions, and
`IsKInjective.Qh_map_bijective` and `quasiIso_iff`), and the project's
`DerivedCategories.lean` and `KInjectiveResolutions.lean`. The abstract-derived-category
node has no lean record but is directly supplied by Mathlib's `DerivedCategory`, `Q`,
and `Qh`; no missing notion requires a new node or module. The project's derived-category
module's new torsion predicate is unrelated here; the recorded existing category notions
are the ones used, so an unused import of that module is not needed.

Edge cases: I and J may have nonzero terms arbitrarily far to the left even when K is
bounded below in cohomology. Neither has a strict boundedness binder, and no term is
required injective. Zero complexes, zero derived objects, empty schemes and any negative
or zero lower bound are covered. All degrees are integers, including 0. No indexing
family occurs, so an empty index set imposes no condition. There is no field, characteristic,
finiteness, properness or nonemptiness hypothesis. The single explicit universe u and
AddCommGrpCat.{u+1} are the chosen size convention of the recorded abelian-sheaf category;
u is arbitrary. Every variable and local abbreviation, including qY, is explicitly bound.

Independent searches (2026-10-11), using words different from the first report:

- LeanFinder via msearch: `derived base change comparison arbitrary K-injective resolution`.
  Eight hits, all classical right-derived cohomology comparisons such as
  `CategoryTheory.InjectiveResolution.rightDerived_app_eq`; none states this derived
  exchange comparison for arbitrary K-injective complexes.
- Loogle via msearch: `CochainComplex.IsKInjective`. Twelve hits include the existing
  predicate, homotopy invariance and the bounded-below injective criterion. These notions
  are reused, not redefined.
- LeanSearch via msearch: `derived base change on arbitrary K injective resolution comparison`.
  Service returned Internal Server Error; unavailable, with no mathematical verdict inferred.
- rg over Mathlib, all WeilConjectures and project lean/Sheaf for
  `base.change.*[Kk].injective`, `[Kk].injective.*base.change`, `derivedExchangeTermwise`,
  `σsrc`, `sigma.src`, `sigma_src`, and `termwise construction`, plus inspection of
  SixFunctors/BaseChange and dag/lean_names_upstream.json. No existing full statement found.
  The source `Etale.derivedBaseChangeMapPlus_fac_app` is exactly the original delivered
  signature, but it has no I, s, J or j and only takes a bounded-below homotopy object.
  It is not the node's arbitrary-resolution statement, so setting existing:true for it
  would also be H3. It remains a useful ingredient for stage 3, not this item's realization.

Mismatches repaired: H3 (a commutative rather than cartesian square; arbitrary coefficient
category rather than the node's abelian sheaves; K a bounded-below homotopy object rather
than a derived object; missing arbitrary I, s, J, j and comparisons; missing clause (a));
H4 (a verbatim duplicate of fac_app that did not state this node); H8 (no seven-step proof
in the docstring); H9 (added the conventional copyright header). The correct topic, module
path, declaration name and useful source import were retained. No definition, axiom or
auxiliary theorem was introduced; the sole theorem still has proof `sorry` for stage 3.
The node's lean.statement was replaced by the exact multiline signature in the file.

Validation: scompile.py compiled the repaired module on the server in 10.6 seconds, exit 0,
with no warnings. The node text, statement dependencies and proof remain unchanged.
