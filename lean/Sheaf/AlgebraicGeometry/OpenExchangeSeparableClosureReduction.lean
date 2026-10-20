/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Sheaf.AlgebraicGeometry.SeparableClosureConservative
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.SixFunctors.BaseChange.UniversalHomeomorphism
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Reduction of open-immersion exchange to a separable closure

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).

The product is `Y ×_S X`. Its pullback along `j : U → X` is used as the chosen
model of `Y ×_S U`; the exchange map is evaluated on the sheaf in degree zero.
Scalar extension uses the existing functor `Over.pullback` on all three schemes
and on the open immersion, and the ordinary sheaf inverse image on its coefficient.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private noncomputable def chosenSquare
    {T T' S S' : Scheme.{u}} {a : T' ⟶ T} {g' : T' ⟶ S'}
    {g : T ⟶ S} {b : S' ⟶ S} (sq : IsPullback a g' g b) :
    ChosenCartesianSquare a g' g b where
  w := sq.w
  isoPullback := sq.isoPullback
  hom_fst := sq.isoPullback_hom_fst
  hom_snd := sq.isoPullback_hom_snd

private theorem exchange_iso_iff_plus
    {T T' S S' : Scheme.{u}} {a : T' ⟶ T} {g' : T' ⟶ S'}
    {g : T ⟶ S} {b : S' ⟶ S} (sq : IsPullback a g' g b)
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app E.obj) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app E) := by
  rw [exactDerivedBaseChangeMap_agrees_plus (chosenSquare sq) E]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]
  constructor
  · intro h
    let := h
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  · intro h
    let := h
    infer_instance

private theorem exchange_congr
    {T T' S S' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S'}
    {a a' : T' ⟶ T} {b b' : S' ⟶ S} (ha : a = a') (hb : b = b')
    (sq : CommSq a g' g b) (sq' : CommSq a' g' g b')
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app E) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq').app E) := by
  subst a'
  subst b'
  rfl

private theorem field_exchange_of_models
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (T S : Over (Spec (.of K))) (g : T ⟶ S)
    [QuasiCompact g.left] [QuasiSeparated g.left]
    (T' S' : Over (Spec (.of L))) (g' : T' ⟶ S')
    (a : T'.left ⟶ T.left) (b : S'.left ⟶ S.left)
    (sqT : IsPullback a T'.hom T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (sqS : IsPullback b S'.hom S.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (sq : CommSq a g'.left g.left b)
    (E : DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app E) := by
  let A := AddCommGrpCat.{u + 1}
  let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let gL := (Over.pullback r).map g
  let eT := sqT.isoPullback
  let eS := sqS.isoPullback
  let sqe : CommSq eT.hom g'.left gL.left eS.hom := ⟨by
    apply pullback.hom_ext
    · simp only [Category.assoc, gL, Over.pullback_map_left, pullback.lift_fst]
      rw [← Category.assoc, sqT.isoPullback_hom_fst, sqS.isoPullback_hom_fst]
      exact sq.w
    · simp only [Category.assoc, gL, Over.pullback_map_left, pullback.lift_snd]
      rw [sqT.isoPullback_hom_snd, sqS.isoPullback_hom_snd]
      exact (Over.w g').symm⟩
  let sqc : CommSq (pullback.fst T.hom r) gL.left g.left (pullback.fst S.hom r) :=
    ⟨by simp [gL, Over.pullback_map_left]⟩
  have := isIso_derivedBaseChangeMapPlus_fieldExtension K L T S g E hE
  have := isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism A
    (IsPullback.of_horiz_isIso sqe)
  have hi : IsIso ((derivedBaseChangeMapPlus A (sqe.horiz_comp sqc)).app E) := by
    rw [derivedBaseChangeMapPlus_paste_horiz A sqc sqe (sqe.horiz_comp sqc)]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  exact (exchange_congr sqT.isoPullback_hom_fst sqS.isoPullback_hom_fst
    (sqe.horiz_comp sqc) sq E).mp hi

private theorem torsion_iso
    (K : Type u) [Field K] (T : Over (Spec (.of K)))
    {F G : Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hG : IsTorsionOfInvertibleOrder K T G) : IsTorsionOfInvertibleOrder K T F := by
  intro Ω _ _ t x
  let a := (Scheme.pointSmallEtale t).sheafFiber.mapIso e
  obtain ⟨n, hn, hx⟩ := hG Ω t (a.hom x)
  refine ⟨n, hn, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso a.hom).injective
  simpa only [map_nsmul, map_zero] using hx

private theorem torsion_pullback
    (K : Type u) [Field K] {T V : Over (Spec (.of K))} (p : V ⟶ T)
    (F : Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K T F) :
    IsTorsionOfInvertibleOrder K V ((upperStar AddCommGrpCat.{u + 1} p.left).obj F) := by
  intro Ω _ _ t x
  let a := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} p.left t).app F
  obtain ⟨n, hn, hx⟩ := hF Ω (t ≫ p.left) (a.hom x)
  refine ⟨n, hn, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso a.hom).injective
  simpa only [map_nsmul, map_zero] using hx

private theorem torsion_single
    (K : Type u) [Field K] (T : Over (Spec (.of K)))
    (F : Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K T F) :
    HasTorsionCohomologyOfInvertibleOrder K T
      ((DerivedCategory.singleFunctor _ 0).obj F) := by
  intro q
  by_cases hq : q = 0
  · subst q
    exact torsion_iso K T
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F) hF
  · have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 q h
      · exact DerivedCategory.isZero_of_isLE _ 0 q h
    intro Ω _ _ t x
    have hz' := Functor.map_isZero (Scheme.pointSmallEtale t).sheafFiber hz
    let := AddCommGrpCat.subsingleton_of_isZero hz'
    have hx : x = 0 := Subsingleton.elim _ _
    exact ⟨1, ⟨by decide, by simp⟩, by rw [hx, smul_zero]⟩

private theorem torsion_derived_pullback
    (K : Type u) [Field K] {T V : Over (Spec (.of K))} (p : V ⟶ T)
    (E : DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj) :
    HasTorsionCohomologyOfInvertibleOrder K V
      ((upperStar AddCommGrpCat.{u + 1} p.left).mapDerivedCategoryPlus.obj E).obj := by
  intro q
  exact torsion_iso K V
    (((upperStar AddCommGrpCat.{u + 1} p.left).mapDerivedCategoryHomologyFunctorIso q).app
      E.obj).symm (torsion_pullback K p _ (hE q))

private theorem plus_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] :
    F.mapDerivedCategoryPlus.IsEquivalence := by
  let e := F.asEquivalence
  let : e.functor.Additive := inferInstanceAs F.Additive
  let : e.inverse.Additive := e.inverse_additive
  let G := e.inverse
  let η := (Functor.mapDerivedCategoryPlusIdIso C).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso e.unitIso ≪≫
    Functor.mapDerivedCategoryPlusCompIso F G
  let ε := (Functor.mapDerivedCategoryPlusCompIso G F).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso e.counitIso ≪≫
    Functor.mapDerivedCategoryPlusIdIso D
  exact inferInstanceAs
    (CategoryTheory.Equivalence.mk F.mapDerivedCategoryPlus
      G.mapDerivedCategoryPlus η ε).functor.IsEquivalence

private theorem plus_conservative
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (T : Over (Spec (.of K))) (T' : Over (Spec (.of L))) (a : T'.left ⟶ T.left)
    (sq : IsPullback a T'.hom T.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {E F : DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (φ : E ⟶ F)
    (hφ : IsIso ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map φ)) :
    IsIso φ := by
  let A := AddCommGrpCat.{u + 1}
  let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let b := pullback.fst T.hom r
  let e := sq.isoPullback
  have hp : e.hom ≫ b = a := sq.isoPullback_hom_fst
  have hi : IsIso (((upperStar A b).mapDerivedCategoryPlus ⋙
      (upperStar A e.hom).mapDerivedCategoryPlus).map φ) :=
    (NatIso.isIso_map_iff (upperStarCompDerivedPlus A e.hom b a hp.symm) φ).mp hφ
  have hcan : IsIso ((upperStar A b).mapDerivedCategoryPlus.map φ) := by
    change IsIso ((upperStar A e.hom).mapDerivedCategoryPlus.map
      ((upperStar A b).mapDerivedCategoryPlus.map φ)) at hi
    have : (upperStar A e.hom).mapDerivedCategoryPlus.IsEquivalence := plus_equivalence _
    let := hi
    exact isIso_of_reflects_iso _ (upperStar A e.hom).mapDerivedCategoryPlus
  have hu : IsIso ((upperStar A b).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map φ)) := by
    have hm : IsIso (( (upperStar A b).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι).map φ) := by
      let := hcan
      change IsIso (DerivedCategory.Plus.ι.map
        ((upperStar A b).mapDerivedCategoryPlus.map φ))
      infer_instance
    exact (NatIso.isIso_map_iff
      (upperStar A b).mapDerivedCategoryPlusCompatibility φ).mp hm
  have ho := (separableClosure_baseChange_conservative K L T.left T.hom).2.2
    _ _ (DerivedCategory.Plus.ι.map φ) |>.mpr hu
  let := ho
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

private theorem exchange_cube
    {U X V Z UL XL VL ZL : Scheme.{u}}
    {j : U ⟶ X} {p : V ⟶ U} {h : V ⟶ Z} {q : Z ⟶ X}
    {jL : UL ⟶ XL} {pL : VL ⟶ UL} {hL : VL ⟶ ZL} {qL : ZL ⟶ XL}
    {rU : UL ⟶ U} {rX : XL ⟶ X} {rV : VL ⟶ V} {rZ : ZL ⟶ Z}
    (sq : CommSq p h j q) (sqL : CommSq pL hL jL qL)
    (sqj : CommSq rU jL j rX) (sqh : CommSq rV hL h rZ)
    (hp : pL ≫ rU = rV ≫ p) (hq : qL ≫ rX = rZ ≫ q)
    (E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (ha : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqj).app E))
    (hb : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqh).app
      ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryPlus.obj E)))
    (hnew : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqL).app
      ((upperStar AddCommGrpCat.{u + 1} rU).mapDerivedCategoryPlus.obj E))) :
    IsIso ((upperStar AddCommGrpCat.{u + 1} rZ).mapDerivedCategoryPlus.map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app E)) := by
  let A := AddCommGrpCat.{u + 1}
  let := ha
  let := hb
  let := hnew
  have hi := exchange_congr hp hq (sqL.horiz_comp sqj) (sqh.horiz_comp sq) E
  rw [derivedBaseChangeMapPlus_paste_horiz A sqj sqL,
    derivedBaseChangeMapPlus_paste_horiz A sq sqh] at hi
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hi
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at hi
  exact hi.mp (by infer_instance)

private theorem scalar_square {B B' : Scheme.{u}} (r : B' ⟶ B)
    {T S : Over B} (g : T ⟶ S) :
    IsPullback (pullback.fst T.hom r) ((Over.pullback r).map g).left g.left
      (pullback.fst S.hom r) := by
  have outer : IsPullback (((Over.pullback r).map g).left ≫ pullback.snd S.hom r)
      (pullback.fst T.hom r) r (g.left ≫ S.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback T.hom r).flip
  exact (outer.of_right (by simp [Over.pullback_map_left])
    (IsPullback.of_hasPullback S.hom r).flip).flip

private theorem product_projection_square
    {B B' : Scheme.{u}} (r : B' ⟶ B) (Y X : Over B) (Y' X' : Over B')
    (aY : Y'.left ⟶ Y.left) (aX : X'.left ⟶ X.left)
    (sqY : IsPullback aY Y'.hom Y.hom r)
    (sqX : IsPullback aX X'.hom X.hom r)
    (aZ : pullback Y'.hom X'.hom ⟶ pullback Y.hom X.hom)
    (hf : aZ ≫ pullback.fst Y.hom X.hom = pullback.fst Y'.hom X'.hom ≫ aY)
    (hs : aZ ≫ pullback.snd Y.hom X.hom = pullback.snd Y'.hom X'.hom ≫ aX) :
    IsPullback aZ (pullback.snd Y'.hom X'.hom) (pullback.snd Y.hom X.hom) aX := by
  have outer := (IsPullback.of_hasPullback Y'.hom X'.hom).paste_horiz sqY
  have outer' : IsPullback (pullback.snd Y'.hom X'.hom)
      (aZ ≫ pullback.fst Y.hom X.hom) (aX ≫ X.hom) Y.hom := by
    simpa only [hf, sqX.w] using outer.flip
  exact (outer'.of_bot hs.symm (IsPullback.of_hasPullback Y.hom X.hom).flip).flip

/-- The canonical open-product exchange map. Here `q` is the second projection of
`Y ×_S X`, and `p,h` are the two projections of its pullback along `j`.
Source: Weil blueprint, node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).
This is the recorded unbounded exchange, with the coefficient placed in degree zero. -/
noncomputable def openProductExchange {S : Scheme.{u}} {U X : Over S}
    (j : U ⟶ X) (Y : Over S)
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (D((pullback.snd Y.hom X.hom)^*[AddCommGrpCat.{u + 1}])).obj
        ((R((j.left)_*[AddCommGrpCat.{u + 1}])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ⟶
      (R((pullback.snd j.left (pullback.snd Y.hom X.hom))_*[AddCommGrpCat.{u + 1}])).obj
        ((D((pullback.fst j.left (pullback.snd Y.hom X.hom))^*[AddCommGrpCat.{u + 1}])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback j.left (pullback.snd Y.hom X.hom)).toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)

/-- Isomorphy of open-product exchange descends from a separable closure.
Source: Weil blueprint, node order 1769 (blueprint: lem-kun-0f1h-sep-reduction).

Proof, following the node's five steps:
1. Finite type over a field makes `U,X` Noetherian, quasi-compact and quasi-separated
   (lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated). The permanence statement
   lem-weil-pbc-qcqs-morphism-permanence makes `j` and its pullback `h` qcqs.
2. Place `F` in degree zero. Exact inverse image, from
   prop-weil-pbc-inverse-image-modules-exact, and lem-kun-stalk-as-pullback identify
   the stalks of `p⁻¹F` with those of `F`, preserving the elementwise torsion condition.
3. Apply lem-kun-0f1c-exchange to `j,F` and `h,p⁻¹F`. This supplies the canonical
   field-extension exchange isomorphisms `a` and `b`. Inverse-image composition
   (lem-weil-pbc-derived-inverse-image-composition) identifies the cube's pullbacks.
4. Lem-kun-unbounded-exchange-agrees identifies these maps with bounded-below
   exchange. Full faithful inclusion reflects isomorphisms. Pullback pasting and
   lem-weil-pbc-exchange-identity-pasting, applied to both factorizations of the outer
   rectangle, identify the extended original exchange with the new exchange:
   `Rh_L,*(C_U) ∘ b ∘ r_Z⁻¹(beta) ∘ C_X = beta_L ∘ q_L⁻¹(a)`.
   Here `C_U` and `C_X` are the inverse-image composition isomorphisms, and
   lem-weil-pbc-cartesian-square-pasting supplies the outer cartesian rectangles.
5. The assumed isomorphy of `beta_L` and the isomorphy of `a,b,C_U,C_X` make
   `r_Z⁻¹(beta)` invertible. Lem-kun-sep-closure-conservative then makes `beta`
   invertible on the original product. No uniform annihilator is used. -/
theorem isIso_openProductExchange_of_separableClosure
    (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L] [IsSepClosure K L]
    (U X Y : Over (Spec (.of K))) (j : U ⟶ X) [IsOpenImmersion j.left]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K U F)
    (hL : IsIso (openProductExchange
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map j)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj Y)
      ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst U.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F))) :
    IsIso (openProductExchange j Y F) := by
  classical
  let A := AddCommGrpCat.{u + 1}
  let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let XL := (Over.pullback r).obj X
  let YL := (Over.pullback r).obj Y
  let jL := (Over.pullback r).map j
  let rU := pullback.fst U.hom r
  let rX := pullback.fst X.hom r
  let rY := pullback.fst Y.hom r
  let q := pullback.snd Y.hom X.hom
  let p := pullback.fst j.left q
  let h := pullback.snd j.left q
  let Z : Over (Spec (.of K)) := Over.mk (q ≫ X.hom)
  let V : Over (Spec (.of K)) := Over.mk (h ≫ Z.hom)
  let qL := pullback.snd YL.hom XL.hom
  let pL := pullback.fst jL.left qL
  let hL' := pullback.snd jL.left qL
  let ZL : Over (Spec (.of L)) := Over.mk (qL ≫ XL.hom)
  let VL : Over (Spec (.of L)) := Over.mk (hL' ≫ ZL.hom)
  let pOver : V ⟶ U := Over.homMk p (by
    change p ≫ U.hom = h ≫ q ≫ X.hom
    rw [← Over.w j, ← Category.assoc, pullback.condition, Category.assoc])
  let hOver : V ⟶ Z := Over.homMk h rfl
  let hOverL : VL ⟶ ZL := Over.homMk hL' rfl
  let sq := IsPullback.of_hasPullback j.left q
  let sqL := IsPullback.of_hasPullback jL.left qL
  let sqj : CommSq rU jL.left j.left rX := ⟨by
    simp [rU, rX, jL, Over.pullback_map_left]⟩
  let rZ : ZL.left ⟶ Z.left := pullback.lift
    (pullback.fst YL.hom XL.hom ≫ rY) (qL ≫ rX) (by
      change (pullback.fst YL.hom XL.hom ≫ pullback.fst Y.hom r) ≫ Y.hom =
        (pullback.snd YL.hom XL.hom ≫ pullback.fst X.hom r) ≫ X.hom
      simp only [Category.assoc, pullback.condition]
      change pullback.fst YL.hom XL.hom ≫ YL.hom ≫ r =
        pullback.snd YL.hom XL.hom ≫ XL.hom ≫ r
      rw [← Category.assoc, pullback.condition, Category.assoc])
  have sqZ : IsPullback rZ ZL.hom Z.hom r := by
    exact (product_projection_square r Y X YL XL rY rX
      (IsPullback.of_hasPullback Y.hom r) (IsPullback.of_hasPullback X.hom r)
      rZ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).paste_vert
        (IsPullback.of_hasPullback X.hom r)
  have hq : qL ≫ rX = rZ ≫ q := (pullback.lift_snd _ _ _).symm
  let rV : VL.left ⟶ V.left := pullback.lift (pL ≫ rU) (hL' ≫ rZ) (by
    rw [Category.assoc, sqj.w, ← Category.assoc, sqL.w, Category.assoc, hq,
      ← Category.assoc])
  have hp : pL ≫ rU = rV ≫ p := (pullback.lift_fst _ _ _).symm
  have sqh : IsPullback rV hL' h rZ := by
    have outer : IsPullback (rV ≫ p) hL' j.left (rZ ≫ q) := by
      rw [← hp, ← hq]
      exact sqL.paste_horiz (scalar_square r j)
    exact outer.of_right (by simp only [rV, h, pullback.lift_snd]) sq
  have sqV : IsPullback rV VL.hom V.hom r := sqh.paste_vert sqZ
  let := LocallyOfFiniteType.isLocallyNoetherian U.hom
  let := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : QuasiCompact j.left := by
    have : QuasiCompact (j.left ≫ X.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp j.left X.hom
  have : QuasiSeparated j.left := inferInstance
  have hqc : QuasiCompact h := MorphismProperty.of_isPullback
    (P := @QuasiCompact) sq inferInstance
  have hqs : QuasiSeparated h := MorphismProperty.of_isPullback
    (P := @QuasiSeparated) sq inferInstance
  let : QuasiCompact hOver.left := hqc
  let : QuasiSeparated hOver.left := hqs
  let E := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have hE : HasTorsionCohomologyOfInvertibleOrder K U E.obj := torsion_single K U F hF
  have ha := isIso_derivedBaseChangeMapPlus_fieldExtension K L U X j E hE
  have hb := field_exchange_of_models K L V Z hOver VL ZL hOverL rV rZ sqV sqZ
    sqh.toCommSq ((upperStar A p).mapDerivedCategoryPlus.obj E)
    (torsion_derived_pullback K pOver E hE)
  have hnew : IsIso ((derivedBaseChangeMapPlus A sqL.toCommSq).app
      ((upperStar A rU).mapDerivedCategoryPlus.obj E)) := by
    have hsingle := (exchange_iso_iff_plus sqL
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar A rU).obj F))).mp hL
    exact (NatTrans.isIso_app_iff_of_iso _
      (((upperStar A rU).mapDerivedCategoryPlusSingleFunctor 0).app F)).mpr hsingle
  have hbase := exchange_cube sq.toCommSq sqL.toCommSq sqj sqh.toCommSq hp hq E
    ha hb hnew
  have hβ := plus_conservative K L Z ZL rZ sqZ
    ((derivedBaseChangeMapPlus A sq.toCommSq).app E) hbase
  exact (exchange_iso_iff_plus sq E).mpr hβ

end AlgebraicGeometry.Etale
