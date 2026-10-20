/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NV and C3
-/
module

public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

import all WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import Sheaf.CategoryTheory.ExactFunctorHalfPlane
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import Sheaf.AlgebraicGeometry.TruncationExchangeAbutment
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative

/-!
# Finite-range comparison

Source: literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/
sbc-lem-finite-range-comparison.md, statement and proof, order 1436
(blueprint: sbc-lem-finite-range-comparison).

The existential exact couples have exactly the recorded truncation data. The limiting
comparison is specified by its restriction to limiting cycles and its quotient square,
so it is the map induced by exchange, rather than an unrelated isomorphism.
-/

@[expose] public section

set_option linter.privateModule false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TruncationExchange
open CategoryTheory.BigradedExactCouple


universe v w

namespace CategoryTheory.BigradedExactCouple

variable {C : Type v} [Category.{w} C] [Abelian C]

private theorem page_kernel_isIso
    (X Y : BigradedExactCouple C 0)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (r : ℕ) (he : ∀ p q, IsIso (e r p q)) (p q : ℤ)
    (k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q))
    (hk : k ≫ kernel.ι ((Y.pageCouple r).d p q) =
      kernel.ι ((X.pageCouple r).d p q) ≫ e r p q) : IsIso k := by
  have : ∀ p q, IsIso (e r p q) := he
  have hk' : k = kernel.map _ _ (e r p q)
      (e r (p + 2 + r) (q - 1 - r)) (hd r p q).symm := by
    apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
    simpa only [kernel.lift_ι] using hk
  rw [hk']
  infer_instance

private theorem page_maps_isIso
    (X Y : BigradedExactCouple C 0)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (hnext : ∀ r p q,
      ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          kernel.ι ((X.pageCouple r).d p q) ≫ e r p q ∧
        (X.pageCouple r).derivedEProjection p q ≫ e (r + 1) p q =
          k ≫ (Y.pageCouple r).derivedEProjection p q)
    (hzero : ∀ p q, IsIso (e 0 p q)) : ∀ r p q, IsIso (e r p q) := by
  intro r
  induction r with
  | zero => exact hzero
  | succ r ih =>
    intro p q
    obtain ⟨k, hk, hkn⟩ := hnext r p q
    have : ∀ p q, IsIso (e r p q) := ih
    have : IsIso k := page_kernel_isIso X Y e hd r ih p q k hk
    let dx := kernel.lift ((X.pageCouple r).d p q)
      ((X.pageCouple r).dInto p q) ((X.pageCouple r).dInto_comp_d p q)
    let dy := kernel.lift ((Y.pageCouple r).d p q)
      ((Y.pageCouple r).dInto p q) ((Y.pageCouple r).dInto_comp_d p q)
    have hin : (X.pageCouple r).dInto p q ≫ e r p q =
        e r (p - r - 2) (q + r + 1) ≫ (Y.pageCouple r).dInto p q := by
      dsimp only [dInto]
      have ht := transport_square (𝟭 C) (e r)
        (show p - (r : ℤ) - 2 + 2 + r = p by omega)
        (show q + (r : ℤ) + 1 - 1 - r = q by omega)
      simp only [Functor.id_map] at ht
      rw [Category.assoc, ht,
        ← Category.assoc, ← hd, Category.assoc]
    have hb : dx ≫ k = e r (p - r - 2) (q + r + 1) ≫ dy := by
      apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
      simp only [Category.assoc, hk, dx, dy, kernel.lift_ι, kernel.lift_ι_assoc, hin]
    have heq : e (r + 1) p q =
        cokernel.map dx dy (e r (p - r - 2) (q + r + 1)) k hb := by
      apply (cancel_epi (cokernel.π dx)).mp
      simpa only [cokernel.π_desc, derivedEProjection, dx, dy] using hkn
    rw [heq]
    infer_instance


private theorem limit_transport (X Y : BigradedExactCouple C 0)
    (t : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (hfinite : ∀ r p q,
      (Y.cycleBoundaryTower.Z r p q).Factors
        ((X.cycleBoundaryTower.Z r p q).arrow ≫ t p q) ∧
      (Y.cycleBoundaryTower.B r p q).Factors
        ((X.cycleBoundaryTower.B r p q).arrow ≫ t p q))
    (LX : LimitSubobjects X) (LY : LimitSubobjects Y) (p q : ℤ) :
    (LY.Z p q).Factors ((LX.Z p q).arrow ≫ t p q) ∧
      (LY.B p q).Factors ((LX.B p q).arrow ≫ t p q) := by
  constructor
  · apply (factors_iff_image_le _ _).mpr
    apply (LY.Z_glb p q).2
    rintro _ ⟨r, rfl⟩
    apply (factors_iff_image_le _ _).mp
    have hz := (LX.Z_glb p q).1 (Set.mem_range_self r)
    have h := Subobject.factors_of_factors_right (Subobject.ofLE _ _ hz)
      (hfinite r p q).1
    simpa only [Subobject.ofLE_arrow_assoc] using h
  · apply (pullback_factors_iff _ _ _).mp
    apply Subobject.factors_of_le _ ((LX.B_lub p q).2 ?_)
      (Subobject.factors_self _)
    rintro _ ⟨r, rfl⟩
    apply Subobject.le_of_factors
    apply pullback_factors
    exact Subobject.factors_of_le _ ((LY.B_lub p q).1 (Set.mem_range_self r))
      (hfinite r p q).2

omit [Abelian C] in
private theorem restriction_iso {A B : C} (t : A ⟶ B) [IsIso t]
    (U : Subobject A) (V : Subobject B)
    (z : (U : C) ⟶ (V : C)) (hz : z ≫ V.arrow = U.arrow ≫ t)
    (hi : U.Factors (V.arrow ≫ inv t)) : IsIso z := by
  let zi := U.factorThru _ hi
  have hzi : zi ≫ U.arrow = V.arrow ≫ inv t := Subobject.factorThru_arrow _ _ _
  refine ⟨⟨zi, ?_, ?_⟩⟩
  · apply (cancel_mono U.arrow).mp
    rw [Category.assoc, hzi, ← Category.assoc, hz]
    simp
  · apply (cancel_mono V.arrow).mp
    rw [Category.assoc, hz, ← Category.assoc, hzi]
    simp

private theorem limit_map_isIso
    (X Y : BigradedExactCouple C 0)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (hnext : ∀ r p q,
      ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          kernel.ι ((X.pageCouple r).d p q) ≫ e r p q ∧
        (X.pageCouple r).derivedEProjection p q ≫ e (r + 1) p q =
          k ≫ (Y.pageCouple r).derivedEProjection p q)
    (hzero : ∀ p q, IsIso (e 0 p q))
    (LX : LimitSubobjects X) (LY : LimitSubobjects Y) (p q : ℤ)
    (z : (LX.Z p q : C) ⟶ (LY.Z p q : C))
    (tInf : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q)
    (hz : z ≫ (LY.Z p q).arrow = (LX.Z p q).arrow ≫ e 0 p q)
    (ht : cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle X LX p q)) ≫ tInf =
      z ≫ cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Y LY p q))) :
    IsIso tInf := by
  classical
  have he : ∀ r p q, IsIso (e r p q) := page_maps_isIso X Y e hd hnext hzero
  let ei := fun r p q ↦ inv (e r p q)
  have hdi : ∀ r p q, ei r p q ≫ (X.pageCouple r).d p q =
      (Y.pageCouple r).d p q ≫ ei r (p + 2 + r) (q - 1 - r) := by
    intro r p q
    dsimp [ei]
    apply (cancel_epi (e r p q)).mp
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, hd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hni : ∀ r p q,
      ∃ k : kernel ((Y.pageCouple r).d p q) ⟶ kernel ((X.pageCouple r).d p q),
        k ≫ kernel.ι ((X.pageCouple r).d p q) =
          kernel.ι ((Y.pageCouple r).d p q) ≫ ei r p q ∧
        (Y.pageCouple r).derivedEProjection p q ≫ ei (r + 1) p q =
          k ≫ (X.pageCouple r).derivedEProjection p q := by
    intro r p q
    obtain ⟨k, hk, hkn⟩ := hnext r p q
    have : IsIso k := page_kernel_isIso X Y e hd r (he r) p q k hk
    refine ⟨inv k, ?_, ?_⟩
    · apply (cancel_mono (e r p q)).mp
      dsimp [ei]
      rw [Category.assoc, ← hk, IsIso.inv_hom_id_assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · apply (cancel_mono (e (r + 1) p q)).mp
      dsimp [ei]
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.assoc, hkn, IsIso.inv_hom_id_assoc]
  have hf := exactCoupleFiniteTransport X Y (e 0) e (fun _ _ ↦ rfl) hd hnext
  have hi := exactCoupleFiniteTransport Y X (ei 0) ei (fun _ _ ↦ rfl) hdi hni
  have hlf := limit_transport X Y (e 0) hf LX LY p q
  have hli := limit_transport Y X (ei 0) hi LY LX p q
  have : IsIso z := restriction_iso (e 0 p q) (LX.Z p q) (LY.Z p q) z hz hli.1
  let b := (LY.B p q).factorThru _ hlf.2
  have hb : b ≫ (LY.B p q).arrow = (LX.B p q).arrow ≫ e 0 p q :=
    Subobject.factorThru_arrow _ _ _
  have : IsIso b := restriction_iso (e 0 p q) (LX.B p q) (LY.B p q) b hb hli.2
  let ix := Subobject.ofLE (LX.B p q) (LX.Z p q) (limitBoundary_le_cycle X LX p q)
  let iy := Subobject.ofLE (LY.B p q) (LY.Z p q) (limitBoundary_le_cycle Y LY p q)
  have hzb : ix ≫ z = b ≫ iy := by
    apply (cancel_mono (LY.Z p q).arrow).mp
    simp only [Category.assoc, hz, ix, iy, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc, hb]
  have heq : tInf = cokernel.map ix iy b z hzb := by
    apply (cancel_epi (cokernel.π ix)).mp
    simpa only [cokernel.π_desc] using ht
  rw [heq]
  infer_instance


omit [Abelian C] in
private theorem family_conj
    {F G F' G' : ℤ → ℤ → C} (hF : F = F') (hG : G = G')
    (m : ∀ p q, F p q ⟶ G p q) (m' : ∀ p q, F' p q ⟶ G' p q)
    (hm : HEq m m') (p q : ℤ) :
    m p q = eqToHom (congrFun (congrFun hF p) q) ≫ m' p q ≫
      eqToHom (congrFun (congrFun hG p) q).symm := by
  subst F'
  subst G'
  cases hm
  simp


private theorem finite_image {A B : C} (F : DecreasingFiltration A)
    (hF : F.IsFinite) (e : A ≅ B) : (F.image e.hom).IsFinite := by
  obtain ⟨n, m, hn, hm⟩ := hF
  refine ⟨n, m, ?_, ?_⟩
  · change imageSubobject ((F.F n).arrow ≫ e.hom) = ⊤
    rw [imageSubobject_mono, ← Subobject.map_mk, Subobject.mk_arrow, hn]
    exact (Subobject.mapIsoToOrderIso e).map_top
  · change imageSubobject ((F.F m).arrow ≫ e.hom) = ⊥
    rw [imageSubobject_mono, ← Subobject.map_mk, Subobject.mk_arrow, hm]
    exact (Subobject.mapIsoToOrderIso e).map_bot

private theorem filtered_iso_of_graded
    {A B : C} (U : DecreasingFiltration A) (V : DecreasingFiltration B)
    (t : A ⟶ B) (lift : ∀ p : ℤ, (U.step p : C) ⟶ (V.step p : C))
    (hlift : ∀ p : ℤ, lift p ≫ (V.step p).arrow = (U.step p).arrow ≫ t)
    (gr : ∀ p : ℤ, U.gradedPiece p ⟶ V.gradedPiece p)
    (hgr : ∀ p : ℤ, cokernel.π (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) ≫
      gr p = lift p ≫
        cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1))))
    (hU : U.IsFinite) (hV : V.IsFinite) (hi : ∀ p : ℤ, IsIso (gr p)) : IsIso t := by
  let f : FilteredObject.Hom
      (⟨A, U⟩ : FilteredObject C) (⟨B, V⟩ : FilteredObject C) :=
    ⟨t, fun p ↦ ⟨lift p, hlift p⟩⟩
  apply (FilteredObject.finite_filtration_induction_steps _ _ f hU hV ?_).1
  intro p
  have hr : FilteredObject.restrictionSteps f p = lift p := by
    apply (cancel_mono (V.step p).arrow).mp
    exact (Classical.choose_spec (f.preserves p)).trans (hlift p).symm
  have hg : FilteredObject.gradedMapSteps f p = gr p := by
    apply (cancel_epi (cokernel.π
      (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))))).mp
    have hh : cokernel.π
        (Subobject.ofLE _ _ (U.antitone_step (by omega : p ≤ p + 1))) ≫
          FilteredObject.gradedMapSteps f p = FilteredObject.restrictionSteps f p ≫
            cokernel.π (Subobject.ofLE _ _ (V.antitone_step (by omega : p ≤ p + 1))) :=
      Classical.choose_spec (FilteredObject.exists_gradedMap_steps _ _ f p)
    rw [hr] at hh
    exact hh.trans (hgr p).symm
  rw [hg]
  exact hi p

end CategoryTheory.BigradedExactCouple

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedBaseChangeMapPlus

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- If exchange is an isomorphism on every E₂ term and K has cohomology in [a,b],
then its induced infinite-page maps, all its cohomology maps, and exchange itself
are isomorphisms.

Proof:
1. Apply lem-weil-pbc-truncation-couple-morphism to form the two exact couples
   and their exchange morphism. Its page identifications identify tE with the
   degree-p exchange on H^q(K). Apply lem-sp-couple-morphism for the induced maps.
2. The lower bound a permits lemma-weil-pbc-exact-couple-abutment: its half-plane
   bounds give limiting pages, finite filtrations, and the canonical identifications
   of the abutments with H^n(Phi K) and H^n(Psi K). Only q in [a,b] contributes.
3. The local exact-couple page-induction helpers show that the E₂ isomorphisms induce
   isomorphisms on all pages and on limiting cycles modulo limiting boundaries. These are
   the z/tInf squares below.
4. Under the canonical abutment identifications, the graded maps are those same
   infinite-page maps. Apply lem-sp-finite-filtration-induction to each finite
   filtered abutment to obtain the isomorphism on H^n(exchange), for every n.
5. Geometric stalks preserve these isomorphisms; lem-weil-pbc-derived-stalk-conservative
   implies exchange is an isomorphism in D+.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1436, proof
(blueprint: sbc-lem-finite-range-comparison). - /
theorem finite_range_exchange_comparison
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a b : ℤ) (_hab : a ≤ b)
    (_hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K))
    (_h₂ : ∀ p q : ℤ,
      IsIso (tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q)) :
    (∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
      P.D = D (truncationPhi f g) K ∧
      Q.D = D (truncationPsi g' f') K ∧
      ∃ hPE : P.E = E (truncationPhi f g) K,
      ∃ hQE : Q.E = E (truncationPsi g' f') K,
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K) ∧
      ∃ L : LimitSubobjects P, ∃ M : LimitSubobjects Q,
      ∃ z : ∀ p q : ℤ,
        (L.Z p q : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) ⟶
          (M.Z p q : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ∃ tInf : ∀ p q : ℤ, P.pageInfinity L p q ⟶ Q.pageInfinity M p q,
        (∀ p q : ℤ,
          z p q ≫ (M.Z p q).arrow = (L.Z p q).arrow ≫
            eqToHom (congrFun (congrFun hPE p) q) ≫
            tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
            eqToHom (congrFun (congrFun hQE p) q).symm) ∧
        (∀ p q : ℤ,
          cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle P L p q)) ≫ tInf p q =
            z p q ≫ cokernel.π (Subobject.ofLE _ _ (limitBoundary_le_cycle Q M p q))) ∧
        (∀ p q : ℤ, IsIso (tInf p q))) ∧
    (∀ n : ℤ, IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K))) ∧
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) := by
  classical
  obtain ⟨⟨P, Q, hPD, hQD, hPE, hQE, hPa, hQa, hPf, hQf, hPg, hQg⟩,
    ha, hg, hf, _⟩ := truncation_exchange_couple_morphism sq K
  let dP (p q : ℤ) := eqToHom (congrFun (congrFun hPD p) q)
  let dQ (p q : ℤ) := eqToHom (congrFun (congrFun hQD p) q)
  let eP (p q : ℤ) := eqToHom (congrFun (congrFun hPE p) q)
  let eQ (p q : ℤ) := eqToHom (congrFun (congrFun hQE p) q)
  let td (p q : ℤ) := dP p q ≫
    tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫ inv (dQ p q)
  let te (p q : ℤ) := eP p q ≫
    tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫ inv (eQ p q)
  have hPa' (p q : ℤ) : P.alpha p q = dP p q ≫
      alpha (truncationPhi f g) K p q ≫ inv (dP (p - 1) (q + 1)) := by
    simpa only [dP, inv_eqToHom] using family_conj hPD
      (congrArg (fun d : ℤ → ℤ → _ ↦ fun p q ↦ d (p - 1) (q + 1)) hPD)
      P.alpha (alpha (truncationPhi f g) K) hPa p q
  have hQa' (p q : ℤ) : Q.alpha p q = dQ p q ≫
      alpha (truncationPsi g' f') K p q ≫ inv (dQ (p - 1) (q + 1)) := by
    simpa only [dQ, inv_eqToHom] using family_conj hQD
      (congrArg (fun d : ℤ → ℤ → _ ↦ fun p q ↦ d (p - 1) (q + 1)) hQD)
      Q.alpha (alpha (truncationPsi g' f') K) hQa p q
  have hPf' (p q : ℤ) : P.f p q = eP p q ≫
      CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
        inv (dP (p + 2) (q - 1)) := by
    simpa only [eP, dP, inv_eqToHom] using family_conj hPE
      (congrArg (fun d : ℤ → ℤ → _ ↦ fun p q ↦ d (p + 2) (q - 1)) hPD)
      P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) hPf p q
  have hQf' (p q : ℤ) : Q.f p q = eQ p q ≫
      CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q ≫
        inv (dQ (p + 2) (q - 1)) := by
    simpa only [eQ, dQ, inv_eqToHom] using family_conj hQE
      (congrArg (fun d : ℤ → ℤ → _ ↦ fun p q ↦ d (p + 2) (q - 1)) hQD)
      Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) hQf p q
  have hPg' (p q : ℤ) : P.initialG p q = dP p q ≫
      CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫ inv (eP p q) := by
    have hE : (fun p q ↦ P.E (p + (0 : ℕ)) (q - (0 : ℕ))) =
        E (truncationPhi f g) K := by simpa using hPE
    rw [initialG, family_conj hPD hE P.g
      (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) hPg p q]
    simp [dP, eP]
  have hQg' (p q : ℤ) : Q.initialG p q = dQ p q ≫
      CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q ≫ inv (eQ p q) := by
    have hE : (fun p q ↦ Q.E (p + (0 : ℕ)) (q - (0 : ℕ))) =
        E (truncationPsi g' f') K := by simpa using hQE
    rw [initialG, family_conj hQD hE Q.g
      (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K) hQg p q]
    simp [dQ, eQ]
  have hat (p q : ℤ) : P.alpha p q ≫ td (p - 1) (q + 1) =
      td p q ≫ Q.alpha p q := by
    simp only [hPa', hQa', td, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc (alpha _ _ _ _), ha]
    simp only [Category.assoc]
  have hft (p q : ℤ) : P.f p q ≫ td (p + 2) (q - 1) = te p q ≫ Q.f p q := by
    simp only [hPf', hQf', td, te, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc (CategoryTheory.TruncationExchange.f _ _ _ _), hf]
    simp only [Category.assoc]
  have hgt (p q : ℤ) : P.initialG p q ≫ te p q = td p q ≫ Q.initialG p q := by
    simp only [hPg', hQg', td, te, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc (CategoryTheory.TruncationExchange.g _ _ _ _), hg]
    simp only [Category.assoc]
  obtain ⟨pages, hp0, hpd, hpn, hconv⟩ := coupleMorphism P Q td te hat hft hgt
  have hpiso (p q : ℤ) : IsIso (pages 0 p q) := by
    rw [hp0]
    have := _h₂ p q
    dsimp [te]
    infer_instance
  have hlow (q : ℤ) (hq : q < a) := _hK q (Or.inl hq)
  have habut (n : ℤ) := truncation_exchange_exact_couple_abutment sq K a n hlow P Q
    hPD hPE hPa hPf hPg hQD hQE hQa hQf hQg
  obtain ⟨hDP, hEP, hDQ, hEQ, _⟩ := habut 0
  obtain ⟨L, M, A, B, hA, hB, hA0, hB0, ff, hff, hffι,
    z, ti, gr, e, e', hz, hti, hgr, he, he', hegr⟩ :=
      hconv a a hDP hEP hDQ hEQ
  have htiIso (p q : ℤ) : IsIso (ti p q) := by
    apply limit_map_isIso P Q pages (fun r p q ↦ (hpd r p q).symm)
      hpn hpiso L M p q (z p q) (ti p q)
    · rw [hp0]
      exact hz p q
    · exact hti p q
  have hcoh : ∀ n : ℤ, IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ n).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)) := by
    intro n
    -- Keep the dependent abutment data in short elimination steps. A single long
    -- pattern makes elaboration repeatedly process the full remaining telescope.
    obtain ⟨_, _, _, _, LN, MN, AN, BN, hAN, hBN, hrest⟩ := habut n
    obtain ⟨_, _, _, _, hfinA, hfinB, _, _, i, j, _, _, U, V, hU, hV, hrest⟩ := hrest
    obtain ⟨_, _, _, t, _, _, lift, hlift, grN, hgrN, zN, tiN, hzN, htiN,
      eN, eN', _, _, _, _, hcomp⟩ := hrest
    have hiN (p : ℤ) : IsIso (tiN p) := by
      apply limit_map_isIso P Q pages (fun r p q ↦ (hpd r p q).symm)
        hpn hpiso LN MN p (n - p) (zN p) (tiN p)
      · rw [hp0]
        have hh := (conj_eqToHom_iff_heq _ _ rfl
          (congrFun (congrFun hQE p) (n - p))).2 (hzN p)
        simpa only [eqToHom_refl, Category.id_comp, te, eP, eQ,
          inv_eqToHom, Category.assoc] using hh
      · exact htiN p
    have hgrIso (p : ℤ) : IsIso (grN p) := by
      have := hiN p
      have hh : grN p = (eN p).inv ≫ tiN p ≫ (eN' p).hom := by
        rw [← hcomp p, Iso.inv_hom_id_assoc]
      rw [hh]
      infer_instance
    apply filtered_iso_of_graded U V _ lift hlift grN hgrN
    · rw [hU]
      exact finite_image _ (hfinA n).1 i
    · rw [hV]
      exact finite_image _ (hfinB n).1 j
    · exact hgrIso
  refine ⟨?_, hcoh, ?_⟩
  · refine ⟨P, Q, hPD, hQD, hPE, hQE, hPa, hQa, hPf, hQf, hPg, hQg,
      L, M, z, ti, ?_, hti, htiIso⟩
    intro p q
    simpa only [te, eP, eQ, inv_eqToHom, Category.assoc] using hz p q
  · apply (Scheme.isIso_iff_isIso_geometricStalk_homologyMap _).2
    intro Ω _ _ t i
    have := hcoh i
    infer_instance
-/

end AlgebraicGeometry.Etale
