/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
import WeilConjectures.DeligneLaumon.CondensedModule.CondensedModuleTransportComposition

/-! # Composition of condensed module semilinear transports

Source: step 10 of lem-a1-condensed-proper-frobenius-germs, contracting the ordered
Weil iterate with the canonical pullback compositors.
(blueprint: lem-a1-condensed-proper-germ-transport-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedModule

private theorem chain_zero {C : Type*} [Category C] (P : ℕ → C) (M : C)
    (i : P 0 ≅ M) (step : ∀ n, P (n + 1) ≅ P n) :
    isoChain P M i step 0 = i := rfl

/-- The unfolding equation retains the chain as an isomorphism before taking components.
Source: the defining ordered Weil iterate in the parent node.
(blueprint: lem-a1-condensed-proper-germ-transport-composition). -/
theorem properGerm_iterate_eq (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}} (g : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M) (n : ℕ) :
    iterate l g M θ n =
      isoChain (fun m ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localPositivePower g m)).obj M) M
        (evaluateInitial
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower g 0))
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
          (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
            (show localPositivePower g 0 = g from Eq.refl g)) M θ)
        (iterateStep l g M θ) n := by
  unfold iterate
  rfl

private theorem app_refl {C B : Type*} [Category C] [Category B]
    (F : C ⥤ B) (M : C) : (Iso.refl F).app M = Iso.refl (F.obj M) := rfl

private theorem pointComparison_congr
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a b : T ⟶ T) (e : a = b)
    (s t : Spec (.of D.k) ⟶ Spec (.of D.k)) (es : s = t)
    (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T)
    (h : z ≫ a = s ≫ z') (h' : z ≫ b = t ≫ z') :
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) s)
      a h).app M ≪≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
          ((CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) e).app M ≪≫ θ) =
      (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
        (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) t)
        b h').app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso θ := by
  subst a
  subst s
  rw [CondensedRing.upperStarCongr_self, app_refl, Iso.refl_trans]

/-- The initial transport is the given one-step Weil map with its point comparison.
Source: the initial ordered iterate, retaining its equality comparison until composition.
(blueprint: lem-a1-condensed-proper-germ-transport-composition). -/
theorem properGerm_transport_zero (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ a = (frobeniusPointIso D).hom ≫ z') :
    transport l D a M θ z z' 0 h =
      (CondensedRing.pointSections l D.k).mapIso
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (frobeniusPointIso D).hom) a h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso θ) := by
  unfold transport
  rw [properGerm_iterate_eq, chain_zero]
  unfold evaluateInitial
  exact congrArg (CondensedRing.pointSections l D.k).mapIso
    (pointComparison_congr l D (localPositivePower a 0) a rfl
      (localPositivePower (frobeniusPointIso D).hom 0) (frobeniusPointIso D).hom rfl
      M θ z z' h h)

/-- The initial transport equation directly as a map of the native point sections.
Source: apply Iso.hom to properGerm_transport_zero and expand the mapped composite.
(blueprint: lem-a1-condensed-proper-germ-transport-composition). -/
theorem properGerm_transport_zero_hom (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (h : z ≫ a = (frobeniusPointIso D).hom ≫ z') :
    (transport l D a M θ z z' 0 h).hom =
      (CondensedRing.pointSections l D.k).map
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (frobeniusPointIso D).hom) a h).hom.app M ≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map θ.hom) := by
  simpa only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom] using
    congrArg Iso.hom (properGerm_transport_zero l D a M θ z z' h)

/-- A final one-step transport followed by an n+1-step transport is the contracted
n+2-step transport, with precisely the prescribed point trivializations.

Source: latest blueprint lem-a1-finite-boundary-weights.proof.md, local stability;
step 10 of lem-a1-condensed-proper-frobenius-germs.
(blueprint: lem-a1-condensed-proper-germ-transport-composition).

Proof: expand transport as the point trivialization, inverse point compositor,
comparison of the semilinear square, source compositor, and pulled-back Weil iterate.
Move the one-step Weil map through the previous point comparison by naturality.
The two source compositors then contract to the compositor for a^(n+2), by the
associativity law for upperStarComp. At the point, the two trivializations contract
to the trivialization for h^(n+2): each is obtained by cancelling the same fully
faithful pullback from the condensed point, and their whiskered comparisons are the
coherent upperStarFromPointModComp maps. Hence the two candidates agree after this
fully faithful functor and agree themselves. Writing alpha_n for pointComparison, the compositor
calculation is exactly
alpha_0 at M followed by alpha_n at g* M equals alpha_(n+1) at M followed by z* of
upperStarComp(g_n,g). Naturality of alpha_n at theta moves z'* theta to its right
as z*(g_n* theta). The remaining factors are therefore z* of the source compositor,
g_n* theta and theta_n: exactly iterateStep followed by iterate, the defining
recursion for iterate at n+1.
Apply the pointSections functor, preserving the composite. Equality proofs hn, h1,
and ht introduce no choices by proof irrelevance. This includes zero modules.
-/
theorem properGerm_transport_comp
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' z'' : Spec (.of D.k) ⟶ T) (n : ℕ)
    (hn : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z')
    (h1 : z' ≫ a = (frobeniusPointIso D).hom ≫ z'')
    (ht : z ≫ localPositivePower a (n + 1) =
      localPositivePower (frobeniusPointIso D).hom (n + 1) ≫ z'') :
    (transport l D a M θ z' z'' 0 h1).hom ≫
        (transport l D a M θ z z' n hn).hom =
      (transport l D a M θ z z'' (n + 1) ht).hom := by
  simpa only [Nat.add_zero, Iso.trans_hom] using
    congrArg Iso.hom (transport_comp D l a M θ z z' z'' n 0 hn h1 ht)

end WeilConjectures.CondensedModule
