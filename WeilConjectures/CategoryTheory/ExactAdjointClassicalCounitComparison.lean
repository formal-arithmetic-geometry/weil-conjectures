/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Lower bounds and the classical comparison of counits

Source: blueprint main-20261015, sk-prop-a1, first localization triangle;
BBD, 1.3.4, p. 30; Stacks Project, Tag 0037
(blueprint: lem-pur-exact-adjoint-classical-counit-comparison).

The comparison is only supplied on `DerivedCategory.Plus`. The conclusions give natural
isomorphisms with prescribed components, and the natural transported counit with its two
component formulas. Thus the existentially bound transformations are fully specified.
-/

@[expose] public section

set_option autoImplicit false

universe uAZ uAX uBZ uBX vAZ vAX vBZ vBX wAZ wAX wBZ wBX

open CategoryTheory

namespace DerivedCategory

-- Retain the stronger hypotheses of the public interface.
set_option linter.unusedVariables false in
/-- An exact derived left adjoint has lower-bound preserving right adjoints, and the
classical-unit identification respects the specified transported counit.

Source: blueprint main-20261015, sk-prop-a1, first localization triangle;
BBD, 1.3.4, p. 30; Stacks Project, Tag 0037
(blueprint: lem-pur-exact-adjoint-classical-counit-comparison).

Proof plan:
1. If `N` is at least `a` and `A` is at most `a - 1`, then `F A` is at most `a - 1`.
   The standard t-structure orthogonality theorem
   (`lem-pc-derived-tstructure-orthogonality`) makes `Hom(F A,N)` a singleton.
   Each adjunction bijection makes `Hom(A,G N)` and `Hom(A,J N)` singletons.
   Apply the converse Hom test (`lem-pur-tstructure-lower-bound-hom-test`) to obtain
   both lower bounds. No additivity of `F` is needed for this singleton argument.
2. For bounded-below `N`, the unit isomorphism puts `U_X S_X N` in the same lower
   bound, since the standard t-structure is strictly full
   (`def-sbc-standard-tstructure-derived-category`). Step 1 now bounds both `D_N`
   and `E_N`. Take `r` inverse to the actual unit, `beta = G(r)` followed by the
   counit-normalized right-adjoint isomorphism (`det-sp-unique-right-adjoint`),
   and `alpha = S_Z(beta)`.
3. The triangle identity says `e` at `S_X N` composed after `S_X(eta_N)` is the
   identity. Inverting the latter gives `e` at `S_X N = S_X(r_N)`.
4. Counit naturality at `r_N` identifies `epsilon^G` followed by `r_N` with
   `F G(r_N)` followed by `epsilon^G_N`. Substitute the counit normalization of
   the canonical isomorphism to rewrite this as `F(beta_N)` followed by
   `epsilon^J_N`.
5. Naturality of `lambda` at `beta_N` moves `S_X F(beta_N)` past `lambda` inverse.
   Together with Steps 3 and 4 this gives the second formula for `t_N`.
6. Inverse-unit naturality and right-adjoint-isomorphism naturality give naturality
   of `r` and `beta`. Applying `S_Z` gives that of `alpha`. The formula for `t`
   is a composite of restricted natural transformations; Step 2 ensures that both
   applications of `lambda` lie in its bounded-below domain. Hence the formulas
   describe an equality of natural transformations, natural in all bounded-below `N`.
-/
theorem exactAdjoint_classicalCounitComparison
    {AZ : Type uAZ} [Category.{vAZ} AZ] [Abelian AZ] [HasDerivedCategory.{wAZ} AZ]
    {AX : Type uAX} [Category.{vAX} AX] [Abelian AX] [HasDerivedCategory.{wAX} AX]
    {BZ : Type uBZ} [Category.{vBZ} BZ] [Abelian BZ] [HasDerivedCategory.{wBZ} BZ]
    {BX : Type uBX} [Category.{vBX} BX] [Abelian BX] [HasDerivedCategory.{wBX} BX]
    (F : DerivedCategory AZ ⥤ DerivedCategory AX)
    (G J : DerivedCategory AX ⥤ DerivedCategory AZ)
    (adjG : F ⊣ G) (adjJ : F ⊣ J)
    (hFle : ∀ (m : ℤ) (H : DerivedCategory AZ), H.IsLE m → (F.obj H).IsLE m)
    (hFge : ∀ (m : ℤ) (H : DerivedCategory AZ), H.IsGE m → (F.obj H).IsGE m)
    (SZ : DerivedCategory AZ ⥤ DerivedCategory BZ)
    (SX : DerivedCategory AX ⥤ DerivedCategory BX)
    (hSZ : ∀ (a : ℤ) (H : DerivedCategory AZ), H.IsGE a → (SZ.obj H).IsGE a)
    (hSX : ∀ (a : ℤ) (N : DerivedCategory AX), N.IsGE a → (SX.obj N).IsGE a)
    (UX : DerivedCategory BX ⥤ DerivedCategory AX) (adjS : SX ⊣ UX)
    (hη : ∀ N : Plus AX, IsIso (adjS.unit.app N.obj))
    (P : DerivedCategory BZ ⥤ DerivedCategory BX)
    (comparison : Plus.ι (C := AZ) ⋙ F ⋙ SX ≅ Plus.ι (C := AZ) ⋙ SZ ⋙ P) :
    (∀ (a : ℤ) (N : DerivedCategory AX), N.IsGE a →
      (J.obj N).IsGE a ∧ (G.obj N).IsGE a) ∧
    ∃ (hD : ∀ N : Plus AX, TStructure.t.plus (J.obj N.obj))
      (hE : ∀ N : Plus AX, TStructure.t.plus (G.obj (UX.obj (SX.obj N.obj))))
      (r : Plus.ι (C := AX) ⋙ SX ⋙ UX ≅ Plus.ι (C := AX))
      (beta : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ≅ Plus.ι (C := AX) ⋙ J)
      (alpha : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ⋙ SZ ≅ Plus.ι (C := AX) ⋙ J ⋙ SZ)
      (t : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ⋙ SZ ⋙ P ⟶ Plus.ι (C := AX) ⋙ SX),
      (∀ N : Plus AX, r.inv.app N = adjS.unit.app N.obj) ∧
      (∀ N : Plus AX, beta.hom.app N =
        G.map (r.hom.app N) ≫ (adjG.rightAdjointUniq adjJ).hom.app N.obj) ∧
      (∀ N : Plus AX, alpha.hom.app N = SZ.map (beta.hom.app N)) ∧
      (∀ N : Plus AX, t.app N =
        comparison.inv.app ⟨G.obj (UX.obj (SX.obj N.obj)), hE N⟩ ≫
          SX.map (adjG.counit.app (UX.obj (SX.obj N.obj))) ≫
          adjS.counit.app (SX.obj N.obj)) ∧
      (∀ N : Plus AX, t.app N =
        P.map (alpha.hom.app N) ≫ comparison.inv.app ⟨J.obj N.obj, hD N⟩ ≫
          SX.map (adjJ.counit.app N.obj)) := by
  classical
  have bound (R : DerivedCategory AX ⥤ DerivedCategory AZ) (adj : F ⊣ R)
      (a : ℤ) (N : DerivedCategory AX) (hN : N.IsGE a) : (R.obj N).IsGE a := by
    apply (TStructure.t.isGE_iff_orthogonal (a - 1) a (by omega) _).2
    intro A f hA
    apply (adj.homEquiv A N).symm.injective
    have hFA := hFle (a - 1) A hA
    calc
      (adj.homEquiv A N).symm f = 0 :=
        TStructure.t.zero_of_isLE_of_isGE _ (a - 1) a (by omega) hFA hN
      _ = (adj.homEquiv A N).symm 0 :=
        (TStructure.t.zero_of_isLE_of_isGE _ (a - 1) a (by omega) hFA hN).symm
  have bounds : ∀ (a : ℤ) (N : DerivedCategory AX), N.IsGE a →
      (J.obj N).IsGE a ∧ (G.obj N).IsGE a :=
    fun a N hN ↦ ⟨bound J adjJ a N hN, bound G adjG a N hN⟩
  refine ⟨bounds, ?_⟩
  have hD (N : Plus AX) : TStructure.t.plus (J.obj N.obj) := by
    obtain ⟨a, ha⟩ := N.property
    exact ⟨a, (bounds a N.obj ha).1⟩
  have hE (N : Plus AX) : TStructure.t.plus (G.obj (UX.obj (SX.obj N.obj))) := by
    obtain ⟨a, ha⟩ := N.property
    have : N.obj.IsGE a := ha
    have := hη N
    have hU := TStructure.t.isGE_of_iso (X := N.obj)
      (asIso (adjS.unit.app N.obj)) a
    exact ⟨a, (bounds a _ hU).2⟩
  have : ∀ N : Plus AX, IsIso ((Functor.whiskerLeft (Plus.ι (C := AX)) adjS.unit).app N) := hη
  have : IsIso (Functor.whiskerLeft (Plus.ι (C := AX)) adjS.unit) :=
    NatIso.isIso_of_isIso_app _
  let r : Plus.ι (C := AX) ⋙ SX ⋙ UX ≅ Plus.ι (C := AX) :=
    (asIso (Functor.whiskerLeft (Plus.ι (C := AX)) adjS.unit)).symm
  let beta : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ≅ Plus.ι (C := AX) ⋙ J :=
    Functor.isoWhiskerRight r G ≪≫
      Functor.isoWhiskerLeft (Plus.ι (C := AX)) (adjG.rightAdjointUniq adjJ)
  let alpha : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ⋙ SZ ≅
      Plus.ι (C := AX) ⋙ J ⋙ SZ := Functor.isoWhiskerRight beta SZ
  let E : Plus AX ⥤ Plus AZ :=
    TStructure.t.plus.lift (Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G) hE
  let t : Plus.ι (C := AX) ⋙ SX ⋙ UX ⋙ G ⋙ SZ ⋙ P ⟶ Plus.ι (C := AX) ⋙ SX :=
    Functor.whiskerLeft E comparison.inv ≫
      Functor.whiskerRight (Functor.whiskerLeft (Plus.ι (C := AX) ⋙ SX ⋙ UX) adjG.counit) SX ≫
      Functor.whiskerLeft (Plus.ι (C := AX) ⋙ SX) adjS.counit
  refine ⟨hD, hE, r, beta, alpha, t, (fun _ ↦ rfl), (fun _ ↦ rfl),
    (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  intro N
  have := hη N
  have hc : adjS.counit.app (SX.obj N.obj) = SX.map (r.hom.app N) := by
    simp [r, ← adjS.inv_map_unit, ← Functor.map_inv]
  have hbeta : F.map (beta.hom.app N) ≫ adjJ.counit.app N.obj =
      adjG.counit.app (UX.obj (SX.obj N.obj)) ≫ r.hom.app N := by
    dsimp [beta]
    rw [F.map_comp, Category.assoc, adjG.rightAdjointUniq_hom_app_counit adjJ]
    exact adjG.counit.naturality (r.hom.app N)
  have hn := comparison.inv.naturality
    (show E.obj N ⟶ ⟨J.obj N.obj, hD N⟩ from ⟨beta.hom.app N⟩)
  change P.map (SZ.map (beta.hom.app N)) ≫ comparison.inv.app ⟨J.obj N.obj, hD N⟩ =
    comparison.inv.app (E.obj N) ≫ SX.map (F.map (beta.hom.app N)) at hn
  change comparison.inv.app (E.obj N) ≫
    SX.map (adjG.counit.app (UX.obj (SX.obj N.obj))) ≫
    adjS.counit.app (SX.obj N.obj) = _
  rw [hc, ← SX.map_comp, ← hbeta, SX.map_comp]
  change _ = P.map (SZ.map (beta.hom.app N)) ≫
    comparison.inv.app ⟨J.obj N.obj, hD N⟩ ≫ SX.map (adjJ.counit.app N.obj)
  rw [← Category.assoc, ← hn, Category.assoc]

end DerivedCategory
