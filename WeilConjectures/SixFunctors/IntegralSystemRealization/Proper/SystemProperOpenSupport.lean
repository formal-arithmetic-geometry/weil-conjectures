/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
import WeilConjectures.AlgebraicGeometry.ProperOpenSquareSupport.ProperOpenSquareDerivedSupport

/-! # Support and invertibility of the unbounded system proper/open mate

Source: Stacks 0F7B, open support and the open-adjunction normalization.
(blueprint: lem-sf-system-proper-open-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

private theorem evaluated_counit_isIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {J : C ⥤ D} {P : D ⥤ C} {j : C' ⥤ D'} {p : D' ⥤ C'}
    (a : J ⊣ P) (b : j ⊣ p) (F : C ⥤ C') (G : D ⥤ D')
    (e : J ⋙ G ≅ F ⋙ j) (t : P ⋙ F ≅ G ⋙ p)
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans = e.inv)
    (M : D) [IsIso (b.counit.app (G.obj M))] :
    IsIso (G.map (a.counit.app M)) := by
  have hm := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ t.hom) M
  change j.map (t.hom.app M) ≫ b.counit.app (G.obj M) =
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans).app (P.obj M) ≫
      G.map (a.counit.app M) at hm
  rw [he] at hm
  change j.map (t.hom.app M) ≫ b.counit.app (G.obj M) =
    e.inv.app (P.obj M) ≫ G.map (a.counit.app M) at hm
  have : IsIso (e.inv.app (P.obj M) ≫ G.map (a.counit.app M)) := by
    rw [← hm]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.inv.app (P.obj M)) (G.map (a.counit.app M))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (o : Operations l E)

/-- Proper direct image of an open extension is supported in the target open for
any commuting proper/open square, on arbitrary unbounded system inputs.
Source: Stacks 0F7B
(blueprint: lem-sf-system-proper-open-support).

Proof: at each positive coefficient level the direct-image and open-extension
comparisons identify the evaluated target with the finite-coefficient proper image
of an open extension. The finite square support theorem makes its open counit
invertible. The counit mate identity and the recorded open-evaluation transpose
identify the evaluated system counit with that counit, up to the two invertible
comparison factors. Joint conservativity of the actual derived evaluations concludes.
-/
theorem systemProperOpenSupportedCounit
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : System l E U) :
    IsIso ((o.extension i).adj.counit.app
      ((Operations.push l E o p).obj ((Operations.shriek l E o k).obj M))) := by
  apply ((calculus l E Z).isIso_iff_evaluations _).2
  intro n
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let N := (Operations.push l E o p).obj ((Operations.shriek l E o k).obj M)
  let ev (X : Scheme.{u}) := coefficientSequenceDerivedEvaluation l E X n
  let d : (ev Z).obj N ≅ (proEtaleConstantDerivedDirectImage p A).obj
      ((sfIntrinsicDerivedOpen A k).obj ((ev U).obj M)) :=
    ((o.evaluation p).evaluation n).app ((Operations.shriek l E o k).obj M) ≪≫
      (proEtaleConstantDerivedDirectImage p A).mapIso
        (((o.openEvaluation k).evaluation n).app M)
  have hs := ProperOpenSquareSupport.derived_support_square p k i r h A ((ev U).obj M)
  have hd : IsIso ((finiteOpenAdj l E i n).counit.app ((ev Z).obj N)) := by
    change IsIso ((exceptionalOpenAdjunction i A).counit.app ((ev Z).obj N))
    exact (NatTrans.isIso_app_iff_of_iso (exceptionalOpenAdjunction i A).counit d).2 hs
  exact evaluated_counit_isIso (o.extension i).adj (finiteOpenAdj l E i n)
    (ev W) (ev Z) ((o.openEvaluation i).evaluation n)
    (pullbackTensorDerivedEvaluation l E i n) ((o.openEvaluation i).transpose n) N

/-- The prescribed proper/open comparison is invertible on arbitrary system inputs.
Source: Stacks 0F7B and the recorded open-adjunction transpose
(blueprint: lem-sf-system-proper-open-support).

Proof: its open adjunct is the inverse of the specified lambda isomorphism.
The target open counit is invertible by proper/open support. The inverse Hom
bijection writes the comparison as open extension of inverse lambda followed
by that counit, hence as a composite of isomorphisms. -/
theorem systemProperOpenGammaIsIso
    (F : WeilConjectures.FiniteFieldDatum.{u}) (z : Realizations l E F o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsIso (z.properOpen.gamma k r p i h) := by
  have hi (M : System l E U) : IsIso ((z.properOpen.gamma k r p i h).app M) := by
    let : IsIso ((o.extension i).adj.counit.app
        ((Operations.shriek l E o k ⋙ Operations.push l E o p).obj M)) :=
      systemProperOpenSupportedCounit l E o k r p i h M
    have he := z.properOpen.adjunct k r p i h M
    have hm := congrArg ((o.extension i).adj.homEquiv _ _).symm he
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at hm
    rw [hm]
    infer_instance
  exact NatIso.isIso_of_isIso_app _
end WeilConjectures.IntegralSystemRealization
