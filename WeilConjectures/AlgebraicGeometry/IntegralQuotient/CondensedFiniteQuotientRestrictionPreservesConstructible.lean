/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.InternalQuotientRestriction
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization

/-! # Constructibility under finite quotient scalar restriction

Source: finite constant models in the principal-quotient coefficient argument.
(blueprint: lem-sf-condensed-finite-quotient-restriction-preserves-constructible). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local instance] Abelian.hasFiniteBiproducts

private noncomputable def diagonalCokernel
    {C : Type*} [Category C] [Abelian C] {ι : Type} [Fintype ι]
    (A B : ι → C) (f : ∀ i, A i ⟶ B i) :
    cokernel (biproduct.map f) ≅ ⨁ fun i ↦ cokernel (f i) := by
  classical
  let g := biproduct.map f
  let q := biproduct.map (fun i ↦ cokernel.π (f i))
  have hgq : g ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro i
    simp [g, q]
  let a := cokernel.desc g q hgq
  have hf (i : ι) : f i ≫ biproduct.ι B i ≫ cokernel.π g = 0 := by
    simpa only [g, biproduct.ι_map_assoc, Limits.comp_zero] using
      biproduct.ι A i ≫= cokernel.condition g
  let b := biproduct.desc (fun i ↦ cokernel.desc (f i)
    (biproduct.ι B i ≫ cokernel.π g) (hf i))
  refine ⟨a, b, ?_, ?_⟩
  · change a ≫ b = 𝟙 _
    apply (cancel_epi (cokernel.π g)).mp
    apply biproduct.hom_ext'
    intro i
    simp [a, b, q]
  · change b ≫ a = 𝟙 _
    apply biproduct.hom_ext'
    intro i
    apply (cancel_epi (cokernel.π (f i))).mp
    simp [a, b, q]

private def PrincipalPresented {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ f : End (Mod.regular R), Nonempty (M ≅ cokernel f)

private theorem principal_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : PrincipalPresented R M) :
    PrincipalPresented ((upperStar Ab.{u + 1} g).obj R)
      (((upperStar Ab.{u + 1} g).mapMod R).obj M) := by
  obtain ⟨f, ⟨e⟩⟩ := h
  let F := (upperStar Ab.{u + 1} g).mapMod R
  let er : F.obj (Mod.regular R) ≅ Mod.regular _ :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  let f' := er.inv ≫ F.map f ≫ er.hom
  exact ⟨f', ⟨F.mapIso e ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso _ f' er er (by simp [f'])⟩⟩

section
variable {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (hreg : PrincipalPresented R ((Mod.comap φ).obj (Mod.regular S)))

include hreg

private theorem restriction_free_fp (k : ℕ) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj (Mod.finiteFree S k)) :=
  hreg.elim fun f he ↦ he.elim fun e ↦ ⟨k, k, biproduct.map (fun _ : Fin k ↦ f),
    ⟨(Mod.comap φ).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫
      (diagonalCokernel _ _ (fun _ : Fin k ↦ f)).symm⟩⟩

private theorem restriction_fp_lfp
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : Mod.IsFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hM
  exact lfp_of_iso (CondensedRing.lfp_cokernel_of_fp ((Mod.comap φ).map f)
    (restriction_free_fp φ hreg m) (restriction_free_fp φ hreg n))
    ((Mod.comap φ).mapIso e ≪≫ PreservesCokernel.iso (Mod.comap φ) f).symm

private theorem principal_comap_pullback {Y : Scheme.{u}} (g : Y ⟶ X) :
    PrincipalPresented ((upperStar Ab.{u + 1} g).obj R)
      ((Mod.comap ((upperStar Ab.{u + 1} g).map φ)).obj
        (Mod.regular ((upperStar Ab.{u + 1} g).obj S))) := by
  let F := upperStar Ab.{u + 1} g
  obtain ⟨f, ⟨e⟩⟩ := principal_pullback (R := R)
    (M := (Mod.comap φ).obj (Mod.regular S)) g hreg
  let er : (F.mapMod S).obj (Mod.regular S) ≅ Mod.regular (F.obj S) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  exact ⟨f, ⟨((Mod.comap (F.map φ)).mapIso er).symm ≪≫
    ((F.mapModComapIso φ).app (Mod.regular S)).symm ≪≫ e⟩⟩

private theorem restriction_lfp
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨U, hU⟩ := hM
  have hv (i : U.I₀) :
      IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj ((Mod.comap φ).obj M)) := by
    let F := upperStar Ab.{u + 1} (U.f i)
    exact lfp_of_iso
      (restriction_fp_lfp (F.map φ) (principal_comap_pullback φ hreg (U.f i)) (hU i))
      ((F.mapModComapIso φ).app M).symm
  choose V hV using hv
  refine ⟨U.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (fp_pullback_comp_iff ((V i).f j) (U.f i) ((Mod.comap φ).obj M)).mpr
    (hV i j)

private theorem restriction_constructible
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨V, hV⟩ := hM
  refine ⟨V, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (V.immersion i)
  exact lfp_of_iso
    (restriction_lfp (F.map φ) (principal_comap_pullback φ hreg (V.immersion i))
      (hV i)) ((F.mapModComapIso φ).app M).symm
end
end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.IntegralQuotient


/-- Restricting between positive finite uniformizer quotients preserves constructibility
on the same finite constructible stratifications.
Source: current blueprint integral Hom reduction, finite coefficient comparison;
Bhatt--Scholze Section 6.8, Stacks 03DA and 03D2.
(blueprint: lem-sf-condensed-finite-quotient-restriction-preserves-constructible).
Proof: the normalized principal sequence presents the restricted regular
B-module over the integral coefficient ring by one generator and one relation.
Finite sums give presentations of the restricted finite free B-modules.
Restriction is exact, so restrict a presentation of M and apply closure of
local finite presentation under cokernels. Pullback commutes with restriction
and preserves the principal presentation. Bind the resulting presentation
covers and retain the original finite stratification. Thus restriction of M
to the integral coefficient ring is constructible. The integral reduction
onto D is an epimorphism; its fully faithful restriction reflects
constructibility by the extension-restriction counit. The factorization of
integral reduction through D identifies this restriction with that of the
D-module in the conclusion. Empty strata and zero ranks are included. -/
theorem finiteQuotientRestriction_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (r n : ℕ) (h : n ≤ r)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T)) :
    IsConstructibleModuleObject (condensedRingObj (finite l E n) T) M →
      IsConstructibleModuleObject (condensedRingObj (finite l E r) T)
        ((Mod.comap (coefficientMap (finiteMap l E r n h) T)).obj M) := by
  intro hM
  let R := condensedRingObj (integral l E) T
  let D := condensedRingObj (finite l E r) T
  let B := condensedRingObj (finite l E n) T
  let q := coefficientMap (reduction l E n) T
  let p := coefficientMap (reduction l E r) T
  let φ := coefficientMap (finiteMap l E r n h) T
  obtain ⟨_, _, _, _, _, hn⟩ :=
    (integral_quotient_resolution_normalization l E).2.2 T
  obtain ⟨_, ⟨w, ⟨hc⟩, _⟩, _⟩ := hn n
  have hreg : PrincipalPresented R ((Mod.comap q).obj (Mod.regular B)) :=
    ⟨multiplication l E T n,
      ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩
  have hcM := restriction_constructible q hreg hM
  have he : q = p ≫ φ := by
    dsimp [q, p, φ]
    rw [← coefficientMap_comp, reduction_comp]
  let e : (Mod.comap q).obj M ≅ (Mod.comap p).obj ((Mod.comap φ).obj M) :=
    (Mod.comapCongr he).app M ≪≫ (Mod.comapComp p φ).app M
  have : Epi p := epi_coefficientMap_reduction l E T r
  exact CondensedRing.constructible_of_comap_of_epi T R D p _
    (_root_.constructible_of_iso e hcM)

end AlgebraicGeometry.ProEtale.IntegralQuotient
