/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SecSmoothPurity.DetPropSfCbc

/-!
# Closed-boundary vanishing for condensed rational proper images

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`,
Lemmas 6.7.5 and 6.7.7, Proposition 6.8.14 and Remark 6.8.15, together with
Lemmas 6.1.11 and 6.1.15 (blueprint: lem-fix-condensed-proper-boundary-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

/-- Pullback to the closed complement of a quasi-compact open is zero after proper
pushforward of exact extension by zero. The input coefficients are the condensed ring
of a finite extension of `ℚ_ℓ` or the finite-subextension-valued condensed algebraic
closure. There is no density condition on the source open, no Cartesian-square condition, and no
requirement that its image exhaust the inverse image of the target open.

Proof:
1. Use the supplied compactification U --a--> W --h--> Z of a ≫ h. These three
schemes are Noetherian because they are finite type over the field k. Apply condensed
compact-support base change directly to K, avoiding any constructibility assertion for a_!K.
2. Put d : W ×_Z C --> W. Its image is disjoint from a(U): otherwise the common
point maps under h both into i(V), by the factorization, and into c(C), its complement.
Underived disjoint-support vanishing, exact-functor cohomology, and the exact/total
pullback comparison therefore give Ld^*D(a_!)K = 0.
3. The canonical open base-change isomorphism identifies this zero object with
D(a'_!)Ld_U^*K in the pulled-back compactification. Its proper derived direct image
is zero. The compact-support exchange from step 1 identifies that object with
Lc^*Rh_*D(a_!)K, proving the assertion. No identity-open comparison or additional
support equality is needed. Empty opens and boundaries, nonreduced boundaries,
and extra inverse-image components are included.
Source: Bhatt--Scholze, Lemmas 6.7.5 and 6.7.7, Proposition 6.8.14 and
Remark 6.8.15, and Lemmas 6.1.11 and 6.1.15
(blueprint: lem-fix-condensed-proper-boundary-vanishing). -/
theorem isZero_closedBoundary_pullback_properPushforward_openExtension
    {k : Type u} [Field k] (ell : ℕ) [Fact ell.Prime]
    [Fact (ringChar k ≠ ell)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {W Z U V C : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = ⟨Profinite.continuousMapRingObj E.1⟩ ∨
      Λ = ⟨Profinite.padicAlgClRingObj ell⟩)
    (h : W ⟶ Z) [IsProper h.left]
    (a : U ⟶ W) [IsOpenImmersion a.left] [QuasiCompact a.left]
    (i : V ⟶ Z) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (hfactor : ∃ q : U ⟶ V, a ≫ h = q ≫ i)
    (c : C ⟶ Z) [IsClosedImmersion c.left]
    (hC : Set.range c.left.base = (Set.range i.left.base)ᶜ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj Λ.X U.left)))
    (hK : boundedConstructible (condensedRingObj Λ.X U.left) K) :
    IsZero ((moduleObjectDerivedPullback Λ.X c.left).obj
        ((moduleObjectDerivedPushforward Λ.X h.left).obj
          (((a.left)_!open⟦Λ.X⟧).mapDerivedCategory.obj K))) := by
  let f := a.left ≫ h.left
  let t : Compactification f :=
    { Z := W.left
      g := h.left
      i := a.left
      comm := rfl
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have : IsNoetherian W.left := isNoetherian_of_locallyOfFiniteType W.hom
  have : IsNoetherian Z.left := isNoetherian_of_locallyOfFiniteType Z.hom
  have : IsNoetherian U.left := isNoetherian_of_locallyOfFiniteType U.hom
  have hcoeff :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    rcases hΛ with hΛ | hΛ
    · subst Λ
      exact Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)
    · subst Λ
      exact Or.inr (Or.inr ⟨Iso.refl _⟩)
  have hdisj : Disjoint (Set.range a.left.base)
      (Set.range (pullback.fst h.left c.left).base) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    obtain ⟨q, hq⟩ := hfactor
    have hq' : a.left ≫ h.left = q.left ≫ i.left := congrArg Over.Hom.left hq
    have him : h.left.base (a.left.base y) ∈ Set.range i.left.base := by
      exact ⟨q.left.base y, (congrArg (fun v : U.left ⟶ Z.left ↦ v.base y) hq').symm⟩
    have hcm : h.left.base (a.left.base y) ∈ Set.range c.left.base := by
      rw [← hz]
      exact ⟨(pullback.snd h.left c.left).base z,
        (congrArg (fun v : pullback h.left c.left ⟶ Z.left ↦ v.base z)
          (pullback.condition (f := h.left) (g := c.left))).symm⟩
    rw [hC] at hcm
    exact hcm him
  have hz : IsZero ((upperStar Λ.X (pullback.fst h.left c.left)).mapDerivedCategory.obj
      ((openImmersionLowerShriek Λ.X a.left).mapDerivedCategory.obj K)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ.X
      a.left (pullback.fst h.left c.left) hdisj
      ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso
      ((upperStar Λ.X (pullback.fst h.left c.left)).mapIso
        (((openImmersionLowerShriek Λ.X a.left).mapDerivedCategoryHomologyFunctorIso n).symm.app K))
  have hz' := hz.of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X (pullback.fst h.left c.left)).app _)
  let β := compactSupportOpenBaseChangeIso Λ.X f c.left t
  have hz'' := hz'.of_iso (β.app K).symm
  have hzout :=
    ((lowerStar Λ.X (pullback.snd h.left c.left)).rightDerivedFunctor).map_isZero hz''
  have he := (condensed_compactSupportBaseChange ell Λ.X hcoeff f c.left t K hK).2.2
  exact hzout.of_iso
    (asIso ((detSfCompactSupportBaseChangeComposite Λ.X f c.left t β).app K))

end AlgebraicGeometry.ProEtale.CondensedRing
