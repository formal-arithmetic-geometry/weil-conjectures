/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompletedConstantConstructibility
public import Sheaf.Paper.AdicStratifiedPerfect
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion

import Sheaf.Paper.IntegralCohomologicalAdicCriterionAdicBridge
import Sheaf.Paper.IntegralCompletedConstantPerfect
import Sheaf.Paper.IntegralPerfectCohomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bridge from completed constant models to stratified perfect models

This is the local-model comparison needed to specialize the general adic
criterion to the integral coefficient presentation.
(blueprint: lem-sfb-integral-cohomological-adic-criterion-bridge)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Canonical coefficient-sized pro-etale sheafification instance.
Source: Stacks Tag 03DA
(blueprint: lem-sfb-integral-cohomological-adic-criterion-bridge). -/
instance (priority := 3000) integralCriterionWEqualsBridge (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

private theorem completed_constant_of_iso
    {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] {I : Ideal A}
    {M N : proEtaleRingModules X (adicLisseCompletedRing X I)}
    (e : M ≅ N) (hM : IsCompletedConstantStratified X I M) :
    IsCompletedConstantStratified X I N := by
  obtain ⟨s, hs, hM⟩ := hM
  refine ⟨s, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hM⟩ := hM a
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, ⟨eP⟩⟩ := hM U f hf
  refine ⟨P, hP, ⟨?_⟩⟩
  exact (SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion a) (adicLisseCompletedRing X I)).mapIso
      e.symm) ≪≫ eP

private theorem bounded_devissage
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) (D : ObjectProperty (DerivedCategory C))
    (hPiso : ∀ {M N : C}, (M ≅ N) → P M → P N)
    (hzero : D 0)
    (hiso : ∀ (K L : DerivedCategory C), Nonempty (K ≅ L) → D K → D L)
    (hshift : ∀ (K : DerivedCategory C) (n : ℤ), D K → D (K⟦n⟧))
    (htri : ∀ T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory C),
      T ∈ distTriang _ → D T.obj₁ → D T.obj₃ → D T.obj₂)
    (hsingle : ∀ M : C, P M → D ((DerivedCategory.singleFunctor C 0).obj M))
    (K : DerivedCategory C) (hK : DerivedCategory.TStructure.t.bounded K)
    (hH : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor C q).obj K)) : D K := by
  let t := DerivedCategory.TStructure.t (C := C)
  have key (n : ℕ) : ∀ (a : ℤ) (L : DerivedCategory C), L.IsGE a →
      L.IsLE (a + n - 1) →
      (∀ q : ℤ, a ≤ q → q < a + n →
        P ((DerivedCategory.homologyFunctor C q).obj L)) → D L := by
    induction n with
    | zero =>
      intro a L _ hL _
      have : L.IsLE (a - 1) := by simpa using hL
      have hz := t.isZero L (a - 1) a (by omega)
      exact hiso 0 L ⟨hz.isoZero.symm⟩ hzero
    | succ n ih =>
      intro a L _ hL hH
      let b : ℤ := a + n
      have : L.IsLE b := t.isLE_of_le L (a + ↑(n + 1) - 1) b (by omega)
      let T := (t.triangleLTGE b).obj L
      have : T.obj₃.IsLE b := inferInstanceAs (t.IsLE ((t.truncGE b).obj L) b)
      have : T.obj₃.IsGE b := inferInstanceAs (t.IsGE ((t.truncGE b).obj L) b)
      obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
        T.obj₃ b
      have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L b b le_rfl
      have hM : P M := hPiso
        (asIso ((DerivedCategory.homologyFunctor C b).map ((t.truncGEπ b).app L)) ≪≫
          (DerivedCategory.homologyFunctor C b).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app M)
        (hH b (by omega) (by omega))
      have h₃ : D T.obj₃ := hiso _ _ ⟨e.symm⟩
        (hiso _ _ ⟨((DerivedCategory.singleFunctors C).shiftIso (-b) b 0
          (by omega)).app M⟩ (hshift _ (-b) (hsingle M hM)))
      have h₁ : D T.obj₁ := by
        refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
        · exact inferInstanceAs (t.IsGE ((t.truncLT b).obj L) a)
        · exact t.isLE_truncLT_obj _ _ _ (by omega)
        · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app L b q (by omega)
          exact hPiso (asIso ((DerivedCategory.homologyFunctor C q).map
            ((t.truncLTι b).app L))).symm (hH q hq (by omega))
      exact htri T (t.triangleLTGE_distinguished b L) h₁ h₃
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  have : K.IsGE a := ha
  have : K.IsLE (a + ↑(b - a + 1).toNat - 1) := t.isLE_of_le K b _ (by omega)
  exact key (b - a + 1).toNat a K ha this (fun q _ _ ↦ hH q)

/-- The completed-constant cohomology presentation is equivalent to the finite
stratified-perfect presentation for the integral completed coefficient ring.
This is the coefficient-model comparison in Bhatt--Scholze, Proposition
6.8.11(3): finitely presented modules over the DVR admit finite free
resolutions. Exact constant realization, completed scalar extension and restriction
compare the actual local models without changing their inverse-image coefficient rings.
Proof: specialize the general adic criterion using integral_coefficient_hypotheses.
A completed-constant constructible module in degree zero is perfect locally, by
integral_completed_constant_single_perfect, hence adic constructible. Induct over a finite
cohomological interval using the canonical truncation triangle. Its upper term is a shifted
single cohomology module and its lower term has shorter interval; the zero-length case is
zero. Closure under shifts, isomorphisms and triangles gives the forward implication.
Conversely the general adic criterion supplies boundedness, and
integral_perfect_cohomology_completed_constant supplies constructibility in every degree.
(blueprint: lem-sfb-integral-cohomological-adic-criterion-bridge)
-/
theorem integral_completed_constant_iff_stratified_perfect
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (proEtaleRingModules X
      (adicLisseCompletedRing X
        (ProEtale.IntegralConstantCompletion.ideal l E)))) :
    (DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsCompletedConstantStratified X
        (ProEtale.IntegralConstantCompletion.ideal l E)
        ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
      IsSfbStratifiedPerfect X
        (ProEtale.IntegralConstantCompletion.ideal l E) K := by
  have hc := integral_coefficient_hypotheses l E
  have := hc.1
  have := hc.2.2
  have hd := adic_stratified_perfect X
    (ProEtale.IntegralConstantCompletion.integers l E)
    (ProEtale.IntegralConstantCompletion.ideal l E) hc.2.1
  constructor
  · rintro ⟨hK, hH⟩
    apply (hd.1 K).mp
    exact bounded_devissage
      (IsCompletedConstantStratified X (ProEtale.IntegralConstantCompletion.ideal l E))
      (IsSfbAdicConstructible X (ProEtale.IntegralConstantCompletion.ideal l E))
      (fun e h ↦ completed_constant_of_iso e h) hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1
      (fun T hT h₁ h₃ ↦ (hd.2.2.2.2.2 T hT).2.2 ⟨h₃, h₁⟩)
      (fun M hM ↦ (hd.1 _).mpr (integral_completed_constant_single_perfect l E X M hM))
      K hK hH
  · intro hK
    obtain ⟨a, b, _, ha, hb⟩ := hd.2.1 K ((hd.1 K).mpr hK)
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
      integral_perfect_cohomology_completed_constant l E X K hK⟩

end AlgebraicGeometry.Scheme
