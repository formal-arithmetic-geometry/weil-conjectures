/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus

/-! # Tensor laws of the specified finite etale reduction

Source: blueprint `lem-coef-finite-hom-site-descent`, final site comparison argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local implicit_reducible] CoefficientClosedStructure.tensor

private theorem domainSymmetry
    {A B : Type _} [Category A] [Category B]
    [mA : MonoidalCategory A] [mB : MonoidalCategory B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (hA : SA.monoidal = mA) (hB : SB.monoidal = mB)
    (βA : @SymmetricCategory A _ SA.monoidal)
    (βB : @SymmetricCategory B _ SB.monoidal)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (δ : tensor A ⋙ F ≅ F.prod F ⋙ tensor B) {W : Type _} (e : W)
    {BA : A → A → Type _} (σA : ∀ P Q, BA P Q)
    {BB : B → B → Type _} (σB : ∀ P Q, BB P Q)
    (hβA : ∀ P Q, HEq (βA.toBraidedCategory.braiding P Q) (σA P Q))
    (hβB : ∀ P Q, HEq (βB.toBraidedCategory.braiding P Q) (σB P Q))
    (hμ : HEq μ δ)
    (h : FiniteHomDomainMonoidal F (fun P Q ↦ δ.app (P, Q)) e σA σB) :
    CoefFiniteHomSymmetry SA SB βA βB F μ := by
  cases hA
  cases hB
  let := SA.monoidal
  let := SB.monoidal
  have hμeq : μ = δ := eq_of_heq hμ
  obtain ⟨s, _, ht, b, b', hb, hb', hbraid⟩ := h
  have ht' (P Q : A) : (s.μIso P Q).symm = μ.app (P, Q) :=
    eq_of_heq ((ht P Q).trans
      (heq_of_eq (congrArg (fun η ↦ η.app (P, Q)) hμeq)).symm)
  have hbA (P Q : A) : b P Q = βA.toBraidedCategory.braiding P Q :=
    eq_of_heq ((hb P Q).trans (hβA P Q).symm)
  have hbB (P Q : B) : b' P Q = βB.toBraidedCategory.braiding P Q :=
    eq_of_heq ((hb' P Q).trans (hβB P Q).symm)
  intro P Q
  change F.map (βA.toBraidedCategory.braiding P Q).hom ≫ (μ.app (Q, P)).hom =
    (μ.app (P, Q)).hom ≫ (βB.toBraidedCategory.braiding (F.obj P) (F.obj Q)).hom
  rw [← hbA, ← hbB, ← ht', ← ht']
  change F.map (b P Q).hom ≫ (s.μIso Q P).inv =
    (s.μIso P Q).inv ≫ (b' (F.obj P) (F.obj Q)).hom
  have hh := congrArg
    (fun f ↦ (s.μIso P Q).inv ≫ f ≫ (s.μIso Q P).inv) (hbraid P Q)
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hh.symm

private theorem domainStrong
    {A B : Type _} [Category A] [Category B]
    [mA : MonoidalCategory A] [mB : MonoidalCategory B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (hA : SA.monoidal = mA) (hB : SB.monoidal = mB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (δ : tensor A ⋙ F ≅ F.prod F ⋙ tensor B) {W : Type _} (e : W)
    {BA : A → A → Type _} (σA : ∀ P Q, BA P Q)
    {BB : B → B → Type _} (σB : ∀ P Q, BB P Q)
    (hμ : HEq μ δ)
    (h : FiniteHomDomainMonoidal F (fun P Q ↦ δ.app (P, Q)) e σA σB) :
    Nonempty (CoefFiniteHomStrong SA SB F μ) := by
  cases hA
  cases hB
  let := SA.monoidal
  let := SB.monoidal
  have hμeq : μ = δ := eq_of_heq hμ
  obtain ⟨s, _, ht, _⟩ := h
  refine ⟨⟨s, ?_⟩⟩
  intro P Q
  have he : (s.μIso P Q).symm = μ.app (P, Q) :=
    eq_of_heq ((ht P Q).trans
      (heq_of_eq (congrArg (fun η ↦ η.app (P, Q)) hμeq)).symm)
  exact congrArg Iso.symm he

private theorem etaleClosed_monoidal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    (finiteHomEtaleClosed l E X n).monoidal =
      (inferInstance : MonoidalCategory (finiteHomEtale l E X n)) := by
  have hc : finiteHomEtaleClosed l E X n =
      finiteHomEtaleClosedGeneral (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X :=
    eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n)
  rw [hc]
  exact (finiteHomEtaleClosed_existsUnique _ X).choose_spec.1.1

/-- Convert ambient scalar monoidality to the specified finite etale tensorator
and the prescribed Koszul symmetry. Source: blueprint thm-coef-finite-hom,
opening paragraph; normalization in finiteHomDomain_monoidal
(blueprint: lem-coef-finite-hom-etale-tensor-laws).

Proof: the closed normalization identifies the specified monoidal structure
with the native derived etale structure. Extract its CoreMonoidal witness
from finiteHomDomain_monoidal. Its heterogeneous tensor normalization then
identifies the inverse tensorator with finiteHomEtaleTensor. The two braiding
normalizations identify its symmetry witnesses with the supplied ones.
Precompose and postcompose the braidedness equation by inverse tensorators;
isomorphism cancellation gives the forward-tensorator equation used here.
This proof includes identity quotients and arbitrary derived objects. -/
theorem finiteHomEtaleTensorLaws
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (βet : ∀ n : ℕ, @SymmetricCategory (finiteHomEtale l E X n) _
      (finiteHomEtaleClosed l E X n).monoidal)
    (hβet : ∀ (n : ℕ) (P Q : finiteHomEtale l E X n),
      HEq ((βet n).toBraidedCategory.braiding P Q)
        (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) P Q))
    {n m : ℕ} (h : m ≤ n) :
    Nonempty (CoefFiniteHomStrong
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)) ∧
    CoefFiniteHomSymmetry
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (βet n) (βet m) (finiteHomEtaleReduction l E X h)
      (finiteHomEtaleTensor l E X h) := by
  obtain ⟨hm, hμ, _⟩ := finiteHomDomain_monoidal D l _hl E X h
  constructor
  · exact domainStrong _ _ (etaleClosed_monoidal l E X n)
      (etaleClosed_monoidal l E X m) (finiteHomEtaleReduction l E X h)
      (finiteHomEtaleTensor l E X h) _ _ _ _ hμ hm
  · exact domainSymmetry _ _ (etaleClosed_monoidal l E X n)
      (etaleClosed_monoidal l E X m) (βet n) (βet m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
      _ _ _ _ (hβet n) (hβet m) hμ hm

end WeilConjectures
