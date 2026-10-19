/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence

/-!
# Composition for constructibility of higher direct images

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lem-finrepair-composition-c.md`, order 1599 (blueprint: lem-finrepair-composition-c).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

section SpectralSequence

variable {Z : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Homology is a cokernel of a map to the kernel of the outgoing differential. -/
private theorem constructible_homology
    (S : ShortComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [Scheme.IsConstructibleSheaf S.X₁] [Scheme.IsConstructibleSheaf S.X₂]
    [Scheme.IsConstructibleSheaf S.X₃] : Scheme.IsConstructibleSheaf S.homology := by
  have := Scheme.IsConstructibleSheaf.kernel S.g
  have := Scheme.IsConstructibleSheaf.cokernel (kernel.lift S.g S.f S.zero)
  exact Scheme.IsConstructibleSheaf.of_iso S.homologyIsoCokernelLift.symm

/-- Constructibility propagates simultaneously through all bidegrees of each page. -/
private theorem constructible_page
    (E : E₂CohomologicalSpectralSequenceNat
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : ∀ pq, Scheme.IsConstructibleSheaf ((E.page 2).X pq))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℕ × ℕ) :
    Scheme.IsConstructibleSheaf ((E.page r).X pq) := by
  induction r, hr using Int.leInduction generalizing pq with
  | base => exact hE pq
  | succ r hr ih =>
    have : Scheme.IsConstructibleSheaf ((E.page r).sc pq).X₁ := ih _
    have : Scheme.IsConstructibleSheaf ((E.page r).sc pq).X₂ := ih _
    have : Scheme.IsConstructibleSheaf ((E.page r).sc pq).X₃ := ih _
    have : Scheme.IsConstructibleSheaf ((E.page r).homology pq) :=
      constructible_homology ((E.page r hr).sc pq)
    exact Scheme.IsConstructibleSheaf.of_iso (E.iso r (r + 1) pq)

/-- Descend the finite abutment filtration, using constructible stable graded pieces. -/
private theorem constructible_abutment
    (E : E₂CohomologicalSpectralSequenceNat
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {H : ℕ → Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hE : E.AbutsTo H)
    (h₂ : ∀ pq, Scheme.IsConstructibleSheaf ((E.page 2).X pq)) (n : ℕ) :
    Scheme.IsConstructibleSheaf (H n) := by
  obtain ⟨A⟩ := hE
  have hstep (p : ℕ) (hp : p ≤ n + 1) :
      Scheme.IsConstructibleSheaf ((A.filtration n p : Subobject (H n)) :
        Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
    induction hp using Nat.decreasingInduction with
    | self =>
      rw [A.filtration_succ_self]
      exact Scheme.IsConstructibleSheaf.of_isZero
        ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
    | of_succ p hp ih =>
      let i := Subobject.ofLE _ _ (A.filtration_succ_le n p)
      obtain ⟨e⟩ := A.nonempty_gradedIso n p (n - p) (by omega)
      have : Scheme.IsConstructibleSheaf (E.pageInfinity (p, n - p)) :=
        constructible_page E h₂ (p + (n - p) + 2 : ℕ) (by omega) (p, n - p)
      have : Scheme.IsConstructibleSheaf (cokernel i) :=
        Scheme.IsConstructibleSheaf.of_iso e.symm
      have := ih
      apply Scheme.IsConstructibleSheaf.of_shortExact
        (S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i))
      exact ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)⟩
  have := hstep 0 (by omega)
  rw [A.filtration_zero] at this
  exact Scheme.IsConstructibleSheaf.of_iso (asIso (⊤ : Subobject (H n)).arrow)

end SpectralSequence

/-- If every higher direct image along `f` and along `g` preserves constructibility,
then every higher direct image along `f ≫ g` does as well, in the domain of property `C`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-composition-c.md`
(blueprint: lem-finrepair-composition-c); Stacks Project, Tags 0734, 015N and 03RZ.

Proof:
1. Fix a constructible `Λ`-module sheaf `F` on `X`. The hypotheses `C(f)` and `C(g)`
   successively make all `Rᵃg_*(Rᵇf_*F)` constructible for nonnegative `a` and `b`.
   The finite-value/finite-stalk comparison transfers this to `IsConstructibleSheaf`;
   `homologyRightDerivedFunctorPlusObjSingleFunctorIso` identifies the two models of `Rⁱ`.
2. Apply `lem-weil-pbc-grothendieck-spectral-sequence` to `f`, `g`, and `Λ`.
   Its second page consists of these sheaves, its terms vanish outside the first
   quadrant, its differentials have bidegree `(r,1-r)`, and its abutment in degree
   `n` is `Rⁿ(f ≫ g)_*F`, with a finite filtration by stable-page graded pieces.
   No acyclicity hypothesis on `F` or uniform dimension bound is required.
3. Induct simultaneously in all bidegrees on the page number `r ≥ 2`.
   The natural-number indexing encodes the first quadrant. The second-page terms
   are constructible by step 1. The kernel of an outgoing differential is
   constructible by `thm-constructible-serre`. The incoming differential factors
   through that kernel since its composite with the outgoing differential is zero.
   Its cokernel is constructible by the same theorem, and is the next-page term.
   This uses kernels and cokernels between constructible sheaves, not arbitrary
   subsheaves.
4. For each fixed `n` and `0 ≤ p ≤ n`, `pageInfinity (p,n-p)` is the term on page
   `p + (n-p) + 2`. Step 3 makes it constructible.
   The finite filtration of the degree-`n` abutment starts with the whole sheaf and
   ends at zero in step `n+1`. Descending induction on its steps, using extension
   closure in `thm-constructible-serre`, makes the whole abutment constructible.
   Since `n` and `F` are arbitrary, this is `C(f ≫ g)` by `def-finrepair-property-c`.
   Finally, `lowerStarComp` and functoriality of right derived functors identify the
   abutment with the higher direct image along `f ≫ g`. The stabilization bound
   depends on the bidegree; there is no uniform vanishing claim. -/
theorem hasConstructibleHigherDirectImages_comp
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hZ : IsSmoothBaseChangeCoefficients N Λ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasConstructibleHigherDirectImages k N Λ hX hY f)
    (hg : HasConstructibleHigherDirectImages k N Λ hY hZ g) :
    HasConstructibleHigherDirectImages k N Λ hX hZ (f ≫ g) := by
  intro n F hF
  obtain ⟨E, h₂, hE⟩ := exists_grothendieckSpectralSequence_lowerStar Λ f g F
  have hpages (pq : ℕ × ℕ) : Scheme.IsConstructibleSheaf ((E.page 2).X pq) := by
    have hfg := hg pq.1 (higherDirectImage Λ f pq.2 F) (hf pq.2 F hF)
    let ef := Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (lowerStar (ModuleCat.{u + 1} Λ) f) F pq.2
    let eg := Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (lowerStar (ModuleCat.{u + 1} Λ) g) (higherDirectImage Λ f pq.2 F) pq.1
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.Plus.homologyFunctor _ (pq.1 : ℤ)).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              (higherDirectImage Λ f pq.2 F)))) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hfg
    exact Scheme.IsConstructibleSheaf.of_iso
      (eg ≪≫ ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived pq.1).mapIso ef ≪≫
        (h₂ pq.1 pq.2).some.symm)
  have hc := constructible_abutment E hE hpages n
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  let e := lowerStarComp (ModuleCat.{u + 1} Λ) f g
  let e' : (((lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
      lowerStar (ModuleCat.{u + 1} Λ) g).rightDerived n) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerived n :=
    ⟨e.hom.rightDerived n, e.inv.rightDerived n,
      by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id],
      by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]⟩
  exact Scheme.IsConstructibleSheaf.of_iso
    (e'.app F ≪≫ (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)) F n).symm)

end AlgebraicGeometry.Etale
