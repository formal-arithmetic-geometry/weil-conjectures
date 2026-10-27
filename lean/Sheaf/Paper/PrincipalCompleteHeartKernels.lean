/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.PrincipalCompleteProductCriterion

/-! # Kernels, cokernels, images and extensions of principal derived complete modules

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.14,
Definition 3.4.1 and Lemma 3.4.12, printed pp.20--23.
(blueprint: lem-sfb-principal-complete-heart-kernels).

The existing universal quotient-completion model specifies the strict quotient tower,
its K-flat computation and its augmented Roos unit. The model is a presentation of the
canonical construction, rather than an arbitrary endofunctor or an unspecified unit.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w t u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PrincipalQuotientCompletion.Model

/-- Completeness of a module means that the specified quotient-completion unit on its
complex in degree zero is invertible. The quotient tower uses powers `n+1`, for `n : ℕ`.
Source: Bhatt--Scholze, Definition 3.4.1 and Lemma 3.4.12, printed pp.20--23
(blueprint: lem-sfb-principal-complete-heart-kernels). -/
def IsCompleteModule {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {R : Sheaf J CommRingCat.{r}}
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    {a : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections}
    (F : Model R a)
    (M : ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) : Prop :=
  IsIso (F.unit.app ((DerivedCategory.singleFunctor _ 0).obj M))

/-- Maps between principal derived complete module sheaves have complete kernel,
cokernel and image, and extensions of complete modules are complete.

Source: Bhatt--Scholze, Lemma 3.4.14, printed p.23, with the regular-principal
quotient interpretation of Lemma 3.4.12
(blueprint: lem-sfb-principal-complete-heart-kernels).

Proof: By lem-weil-proetale-countable-products-exact, countable products are exact.
Apply lem-pe-roos-cone-calculus to the repeated-multiplication tower `(K,a)` to obtain
an exact derived functor T_a. On a module in degree zero it has amplitude [0,1],
since its representative is the two-term product complex with differential 1-shift.
The triangle of lem-sfb-regular-principal-completion-fiber identifies completeness
with T_a vanishing, by lem-sf-derived-homology-long-exact. Regularity is required on
R alone. For g between complete modules, its cone S has T_a(S)=0. Writing A=ker g
and B=coker g, the short exact complex sequence and
lem-pc-cone-short-exact-quasi-iso give A[1] → S → B[0] → A[2]. Its long exact
sequence identifies H^q(T_a(B)) with H^(q+2)(T_a(A)). Their possible supports
{0,1} and {-2,-1} are disjoint, so both vanish. Thus A and B are complete. Apply
cokernel closure to A → M and identify its cokernel with im g. Finally a short
exact sequence M → P → N gives a distinguished triangle, so exactness of T_a and
vanishing on its two endpoints imply vanishing on P. No arbitrary-submodule
closure, classical separatedness or finiteness assumption is used. -/
theorem complete_heart_kernels
    (T : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology T) R))]
    (a : (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology T) R)).sections)
    (_ha : Mono (globalSectionMultiplication R a)) (F : Model.{t + 1, t, max u (t + 1), w} R a) :
    (∀ (M N : ringedSiteModules.{max u (t + 1)}
        (SheafOfModules.derivedChangeRingIndependentCoefficients
          (AlgebraicGeometry.Scheme.ProEt.topology T) R)) (g : M ⟶ N),
      IsCompleteModule.{t + 1, t, max u (t + 1), w} F M →
      IsCompleteModule.{t + 1, t, max u (t + 1), w} F N →
        IsCompleteModule.{t + 1, t, max u (t + 1), w} F (kernel g) ∧
        IsCompleteModule.{t + 1, t, max u (t + 1), w} F (cokernel g) ∧
          IsCompleteModule.{t + 1, t, max u (t + 1), w} F (image g)) ∧
    (∀ S : ShortComplex (ringedSiteModules.{max u (t + 1)}
        (SheafOfModules.derivedChangeRingIndependentCoefficients
          (AlgebraicGeometry.Scheme.ProEt.topology T) R)),
      S.ShortExact → IsCompleteModule.{t + 1, t, max u (t + 1), w} F S.X₁ →
      IsCompleteModule.{t + 1, t, max u (t + 1), w} F S.X₃ →
        IsCompleteModule.{t + 1, t, max u (t + 1), w} F S.X₂) := by
  let A := ringedSiteModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology T) R)
  have hE (M N : A) (f : M ⟶ N) (hf : Epi f) :
      Epi (Limits.Pi.map (fun _ : ℕ ↦ f)) :=
    (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact T R).2.2
      ℕ (fun _ ↦ M) (fun _ ↦ N) (fun _ ↦ f) (fun _ ↦ hf)
  obtain ⟨hmap, hext⟩ := CountableScalarDifference.iso_closure
    (PrincipalCompletionFiber.scalar R a) hE
  have hcrit (M : A) : IsCompleteModule F M ↔
      IsIso ((CountableScalarDifference.difference
        (PrincipalCompletionFiber.scalar R a)).app M) :=
    complete_product_criterion T R a _ha F M
  constructor
  · intro M N g hM hN
    obtain ⟨hK, hC, hI⟩ := hmap M N g ((hcrit M).mp hM) ((hcrit N).mp hN)
    exact ⟨(hcrit _).mpr hK, (hcrit _).mpr hC, (hcrit _).mpr hI⟩
  · intro S hS hM hN
    exact (hcrit _).mpr (hext S hS ((hcrit _).mp hM) ((hcrit _).mp hN))

end CategoryTheory.PrincipalQuotientCompletion.Model
