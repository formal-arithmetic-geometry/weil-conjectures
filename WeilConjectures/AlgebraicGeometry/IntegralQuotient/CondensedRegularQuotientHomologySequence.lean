/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.InternalQuotientRestriction
import WeilConjectures.CategoryTheory.ModuleObjects.InternalScalarProjectionFormula
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # The cohomology sequence of a principal quotient over a common finite ring

Source: current blueprint integral Hom reduction, two-term principal resolution.
(blueprint: lem-sf-condensed-regular-quotient-homology-sequence). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open MonoidalCategory Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.MonObj

private theorem fiveTermShortExact
    {C : Type*} [Category C] [Abelian C] {A B M D E : C}
    (f : A ⟶ B) (g : B ⟶ M) (h : M ⟶ D) (i : D ⟶ E)
    (w₁ : f ≫ g = 0) (w₂ : g ≫ h = 0) (w₃ : h ≫ i = 0)
    (he₁ : (ShortComplex.mk f g w₁).Exact)
    (he₂ : (ShortComplex.mk g h w₂).Exact)
    (he₃ : (ShortComplex.mk h i w₃).Exact) :
    ∃ (j : cokernel f ⟶ M) (p : M ⟶ kernel i) (w : j ≫ p = 0),
      (ShortComplex.mk j p w).ShortExact := by
  let j := cokernel.desc f g w₁
  let p := kernel.lift i h w₃
  have w : j ≫ p = 0 := by
    apply (cancel_epi (cokernel.π f)).mp
    apply (cancel_mono (kernel.ι i)).mp
    simp [j, p, Category.assoc, w₂]
  have : Mono j := he₁.mono_cokernelDesc
  have : Epi p := he₃.epi_kernelLift
  refine ⟨j, p, w, ⟨?_⟩⟩
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  have hxh : x ≫ h = 0 := by
    simpa [p, Category.assoc] using congrArg (fun t ↦ t ≫ kernel.ι i) hx
  obtain ⟨T', σ, hσ, y, hy⟩ := he₂.exact_up_to_refinements x hxh
  refine ⟨T', σ, hσ, y ≫ cokernel.π f, ?_⟩
  simpa [j, Category.assoc] using hy

private theorem liftExactPair
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Full] [F.Faithful] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Z : A} {X' Y' Z' : B}
    (eX : X' ≅ F.obj X) (eY : Y' ≅ F.obj Y) (eZ : Z' ≅ F.obj Z)
    (f : X' ⟶ Y') (g : Y' ⟶ Z') (w : f ≫ g = 0)
    (he : (ShortComplex.mk f g w).Exact)
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (ha : F.map a = eX.inv ≫ f ≫ eY.hom)
    (hb : F.map b = eY.inv ≫ g ≫ eZ.hom) :
    ∃ w' : a ≫ b = 0, (ShortComplex.mk a b w').Exact := by
  have w' : a ≫ b = 0 := by
    apply F.map_injective
    rw [F.map_comp, ha, hb, F.map_zero]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc f g, w, zero_comp, comp_zero]
  refine ⟨w', (ShortComplex.exact_map_iff_of_faithful _ F).mp ?_⟩
  exact ShortComplex.exact_of_iso
    (ShortComplex.isoMk eX eY eZ (by simp [ha]) (by simp [hb])) he

namespace AlgebraicGeometry.ProEtale.IntegralQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n m : ℕ)

private theorem reductionTriangle
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integral l E) T))) :
    ∃ Δ : CategoryTheory.Pretriangulated.Triangle
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integral l E) T))),
      Δ ∈ distTriang _ ∧
      Nonempty (Δ.obj₁ ≅ L) ∧ Nonempty (Δ.obj₂ ≅ L) ∧
      Nonempty (Δ.obj₃ ≅ (restrict l E T m).obj ((scalar l E T m).obj L)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (integral l E) T)
  let B := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (finite l E m) T)
  let V : B ⥤ A := Mod.comap (coefficientMap (reduction l E m) T)
  obtain ⟨_, _, _, _, _, hn⟩ :=
    (integral_quotient_resolution_normalization l E).2.2 T
  obtain ⟨hmono, ⟨w, ⟨hc⟩, _⟩, _⟩ := hn m
  have := hmono
  have : Epi (projection l E T m) := epi_of_isColimit_cofork hc
  let S := ShortComplex.mk (multiplication l E T m) (projection l E T m) w
  have hs : S.ShortExact := ⟨S.exact_of_g_is_cokernel hc⟩
  let Δ := (MonoidalCategory.tensorRight L).mapTriangle.obj hs.singleTriangle
  have hΔ := (MonoidalCategory.tensorRight L).map_distinguished _
    hs.singleTriangle_distinguished
  let e : Δ.obj₁ ≅ L :=
    MonoidalCategory.whiskerRightIso (DerivedCategory.singleFunctorObjUnitIso A) L ≪≫
      λ_ L
  let e' : Δ.obj₂ ≅ L := e
  let eB := ((V.mapDerivedCategorySingleFunctor 0).app
      (Mod.regular (condensedRingObj (finite l E m) T))).symm ≪≫
    V.mapDerivedCategory.mapIso (DerivedCategory.singleFunctorObjUnitIso B)
  obtain ⟨p⟩ := Mod.derived_scalarProjection (coefficientMap (reduction l E m) T) L
    (𝟙_ (DerivedCategory B))
  refine ⟨Δ, hΔ, ⟨e⟩, ⟨e'⟩, ⟨?_⟩⟩
  exact MonoidalCategory.whiskerRightIso eB L ≪≫ p.symm ≪≫
    V.mapDerivedCategory.mapIso (λ_ _)

/-- Input cohomology with its action restricted from level n to the common
quotient at level max(n,m).
Source: principal quotient cohomology argument
(blueprint: lem-sf-condensed-regular-quotient-homology-sequence). -/
abbrev commonInputHomology
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T))) (q : ℤ) :=
  (Mod.comap (coefficientMap (finiteMap l E (max n m) n (le_max_left _ _)) T)).obj
    ((DerivedCategory.homologyFunctor _ q).obj K)

/-- Reduced cohomology, retaining its actual quotient action and restricting it
to the same common finite quotient.
Source: principal quotient cohomology argument
(blueprint: lem-sf-condensed-regular-quotient-homology-sequence). -/
abbrev commonReductionHomology
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T))) (q : ℤ) :=
  (Mod.comap (coefficientMap (finiteMap l E (max n m) m (le_max_right _ _)) T)).obj
    ((DerivedCategory.homologyFunctor _ q).obj
      ((scalar l E T m).obj ((restrict l E T n).obj K)))

set_option maxHeartbeats 1600000 in
-- Descending five cohomology maps unfolds several derived-functor comparison isomorphisms.
/-- Cohomology of reduction of a restricted quotient complex is an extension
of a cokernel on H^q(K) by a kernel on H^(q+1)(K), over the common finite quotient.
No constructibility, boundedness or Tor hypothesis on K is needed here.
Source: latest blueprint lem-coef-integral-hom-reduction, two-term resolution;
Stacks 06YY, 014E and 015F.
(blueprint: lem-sf-condensed-regular-quotient-homology-sequence).
Proof: tensor the exact principal resolution of O_E/pi^(m+1) with Res K.
Its normalized cone gives the triangle L --pi^(m+1)--> L -> Res(red_m L).
Exact restriction identifies H^q(L) with Res H^q(K). The triangle's long
exact sequence yields a short exact sequence from the cokernel on H^q(L)
to the middle cohomology to the kernel on H^(q+1)(L). All three objects have
action through D = O_E/pi^(max(n,m)+1): the outer two through the quotient
at n, the middle through the quotient at m. The integral coefficient map
onto D is an epimorphism, so restriction from D-modules is fully faithful
and reflects exactness. Hence the maps and their equations descend uniquely
to D, giving the displayed short exact sequence. The descended endomorphisms
are multiplication by pi^(m+1). The argument is degreewise and includes
unbounded K, m or n zero, the zero complex and the empty scheme. -/
theorem commonReductionHomology_shortExact
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T))) (q : ℤ) :
    ∃ (f : End (commonInputHomology l E T n m K q))
      (g : End (commonInputHomology l E T n m K (q + 1)))
      (i : cokernel f ⟶ commonReductionHomology l E T n m K q)
      (p : commonReductionHomology l E T n m K q ⟶ kernel g)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact := by
  let R := condensedRingObj (integral l E) T
  let D := condensedRingObj (finite l E (max n m)) T
  let B := condensedRingObj (finite l E n) T
  let C := condensedRingObj (finite l E m) T
  let φ := coefficientMap (reduction l E (max n m)) T
  let F : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) D ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R := Mod.comap φ
  have : Epi φ := epi_coefficientMap_reduction l E T (max n m)
  have : F.Full := Mod.full_comap_of_epi φ
  let Vn : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) B ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R :=
    Mod.comap (coefficientMap (reduction l E n) T)
  let Vm : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) C ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R :=
    Mod.comap (coefficientMap (reduction l E m) T)
  let Gn : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) B ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) D :=
    Mod.comap (coefficientMap (finiteMap l E (max n m) n (le_max_left _ _)) T)
  let Gm : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) C ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) D :=
    Mod.comap (coefficientMap (finiteMap l E (max n m) m (le_max_right _ _)) T)
  let en : Vn ≅ Gn ⋙ F :=
    Mod.comapCongr (by rw [← reduction_comp l E (max n m) n (le_max_left _ _),
      coefficientMap_comp]) ≪≫ Mod.comapComp _ _
  let em : Vm ≅ Gm ⋙ F :=
    Mod.comapCongr (by rw [← reduction_comp l E (max n m) m (le_max_right _ _),
      coefficientMap_comp]) ≪≫ Mod.comapComp _ _
  let L := (restrict l E T n).obj K
  let Z := (scalar l E T m).obj L
  let enH (j : ℤ) : (DerivedCategory.homologyFunctor _ j).obj L ≅
      F.obj (commonInputHomology l E T n m K j) :=
    ((Vn.mapDerivedCategoryHomologyFunctorIso j).app K).symm ≪≫
      en.app ((DerivedCategory.homologyFunctor _ j).obj K)
  let emH (j : ℤ) : (DerivedCategory.homologyFunctor _ j).obj
      ((restrict l E T m).obj Z) ≅
      F.obj (commonReductionHomology l E T n m K j) :=
    ((Vm.mapDerivedCategoryHomologyFunctorIso j).app Z).symm ≪≫
      em.app ((DerivedCategory.homologyFunctor _ j).obj Z)
  obtain ⟨Δ, hΔ, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := reductionTriangle l E T m L
  let H (j : ℤ) := DerivedCategory.homologyFunctor
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) j
  let a₁ := (H q).mapIso e₁ ≪≫ enH q
  let a₂ := (H q).mapIso e₂ ≪≫ enH q
  let a₃ := (H q).mapIso e₃ ≪≫ emH q
  let a₄ := (H (q + 1)).mapIso e₁ ≪≫ enH (q + 1)
  let a₅ := (H (q + 1)).mapIso e₂ ≪≫ enH (q + 1)
  let f := F.preimage (a₁.inv ≫ (H q).map Δ.mor₁ ≫ a₂.hom)
  let a := F.preimage (a₂.inv ≫ (H q).map Δ.mor₂ ≫ a₃.hom)
  let b := F.preimage (a₃.inv ≫ DerivedCategory.HomologySequence.δ Δ q (q + 1) ≫ a₄.hom)
  let g := F.preimage (a₄.inv ≫ (H (q + 1)).map Δ.mor₁ ≫ a₅.hom)
  obtain ⟨w₁, h₁⟩ := liftExactPair F a₁ a₂ a₃ _ _ _
    (DerivedCategory.HomologySequence.exact₂ Δ hΔ q) f a
    (F.map_preimage _) (F.map_preimage _)
  obtain ⟨w₂, h₂⟩ := liftExactPair F a₂ a₃ a₄ _ _ _
    (DerivedCategory.HomologySequence.exact₃ Δ hΔ q (q + 1)) a b
    (F.map_preimage _) (F.map_preimage _)
  obtain ⟨w₃, h₃⟩ := liftExactPair F a₃ a₄ a₅ _ _ _
    (DerivedCategory.HomologySequence.exact₁ Δ hΔ q (q + 1)) b g
    (F.map_preimage _) (F.map_preimage _)
  obtain ⟨i, p, w, hS⟩ := fiveTermShortExact f a b g w₁ w₂ w₃ h₁ h₂ h₃
  exact ⟨f, g, i, p, w, hS⟩

end AlgebraicGeometry.ProEtale.IntegralQuotient
