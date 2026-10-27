module

public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.StrictTransformChart
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Supported-section kernels on blowup charts

Source: Stacks Project, Divisors, Tags 0804 and 080H, and Properties, Tag 07ZP
(blueprint: lem-trf-supported-kernel-blowup-charts).

The supported subsheaves are specified by their sections on every open, together
with their inclusions. Tensor factors are ordered with the coefficient ring first;
the symmetry of tensor products gives the order used in the source.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
namespace SupportedKernelBlowupCharts

/-- The ideal sheaf of the affine centre, using the existing affine ideal constructor.
Source: Stacks, Tag 0804 (blueprint: lem-trf-supported-kernel-blowup-charts). -/
noncomputable abbrev center {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec (.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- The standard generator chart, transported to the global blowup.
Source: Stacks, Tag 0804 (blueprint: lem-trf-supported-kernel-blowup-charts). -/
noncomputable def chart {A : Type u} [CommRing A] (I : Ideal A)
    (e : (center I).blowup ≅ AffineBlowup I) (a : A) (ha : a ∈ I) :
    Spec (.of (AffineBlowup.chartRing I a)) ⟶ (center I).blowup :=
  Spec.map (CommRingCat.ofHom (AffineBlowup.homogeneousAwayEquivChart I ha).toRingHom) ≫
    AffineBlowup.chart I (reesX I a ha) (reesX_mem I a ha) ≫ e.inv

/-- The actual torsion inclusion, followed by an identification of the ambient module.
Source: Stacks, Tag 07ZP (blueprint: lem-trf-supported-kernel-blowup-charts). -/
noncomputable def inclusion {C : Type u} [CommRing C] (N : ModuleCat.{u} C)
    (H : (Spec (.of C)).Modules) (e : tilde (R := .of C) N ≅ H) (t : C) :
    tilde (R := .of C) (ModuleCat.of C (Submodule.powTorsion C N t)) ⟶ H :=
  tilde.map (R := .of C) (ModuleCat.ofHom (Submodule.powTorsion C N t).subtype) ≫ e.hom

/-- Sectionwise equality with the supported kernel, retaining its inclusion.
This is an explicit way of asserting equality as subsheaves, on every open.
Source: Stacks, Tag 07ZP (blueprint: lem-trf-supported-kernel-blowup-charts). -/
def PresentsSupportedKernel {C : Type u} [CommRing C] (N : ModuleCat.{u} C)
    (H : (Spec (.of C)).Modules) (e : tilde (R := .of C) N ≅ H) (t : C) : Prop :=
  Mono (inclusion (C := C) N H e t) ∧
    ∀ (V : (Spec (.of C)).Opens) (s : H.val.obj (op V)),
      (H.val.map (homOfLE
        (inf_le_left : V ⊓ PrimeSpectrum.basicOpen t ≤ V)).op).hom s = 0 ↔
        ∃ z : (tilde (R := .of C)
            (ModuleCat.of C (Submodule.powTorsion C N t))).val.obj (op V),
          ((inclusion (C := C) N H e t).val.app (op V)).hom z = s

/-- Supported-section kernels on all standard affine base-change charts.
Source: Stacks, Tags 0804, 080H (affine reduction of clause (2)), and 07ZP
(blueprint: lem-trf-supported-kernel-blowup-charts).

Proof: The finite generator charts cover the blowup, by
prop-nagata-affine-blowup-chart-cover. Base change and intersection with affine
opens of X give an open cover of the fibre product; the affine fibre-product
formula identifies its rings with R tensor A[I/a]. The affine pullback formula
and the tilde-Gamma counit identify the pulled-back module with the associated
tensor module. Associativity and symmetry identify this module with M tensor_A B;
on pure tensors the map sends (r tensor b) tensor m to b tensor (r m).
In B each generator f_j equals a times f_j/a, so IB = (a), hence IC = (a).
The inverse images of Z and Z union V(x) are therefore V(a) and V(xa), using
primality for the union formula. Principal opens are retrocompact. Applying
lem-trf-supported-sections-quasi-coherent identifies the supported kernel sections
with elements killed by a power of a, respectively xa. The naturality of the
counit in lem-weil-pbc-affine-tilde-gamma-adjunction identifies their actual
inclusions with the tilde of the torsion submodule inclusions. This gives the
sectionwise image equalities on every open. No regularity or torsion-free
hypothesis is used. -/
theorem supported_kernel_blowup_charts
    {A : Type u} [CommRing A] (I : Ideal A) (r : ℕ) (g : Fin (r + 1) → A)
    (hg : Ideal.span (Set.range g) = I) (x : A)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : (center I).blowup ≅ AffineBlowup I,
      e.hom ≫ AffineBlowup.toSpec I = (center I).blowupMap ∧
      ∃ hgI : ∀ i, g i ∈ I,
        (∀ z : pullback (C := Scheme.{u}) f (center I).blowupMap,
          ∃ (i : Fin (r + 1)) (U : X.affineOpens),
            pullback.fst f (center I).blowupMap z ∈ U.1 ∧
            pullback.snd f (center I).blowupMap z ∈ Set.range (chart I e (g i) (hgI i))) ∧
        ∀ (i : Fin (r + 1)) (R : Type u) [CommRing R] [Algebra A R]
          (v : Spec (.of R) ⟶ X) [IsOpenImmersion v]
          (_hv : v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A R)))
          (M : ModuleCat.{u} R)
          (_eM : (Scheme.Modules.tensorPullback v).obj F ≅ tilde M),
          ∃ j : Spec (.of (AffineBlowup.BaseChangeChart R I (g i))) ⟶
              pullback (C := Scheme.{u}) f (center I).blowupMap,
            IsOpenImmersion j ∧
            j ≫ pullback.fst f (center I).blowupMap =
              Spec.map (CommRingCat.ofHom (algebraMap R
                (AffineBlowup.BaseChangeChart R I (g i)))) ≫ v ∧
            j ≫ pullback.snd f (center I).blowupMap =
              Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
                chart I e (g i) (hgI i) ∧
            Set.range j =
              (pullback.fst f (center I).blowupMap) ⁻¹' Set.range v ∩
              (pullback.snd f (center I).blowupMap) ⁻¹'
                Set.range (chart I e (g i) (hgI i)) ∧
            (j ≫ pullback.snd f (center I).blowupMap ≫ (center I).blowupMap) ⁻¹'
                PrimeSpectrum.zeroLocus (I : Set A) =
              PrimeSpectrum.zeroLocus
                ({algebraMap A (AffineBlowup.BaseChangeChart R I (g i)) (g i)} : Set _) ∧
            (j ≫ pullback.snd f (center I).blowupMap ≫ (center I).blowupMap) ⁻¹'
                (PrimeSpectrum.zeroLocus (I : Set A) ∪
                  PrimeSpectrum.zeroLocus ({x} : Set A)) =
              PrimeSpectrum.zeroLocus
                ({algebraMap A (AffineBlowup.BaseChangeChart R I (g i)) (x * g i)} : Set _) ∧
            ∃ E : tilde (ModuleCat.of (AffineBlowup.BaseChangeChart R I (g i))
                  (AffineBlowup.BaseChangeChart R I (g i) ⊗[R] M)) ≅
                (Scheme.Modules.tensorPullback j).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (center I).blowupMap)).obj F),
              PresentsSupportedKernel _ _ E
                (algebraMap A (AffineBlowup.BaseChangeChart R I (g i)) (g i)) ∧
              PresentsSupportedKernel _ _ E
                (algebraMap A (AffineBlowup.BaseChangeChart R I (g i)) (x * g i)) ∧
              ∃ α : (AffineBlowup.BaseChangeChart R I (g i) ⊗[R] M) ≃ₗ[A]
                  (AffineBlowup.chartRing I (g i) ⊗[A]
                    (ModuleCat.restrictScalars (algebraMap A R)).obj M),
                ∀ (s : R) (b : AffineBlowup.chartRing I (g i)) (m : M),
                  α ((s ⊗ₜ[A] b) ⊗ₜ[R] m) =
                    b ⊗ₜ[A]
                      (@id ((ModuleCat.restrictScalars (algebraMap A R)).obj M) (s • m)) := by
  sorry

end SupportedKernelBlowupCharts
end AlgebraicGeometry
