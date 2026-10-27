/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.Blowup.Principalization
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.QuotSMulTop
import Sheaf.AlgebraicGeometry.UniversalExactAffinePowerReduction
import Sheaf.AlgebraicGeometry.OpenSupportQuotientLocalExact

/-!
# Strict transforms of universally exact sequences

Source: Stacks Project, Divisors, Tag 080W,
`lemma-strict-transform-universally-injective`
(blueprint: lem-trf-strict-transform-universal-exact).

The induced maps are constructed from the natural open-restriction map by taking
kernels and then cokernels, using the existing strict-transform objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical map on module strict transforms: tensor-pull back the given map,
map its supported-section kernel by naturality of open restriction, and pass to the
quotient by this kernel. All objects are those of `moduleStrictTransform`.
Source: Stacks Project, Tags 080D (1) and 080W
(blueprint: lem-trf-strict-transform-universal-exact). -/
noncomputable def moduleStrictTransformMap {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (a : F ⟶ G) :
    moduleStrictTransform f I F ⟶ moduleStrictTransform f I G :=
  cokernel.map (kernel.ι (moduleStrictTransformRestriction f I F))
    (kernel.ι (moduleStrictTransformRestriction f I G))
    (kernel.map (moduleStrictTransformRestriction f I F)
      (moduleStrictTransformRestriction f I G)
      ((tensorPullback (pullback.fst f I.blowupMap)).map a)
      (((restrictFunctor (moduleStrictTransformOpen f I).ι) ⋙
        pushforward (moduleStrictTransformOpen f I).ι).map
          ((tensorPullback (pullback.fst f I.blowupMap)).map a))
      ((restrictAdjunction (moduleStrictTransformOpen f I).ι).unit.naturality
        ((tensorPullback (pullback.fst f I.blowupMap)).map a)).symm)
    ((tensorPullback (pullback.fst f I.blowupMap)).map a)
    (kernel.lift_ι _ _ _).symm

private theorem quotSMulTop_map_injective_of_divisibility
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (r : R) (i : M →ₗ[R] N)
    (hdiv : ∀ m : M, (∃ x : N, r • x = i m) → ∃ y : M, r • y = m) :
    Function.Injective (QuotSMulTop.map r i) := by
  apply (injective_iff_map_eq_zero (QuotSMulTop.map r i)).mpr
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (r • (⊤ : Submodule R M)) x
  change (Submodule.Quotient.mk (i m) : QuotSMulTop r N) = 0 at hx
  change (Submodule.Quotient.mk m : QuotSMulTop r M) = 0
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨n, -, hn⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists (i m) r (⊤ : Submodule R N)).mp hx
  obtain ⟨m', hm'⟩ := hdiv m ⟨n, hn⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.mem_smul_pointwise_iff_exists m r (⊤ : Submodule R M)).mpr
      ⟨m', Submodule.mem_top, hm'⟩)

private theorem exists_principal_affine_chart {B Y : Scheme.{u}} (q : Y ⟶ B)
    (J : B.IdealSheafData) (hJ : J.IsLocallyPrincipal) (y : Y) :
    ∃ (A R : CommRingCat.{u}) (ρ : A →+* R) (v : Spec A ⟶ B)
      (_ : IsOpenImmersion v) (z : Spec R ⟶ Y) (_ : IsOpenImmersion z) (a : A),
      y ∈ Set.range z ∧ z ≫ q = Spec.map (CommRingCat.ofHom ρ) ≫ v ∧
      z ⁻¹ᵁ (q ⁻¹ᵁ J.support.compl) = PrimeSpectrum.basicOpen (ρ a) := by
  obtain ⟨V, hyV, ⟨a, ha⟩⟩ := hJ (q y)
  have hVaff : IsAffineOpen V.1 := V.2
  obtain ⟨Z, hZ, hyZ, hZV⟩ :=
    exists_isAffineOpen_mem_and_subset (U := q ⁻¹ᵁ V.1) (x := y) hyV
  let ρ := (q.appLE V.1 Z hZV).hom
  have hcomp : hZ.fromSpec ≫ q = Spec.map (CommRingCat.ofHom ρ) ≫ hVaff.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec q hVaff hZ hZV).symm
  have hV : hVaff.fromSpec ⁻¹ᵁ J.support.compl = PrimeSpectrum.basicOpen a := by
    apply TopologicalSpace.Opens.ext
    ext x
    have hxV : hVaff.fromSpec x ∈ V.1 := by
      change hVaff.fromSpec x ∈ (V.1 : Set B)
      exact hVaff.range_fromSpec ▸ (Set.mem_range_self x)
    change hVaff.fromSpec x ∉ J.support ↔ x ∈ PrimeSpectrum.basicOpen a
    rw [J.mem_support_iff_of_mem hxV, ha, B.zeroLocus_span, B.zeroLocus_singleton]
    simp only [Set.mem_compl_iff, not_not]
    change x ∈ hVaff.fromSpec ⁻¹ᵁ B.basicOpen a ↔ x ∈ PrimeSpectrum.basicOpen a
    rw [hVaff.fromSpec_preimage_basicOpen]
  refine ⟨Γ(B, V.1), Γ(Y, Z), ρ, hVaff.fromSpec, inferInstance,
    hZ.fromSpec, inferInstance, a, ?_, hcomp, ?_⟩
  · rwa [hZ.range_fromSpec]
  · rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hV]
    rfl

/-- Strict transforms preserve a short exact sequence which remains short exact after
all scheme base changes to the base. The centre is a finite-type quasi-coherent ideal,
and every pullback in the hypothesis is the tensor pullback of module sheaves.
Source: Stacks Project, Tag 080W
(blueprint: lem-trf-strict-transform-universal-exact).

Proof plan:
1. Pull back to the blowup. The universal hypothesis gives a short exact sequence;
   tensor pullback preserves quasi-coherence (`lem-pc-ringed-space-tensor-pullback-qcoh`).
   Principalization (`thm-nagata-blowup-principalizes-center`) and the affine-open basis
   (`lem-weil-pbc-affine-opens-basis`) reduce to affine charts where the exceptional
   ideal is generated by one element a. Use the tilde/global-section adjunction
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`) to write the modules as tilde N_i.
2. The affine kernel and cokernel descriptions
   (`lem-weil-pbc-quasi-coherent-module-kernel` and
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`) give a short exact module
   sequence N_1 -> N_2 -> N_3 with maps i and j.
3. Base change to A/(a^n) for every n. Fibre-product pasting and affine spectra,
   open-immersion base change, composition of tensor pullbacks and tilde base change
   (`def-pc-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`,
   `lem-weil-pbc-open-immersion-base-change`, `def-pc-module-pullback`,
   `lem-weil-pbc-tilde-pullback-base-change`) show that N_1/a^n N_1 injects into
   N_2/a^n N_2, using the affine tilde/global-section adjunction.
4. The supported-section kernel on each chart is tilde of the a-power torsion T_i.
   Check this on principal opens by the localization fraction criterion
   (`lem-weil-pbc-spec-module-tilde-sections`, `def-weil-pbc-module-localization-away`,
   `def-nagata-power-torsion`, `lemma-nagata-power-torsion-submodule`,
   `lemma-nagata-power-torsion-kernel-localization`). Thus the existing strict
   transforms are tilde (N_i/T_i), with the induced quotient maps.
5. The quotient map induced by i is injective since i is injective; the quotient
   map induced by j is surjective since j is surjective. Their composite is zero.
6. If j(x) is torsion, choose n with a^n j(x)=0, so i(y)=a^n x. Injectivity modulo
   a^n gives y=a^n z. Then a^n(x-i(z))=0 and [x]=[i(z)], proving middle exactness.
   No non-zero-divisor hypothesis on the chart ring or its modules is required.
7. Sheafify: tilde preserves finite limits (`lem-sc-tilde-preserves-finite-limits`)
   and colimits (the affine tilde/global-section adjunction). The exact sequences
   on the affine cover glue to the stated short exact sequence of strict transforms. -/
theorem moduleStrictTransform_shortExact_of_universallyShortExact
    {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact)
    (hbase : ∀ (T : Scheme.{u}) (t : T ⟶ S),
      ∃ w : (tensorPullback (pullback.fst f t)).map C.f ≫
          (tensorPullback (pullback.fst f t)).map C.g = 0,
        (ShortComplex.mk ((tensorPullback (pullback.fst f t)).map C.f)
          ((tensorPullback (pullback.fst f t)).map C.g) w).ShortExact) :
    ∃ w : moduleStrictTransformMap f I C.f ≫ moduleStrictTransformMap f I C.g = 0,
      (ShortComplex.mk (moduleStrictTransformMap f I C.f)
        (moduleStrictTransformMap f I C.g) w).ShortExact := by
  obtain ⟨w, -⟩ := hbase I.blowup I.blowupMap
  let H := ShortComplex.mk
    ((tensorPullback (pullback.fst f I.blowupMap)).map C.f)
    ((tensorPullback (pullback.fst f I.blowupMap)).map C.g) w
  change ∃ w : openSupportQuotientMap (moduleStrictTransformOpen f I) H.f ≫
      openSupportQuotientMap (moduleStrictTransformOpen f I) H.g = 0,
    (ShortComplex.mk (openSupportQuotientMap (moduleStrictTransformOpen f I) H.f)
      (openSupportQuotientMap (moduleStrictTransformOpen f I) H.g) w).ShortExact
  apply openSupportQuotient_shortExact_of_affine
  intro y
  obtain ⟨A, R, ρ, v, hv, z, hz, a, hy, hzq, hzU⟩ :=
    exists_principal_affine_chart (pullback.snd f I.blowupMap)
      (I.comap I.blowupMap) I.isInvertible_comap_blowupMap.isLocallyPrincipal y
  let : Algebra A R := ρ.toAlgebra
  have hopen : (pullback.snd f I.blowupMap) ⁻¹ᵁ
      (I.comap I.blowupMap).support.compl = moduleStrictTransformOpen f I := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hchart := universalExact_affine_power_reduction f I.blowupMap C hC hbase
    A R v z hzq a
  obtain ⟨_, _, _, he₁, he₂, he₃, _, _, hi, hij, hj, hp⟩ := hchart
  refine ⟨R, z, hz, algebraMap A R a, hy, ?_, he₁, he₂, he₃, ?_⟩
  · rw [← hopen]
    exact hzU
  · have hpow : ∀ n : ℕ, Function.Injective
        (QuotSMulTop.map ((algebraMap A R a) ^ n)
          ((universalExactAffineSections f I.blowupMap R z).map C.f).hom) := by
      intro n
      have h := hp n
      repeat' rcases h with ⟨_, h⟩
      exact quotSMulTop_map_injective_of_divisibility _ _ h
    exact (principalSupportQuotient_exact (algebraMap A R a)
      ((universalExactAffineSections f I.blowupMap R z).map C.f)
      ((universalExactAffineSections f I.blowupMap R z).map C.g)
      hi hij hj hpow).2.2.2.2.2.2

end AlgebraicGeometry.Scheme.Modules
