/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MeromorphicDenominatorIdeal
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.RingTheory.Lasker
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.AlgebraicGeometry.HilbertDenominatorMaps
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.NowhereDenseDimensionDrop
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian

/-! # Regular-section exact sequences give lower-dimensional differences

Source: Stacks Project, Divisors, Tag 02P2 (Lemma 31.25.5, label
`divisors-lemma-make-maps-regular-section`); Varieties, Tag 0BEM (blueprint:
lem-sc-hilbert-difference).
-/

@[expose] public section

universe u

open scoped AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem hilbert_coherent_fp {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (hc : RingedSpace.IsCoherent X.toRingedSpace F) :
    F.IsFinitePresentation := by
  have hq := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hc
  have hfp (U : X.affineOpens) : (F.over U.1).IsFinitePresentation := by
    have := IsLocallyNoetherian.component_noetherian U
    have := coherent_affine_sections_finite X F hc U.1 U.2
    exact (((quasicoherent_finite_type_affine.{u, u} X).2 F hq.1).1 U.1 U.2).2.mpr
      (Module.finitePresentation_of_finite Γ(X, U.1) Γ(F, U.1))
  exact SheafOfModules.IsFinitePresentation.of_coversTop F (fun U : X.affineOpens ↦ U.1)
    ((Opens.coversTop_iff X _).mpr (iSup_affineOpens_eq_top X))

private theorem hilbert_twist_succ {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (n : ℤ) :
    Nonempty ((L ⊗ (if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat)) ≅
      (if 0 ≤ n + 1 then L.tensorPow (n + 1).toNat
        else L.dual.tensorPow (-(n + 1)).toNat)) := by
  split_ifs with hn hn1 hn1
  · exact ⟨eqToIso (by rw [show (n + 1).toNat = n.toNat + 1 by omega]; rfl)⟩
  · omega
  · have hn' : n = -1 := by omega
    subst n
    refine ⟨(Iso.refl L ⊗ᵢ (ρ_ L.dual)) ≪≫
      (nonempty_tensorObj_dual_iso_unit L).some⟩
  · have hm : (-n).toNat = (-(n + 1)).toNat + 1 := by omega
    rw [hm, tensorPow_succ]
    exact ⟨(α_ _ _ _).symm ≪≫
      ((nonempty_tensorObj_dual_iso_unit L).some ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem hilbert_euler_mono_tensor
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [IsLocallyNoetherian X] {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) N]
    (f : M ⟶ N) [Mono f] (P : X.Modules) [P.IsInvertible] :
    eulerChar k (tensorObj N P) =
      eulerChar k (tensorObj M P) + eulerChar k (tensorObj (cokernel f) P) := by
  have h := eulerChar_tensorObj_sub_eulerChar_tensorObj_eq k f P
  have hz : IsZero (kernel f ⊗ P) :=
    (tensorRight P).map_isZero (isZero_kernel_of_mono f)
  rw [eulerChar_eq_zero_of_isZero k hz, sub_zero] at h
  change eulerChar k (tensorObj N P) - eulerChar k (tensorObj M P) =
    eulerChar k (tensorObj (cokernel f) P) at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Regular meromorphic sections give coherent lower-dimensional cokernels and the
forward-difference identity for Euler characteristics.
Source: Stacks Project, Divisors, Tag 02P2; Varieties, Tag 0BEM
(blueprint: lem-sc-hilbert-difference).

Proof:
1. Trivialize L on affine opens and write s = a/b with a and b non-zero-divisors.
   The denominator ideal has sections I = {x | x(a/b) lies in A}. Since F has full
   support and no embedded associated points, a and b are also regular on its finite
   section module M. The affine calculation constructs the injective maps IM to M
   and IM to M tensor L. They agree on overlaps and glue
   [lem-sc-hilbert-affine-denominator-module,
   lem-sc-hilbert-denominator-ideal-nowhere-dense].
2. The denominator ideal is quasi-coherent and finitely generated on Noetherian affines,
   hence coherent [pqf-lem-coherent-ft-locnoeth]. Its product with F is the image of
   multiplication and has sections IM
   [lem-weil-pbc-ideal-times-quasi-coherent-affine-sections]. This submodule of F and
   the two cokernels are coherent by kernel/cokernel closure; F tensor L is coherent
   on the trivializing opens [lem-weil-pbc-coherent-kernel-cokernel-locnoeth].
3. The two cokernels are annihilated locally by I and s(I), respectively. Their supports
   lie in closed nowhere-dense subsets
   [lem-sc-hilbert-denominator-ideal-nowhere-dense]. Nonemptiness and finite dimension
   give strict dimension drop [lem-sc-hilbert-nowhere-dense-dimension-drop].
4. Tensor the two short exact sequences by L^n, which is exact for every integer n
   [lem-sc-ext-tensor-exact]. Apply Euler-characteristic additivity and cancel the common
   term IF tensor L^n [lem-pc-euler-additive], giving the displayed signs.

The first map uses the recorded ideal-module product. The second map is characterized
by factoring the tensor of the denominator map through the image of multiplication.
That image factor is an epimorphism, so the factorization determines the map uniquely.
The cokernels below are those of IF to F and IF to F tensor L, not those of I itself.
The denominator ideal I is the pullback of s along L to K_X(L), with projections to O_X
and L, written out explicitly. Integer twists L^n use `tensorPow` for nonnegative n and
powers of `dual` for negative n, inline as in lem-sc-snapper-numerical-polynomial.
-/
theorem hilbert_difference {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [Nonempty X]
    [IsLocallyNoetherian X] (d : ℕ)
    (hDim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (F : X.Modules)
    (hFcoh : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hFsupport : ∀ x : X, ¬ Subsingleton ((presheaf F).stalk x))
    (hFnoEmbedded : ∀ (U : X.Opens) (_ : IsAffineOpen U)
      (p : Ideal (Γ(X, U))),
      p ∈ associatedPrimes (Γ(X, U)) (Γ(F, U)) →
        Minimal (fun q : Ideal (Γ(X, U)) =>
          q ∈ associatedPrimes (Γ(X, U)) (Γ(F, U))) p)
    (L : X.Modules) [L.IsInvertible]
    (s : unit X ⟶ meromorphicModule X L)
    (hs : Mono (meromorphicSectionMap X L s)) :
    ∃ jF : idealModuleProduct (pullback.fst s (toMeromorphicModule X L)) F ⟶ tensorObj F L,
      factorThruImage ((pullback.fst s (toMeromorphicModule X L)) ▷ F ≫ (λ_ F).hom) ≫ jF =
        (pullback.snd s (toMeromorphicModule X L)) ▷ F ≫ (β_ L F).hom ∧
      (Mono (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F) ∧ Mono jF) ∧
      (AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace
          (cokernel (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F)) ∧
        AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace (cokernel jF)) ∧
      topologicalKrullDim {x : X |
          ¬ Subsingleton ((presheaf (cokernel (idealModuleProductι
            (pullback.fst s (toMeromorphicModule X L)) F) : X.Modules)).stalk x)} <
        topologicalKrullDim X ∧
      topologicalKrullDim {x : X | ¬ Subsingleton ((presheaf (cokernel jF : X.Modules)).stalk x)} <
        topologicalKrullDim X ∧
      ∀ (n : ℤ),
        eulerChar k (tensorObj F (if 0 ≤ n + 1 then L.tensorPow (n + 1).toNat
            else L.dual.tensorPow (-(n + 1)).toNat)) -
            eulerChar k (tensorObj F (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) =
          eulerChar k (tensorObj (cokernel jF) (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) -
            eulerChar k (tensorObj
              (cokernel (idealModuleProductι (pullback.fst s (toMeromorphicModule X L)) F))
              (if 0 ≤ n then L.tensorPow n.toNat
            else L.dual.tensorPow (-n).toNat)) := by
  obtain ⟨jF, hjF, hmjF, hQi, hQj⟩ :=
    hilbert_denominator_maps F hFcoh hFsupport hFnoEmbedded L s hs
  have hden := meromorphic_denominator_ideal_nowhere_dense X L s hs
  dsimp only at hden
  obtain ⟨_, _, hIqc, hmi, _, ⟨Zi, hZi, hni, hvi⟩, ⟨Zj, hZj, hnj, hvj⟩⟩ := hden
  let i := pullback.fst s (toMeromorphicModule X L)
  let A := idealModuleProduct i F
  let a := idealModuleProductι i F
  have : Mono a := by dsimp [a, idealModuleProductι]; infer_instance
  have : Mono jF := hmjF
  have : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hFcoh).1
  have : F.IsFinitePresentation := hilbert_coherent_fp F hFcoh
  have : (Limits.pullback s (toMeromorphicModule X L)).IsQuasicoherent := hIqc
  have : (tensorObj (Limits.pullback s (toMeromorphicModule X L)) F).IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections _ _).1
  have : A.IsQuasicoherent := by
    have := isQuasicoherent_cokernel (i ▷ F ≫ (λ_ F).hom)
    have := isQuasicoherent_kernel (cokernel.π (i ▷ F ≫ (λ_ F).hom))
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage (i ▷ F ≫ (λ_ F).hom)) inferInstance
  have hA := (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F A a
    hFcoh inferInstance inferInstance
  have : A.IsFinitePresentation := hilbert_coherent_fp A hA.1
  have : (F ⊗ L).IsQuasicoherent := isQuasicoherent_tensorObj F L
  have : (F ⊗ L).IsFinitePresentation := isFinitePresentation_tensorObj F L
  have hFL : RingedSpace.IsCoherent X.toRingedSpace (tensorObj F L) :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
      ⟨inferInstance, inferInstance⟩
  have hcj := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1
    A (F ⊗ L) hA.1 hFL).1 jF |>.2
  have dim_support (M : X.Modules) (Z : Set X) (hz : IsClosed Z) (hn : IsNowhereDense Z)
      (hv : ∀ x : X, x ∉ Z → Subsingleton ((presheaf M).stalk x)) :
      topologicalKrullDim {x : X | ¬ Subsingleton ((presheaf M).stalk x)} <
        topologicalKrullDim X := by
    let E := {x : X | ¬ Subsingleton ((presheaf M).stalk x)}
    have hsub : E ⊆ Z := fun x hx ↦ by_contra fun h ↦ hx (hv x h)
    have he : Topology.IsInducing (Set.inclusion hsub) :=
      Topology.IsInducing.subtypeVal.of_comp_iff.mp
        (show Topology.IsInducing ((Subtype.val : Z → X) ∘ Set.inclusion hsub) from
          Topology.IsInducing.subtypeVal)
    exact he.topologicalKrullDim_le.trans_lt
      (hDim ▸ X.topologicalKrullDim_lt_of_isNowhereDense d hDim Z hz hn)
  refine ⟨jF, hjF, ⟨inferInstance, hmjF⟩, ⟨hA.2, hcj⟩,
    dim_support _ Zi hZi hni (fun x hx ↦ hQi x (hvi x hx)),
    dim_support _ Zj hZj hnj (fun x hx ↦ hQj x (hvj x hx)), ?_⟩
  intro n
  let P := if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat
  have : P.IsInvertible := by dsimp [P]; split_ifs <;> infer_instance
  have e1 := hilbert_euler_mono_tensor (k := k) a P
  have e2 := hilbert_euler_mono_tensor (k := k) jF P
  have e3 := eulerChar_congr k
    ((α_ F L P) ≪≫ (Iso.refl F ⊗ᵢ (hilbert_twist_succ L n).some))
  dsimp only [tensorObj] at e1 e2 e3 ⊢
  change _ = _ at e3
  dsimp only [P, a, i] at e1 e2 e3
  omega

end AlgebraicGeometry.Scheme.Modules
