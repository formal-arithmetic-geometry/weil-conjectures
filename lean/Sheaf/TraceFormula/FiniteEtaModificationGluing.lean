/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.TraceFormula.SchematicallyDenseOpen
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite-base reconciliation of local reduced generic modifications

Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4 and
Theorem 3.5.5, Step 1 (blueprint: lem-trf-finite-eta-modification-gluing).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The open of `H i` corresponding to the overlap with `H j`.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
def etaModificationOverlapOpen {Z : Scheme.{u}} {n : ℕ}
    (H : Fin n → Z.Opens) (i j : Fin n) : (H i).toScheme.Opens :=
  (opensRestrict (H i)).symm ⟨(H i) ⊓ (H j), inf_le_left⟩

/-- The restriction of a local modification to an overlap.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
noncomputable def etaModificationOverlapRestriction {Z : Scheme.{u}} {n : ℕ}
    (H : Fin n → Z.Opens) (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme) (i j : Fin n) :
    (q i ⁻¹ᵁ etaModificationOverlapOpen H i j).toScheme ⟶
      (etaModificationOverlapOpen H i j).toScheme :=
  (q i).resLE (etaModificationOverlapOpen H i j)
      (q i ⁻¹ᵁ etaModificationOverlapOpen H i j) le_rfl

/-- The restriction of a local modification to an overlap, viewed over `S`.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
noncomputable def etaModificationOverlapMap {S Z : Scheme.{u}} {n : ℕ}
    (f : Z ⟶ S) (H : Fin n → Z.Opens) (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme) (i j : Fin n) :
    (q i ⁻¹ᵁ etaModificationOverlapOpen H i j).toScheme ⟶ S :=
  etaModificationOverlapRestriction H Y q i j ≫
    (etaModificationOverlapOpen H i j).ι ≫ (H i).ι ≫ f

/-- The restriction of a local modification to an overlap, viewed over `Z`.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
noncomputable def etaModificationOverlapMapToZ {Z : Scheme.{u}} {n : ℕ}
    (H : Fin n → Z.Opens) (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme) (i j : Fin n) :
    (q i ⁻¹ᵁ etaModificationOverlapOpen H i j).toScheme ⟶ Z :=
  etaModificationOverlapRestriction H Y q i j ≫
    (etaModificationOverlapOpen H i j).ι ≫ (H i).ι

/-- The open immersion of an overlap chart into the base-changed chart.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
noncomputable def etaModificationOverlapInclusion {S S' Z : Scheme.{u}} {n : ℕ}
    (f : Z ⟶ S) (H : Fin n → Z.Opens) (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme) (h : S' ⟶ S) (i j : Fin n) :
    pullback (etaModificationOverlapMap f H Y q i j) h ⟶
      pullback (q i ≫ (H i).ι ≫ f) h :=
  pullback.map (etaModificationOverlapMap f H Y q i j)
    h (q i ≫ (H i).ι ≫ f) h
    ((q i ⁻¹ᵁ etaModificationOverlapOpen H i j).ι) (𝟙 _)
    (𝟙 _)
    (by simp [etaModificationOverlapMap, etaModificationOverlapRestriction])
    (by simp)

/-- The categorical factorization and cocycle conditions for overlap maps.
Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4
(blueprint: lem-trf-finite-eta-modification-gluing). -/
def etaModificationOverlapCocycle {S S' Z : Scheme.{u}} {n : ℕ}
    (f : Z ⟶ S) (H : Fin n → Z.Opens) (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme) (h : S' ⟶ S)
    (φ : ∀ i j,
      pullback (etaModificationOverlapMap f H Y q i j) h ≅
      pullback (etaModificationOverlapMap f H Y q j i) h) : Prop :=
  ∃ (τ : ∀ i j k,
      pullback (etaModificationOverlapInclusion f H Y q h i j)
          (etaModificationOverlapInclusion f H Y q h i k) ⟶
        pullback (etaModificationOverlapInclusion f H Y q h j k)
          (etaModificationOverlapInclusion f H Y q h j i)),
    (∀ i j k,
      τ i j k ≫ pullback.snd
          (etaModificationOverlapInclusion f H Y q h j k)
          (etaModificationOverlapInclusion f H Y q h j i) =
        pullback.fst (etaModificationOverlapInclusion f H Y q h i j)
            (etaModificationOverlapInclusion f H Y q h i k) ≫
          (φ i j).hom) ∧
    (∀ i j k,
      τ i j k ≫ τ j k i ≫ τ k i j = 𝟙 _)

/-- Finite-base reconciliation of local reduced generic modifications.

Source: Temkin, *Stable modification of relative curves*, Corollary 3.5.4 and
Theorem 3.5.5, Step 1 (blueprint: lem-trf-finite-eta-modification-gluing).

Proof, following the node step by step:
1. If `n = 0` then `Z` is empty; take `S' = S`, `h = 𝟙 S` and `Y'` empty.
2. All `H i`, their pairwise and triple overlaps and their inverse images in the `Y i`
   are quasi-compact and quasi-separated, and the restrictions to `S` are flat and of
   finite presentation, also after base change (`lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-flat-morphism-base-change`).
3. Spread the inverses of the generic isomorphisms `(q i)_η` to one quasi-compact open
   `V ∋ η` over which every `q i` is an isomorphism (Limits 01ZM (2),(3) via
   `thm-pd-spreading-out` and the affine-neighbourhood limit of `η`).
4. Density: for a flat scheme over an integral base, restriction of sections to the
   generic fibre, or to the inverse image of any open containing `η`, is injective
   (`lem-sc-flat-invertible-sections-torsion-free`).
5. Let `ν : N ⟶ S` be the normalization in `k(S)` (`lem-weil-pbc-relative-normalization`,
   `lem-sbc-integral-closure-finite-normal-product`): `N` is integral, normal, qcqs, and
   `N_η = η`.
6. Write `N` as the limit of the finite integral birational `T_λ = Spec_S 𝒜_λ` over the
   finite quasi-coherent subalgebras `𝒜_λ ⊆ ν_* 𝒪_N` (Properties 0817(1), Limits 01YW,
   01YX).
7. Over `N`, fix `i, j`; the base changes `F_i`, `F_j` of the overlap charts are flat,
   finitely presented with reduced geometric fibres over the normal `N`, so every finite
   `η`-modification of either is an isomorphism (`lem-trf-geometrically-reduced-eta-normal`).
   Form the scheme-theoretic image `G` of the graph of the identification over `V_N`.
8. Both projections of `G` are finite, isomorphisms over a schematically dense open
   (Tags 0CNG, 01R8), hence finite `η`-modifications and so isomorphisms; put
   `φ_ij = p_j ∘ p_i⁻¹`.
9. Overlap maps over an integral base are unique, by injectivity into the generic fibre
   (step 4) and `lem-weil-pbc-scheme-morphism-gluing`; hence `φ_ii = id`,
   `φ_ji = φ_ij⁻¹` and the cocycle condition.
10. Descend the finitely many `φ_ij`, their inverses and the needed equalities to one
    `S' = T_λ` (`thm-pd-spreading-out` (2),(3)); `h` is finite, proper
    (`lem-weil-pbc-finite-proper`), birational and surjective, and step 9 gives the
    cocycle and the identity over `h⁻¹ V`.
11. Glue the base-changed `Y i` along the `φ_ij` (`lem-weil-pbc-glue-schemes`) and the
    maps to `Z ×_S S'`; `q` is finite since finiteness is local on the target
    (`lem-weil-pbc-finite-local-on-target`), and an isomorphism generically.
12. `Y ⟶ S'` is flat and locally of finite presentation chartwise, quasi-compact and
    quasi-separated since `q` is finite and `Z ×_S S'` is qcqs, and has reduced
    geometric fibres (`lem-trf-geometric-reduced-fibre-locus-base-change`,
    `lem-trf-reduced-scheme-open-cover`).
13. Put `U = Z ×_S h⁻¹ V`; `q` is an isomorphism over `U`, and `U`, `q⁻¹ U` are
    schematically dense by step 4 (`def-trf-schematically-dense-open`).
-/
theorem finite_eta_modification_gluing
    {S Z : Scheme.{u}} [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (f : Z ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (H : Fin n → Z.Opens)
    (hHqc : ∀ i, QuasiCompact (H i).ι)
    (hHcover : ⨆ i, H i = ⊤)
    (Y : Fin n → Scheme)
    (q : ∀ i, Y i ⟶ (H i).toScheme)
    (hqfin : ∀ i, IsFinite (q i))
    (hYflat : ∀ i, Flat (q i ≫ (H i).ι ≫ f))
    (hYlfp : ∀ i, LocallyOfFinitePresentation (q i ≫ (H i).ι ≫ f))
    (hYred : ∀ i, GeometricallyReduced (q i ≫ (H i).ι ≫ f))
    (hqη : ∀ i, IsIso (pullback.map
      (q i ≫ (H i).ι ≫ f) (S.fromSpecResidueField η)
      ((H i).ι ≫ f) (S.fromSpecResidueField η)
      (q i) (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    ∃ (S' : Scheme) (h : S' ⟶ S),
      IsIntegral S' ∧ IsFinite h ∧ IsProper h ∧ Surjective h ∧
      IsIso (h.fiberToSpecResidueField η) ∧
      ∃ (η' : S') (hη' : h η' = η),
        ∃ (Y' : Scheme) (q' : Y' ⟶ pullback f h)
          (p' : Y' ⟶ S') (hp' : p' = q' ≫ pullback.snd f h),
          IsFinite q' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧
          QuasiCompact p' ∧ QuasiSeparated p' ∧ GeometricallyReduced p' ∧
          IsIso (pullback.map p' (S'.fromSpecResidueField η')
            (pullback.snd f h) (S'.fromSpecResidueField η')
            q' (𝟙 _) (𝟙 _) (by simp [hp']) (by simp)) ∧
          ∃ (U : (pullback f h).Opens),
            SchematicallyDenseOpen U ∧
            SchematicallyDenseOpen (q' ⁻¹ᵁ U) ∧
            IsIso (q'.resLE U (q' ⁻¹ᵁ U) le_rfl) ∧
            ∃ (φ : ∀ i j,
                pullback (etaModificationOverlapMap f H Y q i j) h ≅
                pullback (etaModificationOverlapMap f H Y q j i) h),
              (∀ i j,
                (φ i j).hom ≫ pullback.snd
                  (etaModificationOverlapMap f H Y q j i) h =
                pullback.snd (etaModificationOverlapMap f H Y q i j) h) ∧
              (∀ i j,
                (φ i j).hom ≫ pullback.fst
                  (etaModificationOverlapMap f H Y q j i) h ≫
                  etaModificationOverlapMapToZ H Y q j i =
                pullback.fst (etaModificationOverlapMap f H Y q i j) h ≫
                  etaModificationOverlapMapToZ H Y q i j) ∧
              (∀ i, φ i i = Iso.refl _) ∧
              (∀ i j, φ j i = (φ i j).symm) ∧
              (∀ i j (ψ :
                pullback (etaModificationOverlapMap f H Y q i j) h ≅
                pullback (etaModificationOverlapMap f H Y q j i) h),
                ψ.hom ≫ pullback.snd
                    (etaModificationOverlapMap f H Y q j i) h =
                  pullback.snd (etaModificationOverlapMap f H Y q i j) h ∧
                ψ.hom ≫ pullback.fst
                    (etaModificationOverlapMap f H Y q j i) h ≫
                    etaModificationOverlapMapToZ H Y q j i =
                  pullback.fst (etaModificationOverlapMap f H Y q i j) h ≫
                    etaModificationOverlapMapToZ H Y q i j →
                ψ = φ i j) ∧
              etaModificationOverlapCocycle f H Y q h φ ∧
              ∃ (ιY : ∀ i, pullback (q i ≫ (H i).ι ≫ f) h ⟶ Y'),
                (∀ i, IsOpenImmersion (ιY i)) ∧
                (∀ y : Y', ∃ i x, ιY i x = y) ∧
                (∀ i, ιY i ≫ q' = pullback.map
                  (q i ≫ (H i).ι ≫ f) h f h
                  (q i ≫ (H i).ι) (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  sorry

end AlgebraicGeometry
