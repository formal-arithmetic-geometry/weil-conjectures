/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.VerdierDualFinite
import WeilConjectures.WeilSheaf.StalkRationalPoint

/-!
# Degreewise Poincaré duality for lisse Weil sheaves

Let `X₀` be a smooth separated `k₀`-scheme of finite type and pure dimension `d` and `F` a lisse
Weil sheaf on `X₀`, with coefficient dual `F^∨` and Tate twist `F^∨(d)`, the constant twist of
`F^∨` by `χ_ℓ(σ)ᵈ = q⁻ᵈ`. Poincaré duality with coefficients `F` says that the degreewise
pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
  (`thm-pod-degreewise-perfectness-over-a-field`, with the Frobenius invariance of
  `thm-pod-equivariance-of-the-twisted-pairing`).

## Implementation notes

The statement is existential, as for constant coefficients
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`): Weil
complexes have no derived tensor product, `Ra^!` or orientation yet, so the derived Poincaré
pairing of `def-pod-derived-poincare-pairing` cannot be written down. It is a node of the
Poincaré duality section, stated here with `sorry` in the form needed by smooth-proper purity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

private theorem exists_pairing_of_equiv_dual {K : Type*} [Field K]
    {M N : FrobeniusModule K} (e : N.Equiv M.dual) :
    ∃ P : M.carrier →ₗ[K] N.carrier →ₗ[K] K,
      P.IsPerfPair ∧ ∀ x y, P (M.frobenius x) (N.frobenius y) = P x y := by
  let E : N.carrier ≃ₗ[K] Module.Dual K M.carrier := e.toLinearEquiv
  refine ⟨E.toLinearMap.flip,
    (LinearMap.IsPerfPair.of_bijective _ E.bijective).flip, ?_⟩
  intro x y
  change E (N.frobenius y) (M.frobenius x) = E y x
  have he := e.map_frobenius y
  change E (N.frobenius y) =
    (E y) ∘ₗ M.frobenius.symm.toLinearMap at he
  rw [he]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

private theorem nonempty_dual_equiv {K : Type*} [Field K]
    {M N : FrobeniusModule K} (e : M.Equiv N) :
    Nonempty (N.dual.Equiv M.dual) := by
  refine ⟨⟨e.toLinearEquiv.dualMap, ?_⟩⟩
  intro f
  change Module.Dual K N.carrier at f
  apply LinearMap.ext
  intro x
  have he := e.map_frobenius (M.frobenius.symm x)
  rw [LinearEquiv.apply_symm_apply] at he
  change f (N.frobenius.symm (e.toLinearEquiv x)) =
    f (e.toLinearEquiv (M.frobenius.symm x))
  rw [he, LinearEquiv.symm_apply_apply]

namespace AlgebraicGeometry

private theorem globalSections_dual_equiv
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀)))
    (hG : G.IsLisse) : Nonempty ((G.dual hG).globalSections.Equiv G.globalSections.dual) := by
  have hy := Scheme.Hom.mem_finitePoints_of_comp_eq_id
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) (𝟙 _) (Category.id_comp _)
    (IsLocalRing.closedPoint k₀)
  let y : (Spec (CommRingCat.of k₀)).finitePoints := ⟨_, hy⟩
  have hdy : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 = 1 :=
    Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ (𝟙 _) (Category.id_comp _) _
  let s := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y
  have hs : s ≫ ((Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      1).hom = (specGeometricFrobenius k₀ ^ 1).hom ≫ s :=
    hdy ▸ Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ y
  have : IsIso s := by
    have : IsIso (pullback.snd (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
        (Scheme.specAlgebraicClosure k₀).hom) := by
      change IsIso (pullback.snd (𝟙 _) _)
      infer_instance
    have hs' : s ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have : IsIso (s ≫ pullback.snd _ _) := by rw [hs']; infer_instance
    exact IsIso.of_isIso_comp_right s (pullback.snd _ _)
  obtain ⟨e⟩ := G.nonempty_equiv_globalSections_stalkAt s hs
  obtain ⟨e'⟩ := (G.dual hG).nonempty_equiv_globalSections_stalkAt s hs
  let ed := WeilSheaf.stalkAtDualEquiv s 1 hs G hG
  obtain ⟨eg⟩ := nonempty_dual_equiv e
  exact ⟨e'.trans (ed.trans eg)⟩

open WeilComplex in
private theorem homology_verdierDual_equiv
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    [HasUpperShriek k₀ l (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))]
    (A : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) (i : ℤ) :
    Nonempty ((((verdierDual k₀ l _).obj (Opposite.op A)).cohomologyFrobeniusModule (-i)).Equiv
      (A.cohomologyFrobeniusModule i).dual) := by
  let B := A⟦i - 1⟧
  obtain ⟨e⟩ := nonempty_homologySheaf_neg_one_verdierDual_iso B
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated_verdierDual k₀ l
    (Spec (CommRingCat.of k₀))
  let es : (verdierDual k₀ l _).obj (Opposite.op B) ≅
      ((verdierDual k₀ l _).obj (Opposite.op A))⟦1 - i⟧ := by
    simpa only [neg_sub] using verdierDualShiftIso A (1 - i)
  let el : (homologySheaf (-1)).obj ((verdierDual k₀ l _).obj (Opposite.op B)) ≅
      (homologySheaf (-i)).obj ((verdierDual k₀ l _).obj (Opposite.op A)) :=
    (homologySheaf (-1)).mapIso es ≪≫
      homologySheafShiftIso _ (1 - i) (-1) (-i) (by lia)
  let eh : (homologySheaf 1).obj B ≅ (homologySheaf i).obj A :=
    homologySheafShiftIso A (i - 1) 1 i (by lia)
  let G := (homologySheaf i).obj A
  have hG : G.IsLisse := WeilSheaf.isLisse_of_isFinite_of_isReduced G
  let er : (homologySheaf 0).obj ((verdierDual k₀ l _).obj
      (Opposite.op (WeilSheaf.toComplex.obj ((homologySheaf 1).obj B)))) ≅
      (homologySheaf 0).obj ((verdierDual k₀ l _).obj
        (Opposite.op (WeilSheaf.toComplex.obj G))) :=
    (homologySheaf 0).mapIso
      ((verdierDual k₀ l _).mapIso (WeilSheaf.toComplex.mapIso eh.symm).op)
  obtain ⟨ed⟩ := nonempty_verdierDual_toComplex_iso_of_isFinite G
  obtain ⟨et⟩ := WeilSheaf.nonempty_dual_tensorObj_tateTwistSheaf_iso G hG 0
  let et' : (G.dual hG).tensorObj
      ((WeilSheaf.tateTwistSheaf k₀ l _ 0).tensorObj (WeilSheaf.adicConstant k₀ l _)
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l _ 0)) hG.dual ≅ G.dual hG :=
    et ≪≫ ObjectProperty.isoMk _
      ((G.dual hG).constantTwistObjIso _ ≪≫
        ProEtaleWeilSheaf.constantTwistCongrIso (zpow_zero _) _ ≪≫
        ProEtaleWeilSheaf.constantTwistOneObjIso _)
  let ep : (homologySheaf (-i)).obj ((verdierDual k₀ l _).obj (Opposite.op A)) ≅ G.dual hG :=
    el.symm ≪≫ e ≪≫ er ≪≫ (homologySheaf 0).mapIso
      (ed ≪≫ WeilSheaf.toComplex.mapIso et') ≪≫
      WeilSheaf.toComplexCompHomologySheafIso.app _
  obtain ⟨eg⟩ := globalSections_dual_equiv G hG
  exact ⟨(WeilSheaf.globalSectionsEquivOfIso ep).trans eg⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Degreewise Poincaré duality for a lisse Weil sheaf** (blueprint
`thm-pod-degreewise-perfectness-over-a-field` for `K = F` perfect over `ℚ̄_ℓ,X`, with the Frobenius
invariance `thm-pod-equivariance-of-the-twisted-pairing`): for `X₀` smooth, separated, of finite
type and pure dimension `d` over `k₀` and `F` a lisse Weil sheaf on `X₀`, the degreewise
Poincaré pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius. Here `F^∨(d)` is the constant twist of the coefficient
dual `F^∨` by `χ_ℓ(σ)ᵈ`. Properness is not needed. -/
theorem exists_isPerfPair_compactlySupportedCohomology_dual (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).carrier
          →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P ((F.compactlySupportedCohomology i).frobenius x)
        ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).frobenius y) =
          P x y := by
  let := WeilComplex.isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  let := WeilComplex.isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l)
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
  -- Verdier exchange identifies the dual of compact support with the shifted
  -- ordinary direct image of the twisted coefficient dual.
  obtain ⟨e⟩ := WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso
    (X ↘ Spec (CommRingCat.of k₀)) (toComplex.obj F)
  obtain ⟨es⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isLisse d F hF
  obtain ⟨et⟩ := nonempty_dual_tensorObj_tateTwistSheaf_iso F hF (d : ℤ)
  let G := (F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)
  let E : (WeilComplex.verdierDual k₀ l _).obj
      (Opposite.op ((WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F))) ≅
      ((WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj G))⟦(2 * d : ℤ)⟧ :=
    e ≪≫ (WeilComplex.derivedLowerStar _).mapIso
      (es ≪≫ (shiftFunctor _ (2 * d : ℤ)).mapIso
        (toComplex.mapIso (by simpa only [zpow_natCast] using et))) ≪≫
      ((WeilComplex.derivedLowerStar _).commShiftIso (2 * d : ℤ)).app _
  -- Take degree -i, whose shifted degree is j by i + j = 2d.
  let EH : (WeilComplex.homologySheaf (-i)).obj
      ((WeilComplex.verdierDual k₀ l _).obj
        (Opposite.op ((WeilComplex.derivedLowerShriek k₀ l
          (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F)))) ≅
      (WeilComplex.homologySheaf j).obj
        ((WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj
          (toComplex.obj G)) :=
    (WeilComplex.homologySheaf (-i)).mapIso E ≪≫
      WeilComplex.homologySheafShiftIso _ (2 * d : ℤ) (-i) j (by lia)
  -- Duality on the point and evaluation finish both assertions simultaneously.
  obtain ⟨ed⟩ := homology_verdierDual_equiv
    ((WeilComplex.derivedLowerShriek k₀ l
      (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F)) i
  exact exists_pairing_of_equiv_dual ((globalSectionsEquivOfIso EH).symm.trans ed)

end AlgebraicGeometry.WeilSheaf
