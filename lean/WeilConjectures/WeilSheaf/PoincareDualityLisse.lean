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
import WeilConjectures.WeilSheaf.ConstantTwistCohomology

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
  let a := X ↘ Spec (CommRingCat.of k₀)
  let K := toComplex.obj F
  let T := (F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)
  let C := (WeilComplex.derivedLowerShriek k₀ l a).obj K
  obtain ⟨ed⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isLisse d F hF
  obtain ⟨et⟩ := nonempty_dual_tensorObj_tateTwistSheaf_iso F hF (d : ℤ)
  let et' : (F.dual hF).tensorObj
      ((tateTwistSheaf k₀ l X d).tensorObj (adicConstant k₀ l X)
        (isLisse_tateTwistSheaf k₀ l X d)) hF.dual ≅ T := by
    simpa only [zpow_natCast] using et
  let es : (WeilComplex.verdierDual k₀ l X).obj (Opposite.op K) ≅
      (toComplex.obj T)⟦(2 * d : ℤ)⟧ :=
    ed ≪≫ (shiftFunctor _ (2 * d : ℤ)).mapIso (toComplex.mapIso et')
  obtain ⟨ex⟩ := WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso a K
  let ec : (WeilComplex.verdierDual k₀ l _).obj (Opposite.op C) ≅
      ((WeilComplex.derivedLowerStar a).obj (toComplex.obj T))⟦(2 * d : ℤ)⟧ :=
    ex ≪≫ (WeilComplex.derivedLowerStar a).mapIso es ≪≫
      ((WeilComplex.derivedLowerStar a).commShiftIso (2 * d : ℤ)).app _
  let eh := (WeilComplex.homologySheaf (-i)).mapIso ec ≪≫
    WeilComplex.homologySheafShiftIso _ (2 * d : ℤ) (-i) j (by lia)
  obtain ⟨ep⟩ := homology_verdierDual_equiv C i
  let e : (T.cohomology j).Equiv (F.compactlySupportedCohomology i).dual :=
    (globalSectionsEquivOfIso eh).symm.trans ep
  let eL : (T.cohomology j).carrier ≃ₗ[PadicAlgCl l]
      Module.Dual (PadicAlgCl l) (F.compactlySupportedCohomology i).carrier := e.toLinearEquiv
  let P := (Module.Dual.eval (PadicAlgCl l) (F.compactlySupportedCohomology i).carrier).compl₁₂
    (LinearMap.id : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
      (F.compactlySupportedCohomology i).carrier) eL.toLinearMap
  refine ⟨P, LinearMap.IsPerfPair.compl₁₂
    (p := Module.Dual.eval (PadicAlgCl l) (F.compactlySupportedCohomology i).carrier)
    (LinearEquiv.refl (PadicAlgCl l) _) eL, ?_⟩
  intro x y
  have he : eL ((T.cohomology j).frobenius y) =
      (eL y) ∘ₗ (F.compactlySupportedCohomology i).frobenius.symm.toLinearMap :=
    e.map_frobenius y
  change eL ((T.cohomology j).frobenius y)
    ((F.compactlySupportedCohomology i).frobenius x) = eL y x
  rw [he, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end AlgebraicGeometry.WeilSheaf
