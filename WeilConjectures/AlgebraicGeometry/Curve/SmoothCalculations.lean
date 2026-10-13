/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.AlgebraicGeometry.Curve.AssertionsTransfer
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierDimension
public import WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantModSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen

/-!
# The curve assertions for constant coefficients on smooth curves

Let `k` be an algebraically closed field, `f : C ⟶ Spec k` a smooth separated connected curve
(`[IsCurve f] [Smooth f] [ConnectedSpace C]`) and `n` a prime. The constant sheaf `𝐅_n` is
read over an arbitrary coefficient ring `Λ` as the constant sheaf `Λ/nΛ`
(`AlgebraicGeometry.Etale.constantModSheaf Λ C n`), and `Hᵠ(C, 𝐅_n)` is the cohomology of its
underlying abelian sheaf, as in the eight curve assertions
`AlgebraicGeometry.IsCurve.Assertions`. This file states, for `F = 𝐅_n`, each assertion
`C₁, …, C₈` in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`,
under the hypotheses of the smooth-curve calculations:

* `C₁`, `C₈` for every prime `n`; `C₂` for affine `C`; `C₅`, `C₇` for proper `C`;
* `C₄`, `C₆` for `n ≠ char k`;
* `C₃` for `n = char k = p > 0`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_two_lt`: `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine`: `C₂`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP`: `C₃`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_ne_zero`: `C₄`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_isProper`: `C₅`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_ne_zero`: `C₆`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_isProper`: `C₇`.
- `AlgebraicGeometry.IsCurve.surjective_cohomologyMap_constantModSheaf_two`: `C₈`.
- `AlgebraicGeometry.IsCurve.constantModSheaf_curveCalculations`: the smooth-curve
  calculations, the conjunction of the above.
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero`: all eight assertions
  for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve (not necessarily connected).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP`: all eight assertions
  for `𝐅_p`, `p = char k`, on a smooth curve (not necessarily connected).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Auxiliary lemmas -/

/-- The constant sheaf `Λ/nΛ` is killed by `n`: `n • 𝟙 = 0` on
`AlgebraicGeometry.Etale.constantModSheaf Λ X n`. -/
lemma Etale.nsmul_id_constantModSheaf (X : Scheme.{u}) (n : ℕ) :
    n • 𝟙 (Etale.constantModSheaf Λ X n) = 0 := by
  rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
    ← (constantSheaf _ _).map_zero]
  congr 1
  ext
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (n : Λ))

/-- For `n > 0`, the underlying abelian sheaf of the constant sheaf `Λ/nΛ` is torsion
(`CategoryTheory.Sheaf.IsTorsion`): every section is killed by `n`. -/
lemma Etale.isTorsion_constantModSheaf (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ X n)).IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have h := congr_arg
    (fun φ => ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app U)
    (Etale.nsmul_id_constantModSheaf Λ X n)
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
  have hx := congr_arg (fun φ => φ.hom x) h
  simp only [ModuleCat.hom_nsmul, ModuleCat.hom_zero] at hx
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

/-- The pullback of the underlying abelian sheaf of the constant sheaf `Λ/nΛ` along
`g : X ⟶ Y` is the underlying abelian sheaf of the constant sheaf `Λ/nΛ` on `X`. -/
noncomputable def Etale.upperStarConstantModSheafForgetIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ Y n)) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X n) :=
  (Etale.upperStar AddCommGrpCat.{u + 1} g).mapIso (Etale.constantModSheafForgetIso Λ Y n) ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app _ ≪≫
    (Etale.constantModSheafForgetIso Λ X n).symm

/-- The étale cohomology of the empty scheme vanishes. -/
lemma Etale.subsingleton_sheafH_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H G q) :=
  Etale.subsingleton_H_of_isClopen (ι := PEmpty.{u + 1}) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (fun i ↦ i.elim) (fun x ↦ isEmptyElim x) G q fun i ↦ i.elim

/-- Let `X` be a nonempty scheme. If every element of every geometric stalk of the constant
sheaf `Λ/nΛ` is killed by an integer prime to `n`, then `Λ/nΛ = 0`: the stalks are `Λ/nΛ`,
which is killed by `n`. -/
lemma Etale.subsingleton_quotient_of_forall_sheafFiber (X : Scheme.{u}) [Nonempty X] (n : ℕ)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥((Scheme.pointSmallEtale s).sheafFiber.obj (Etale.constantModSheaf Λ X n))),
      ∃ m : ℕ, m.Coprime n ∧ m • x = 0) :
    Subsingleton (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : LocallySmall.{u} X.Etale := ⟨fun _ _ ↦ small_self _⟩
  let e := (Scheme.pointSmallEtale (X.algClosurePoint x₀)).sheafFiberConstantSheafIso
    (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)))
  suffices hy : ∀ y : Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ), y = 0 from
    ⟨fun a b ↦ (hy a).trans (hy b).symm⟩
  intro y
  obtain ⟨m, hm, hx⟩ := h _ (X.algClosurePoint x₀) (e.inv y)
  have h₁ : m • y = 0 := by
    have := congrArg e.hom.hom hx
    rwa [map_nsmul, map_zero, ← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply] at this
  have h₂ : n • y = 0 := Etale.nsmul_quotient_span_eq_zero Λ n y
  rw [← AddMonoid.addOrderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hm (addOrderOf_dvd_of_nsmul_eq_zero h₁)
    (addOrderOf_dvd_of_nsmul_eq_zero h₂)

/-- The constant sheaf `Λ/nΛ` vanishes if `Λ/nΛ = 0`. -/
lemma Etale.isZero_constantModSheaf (X : Scheme.{u}) (n : ℕ)
    [Subsingleton (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ))] :
    IsZero (Etale.constantModSheaf Λ X n) :=
  Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)

/-- Every pullback map into the étale cohomology of the empty scheme is bijective. -/
lemma Etale.bijective_cohomologyMap_of_isEmpty {X Y : Scheme.{u}} [IsEmpty X] (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap g G q) := by
  have : IsEmpty Y := ⟨fun y ↦ isEmptyElim (g y)⟩
  have := Etale.subsingleton_sheafH_of_isEmpty G q
  have := Etale.subsingleton_sheafH_of_isEmpty ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G) q
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- Surjectivity of the pullback map only depends on the coefficient sheaf up to isomorphism. -/
lemma Etale.surjective_cohomologyMap_iff_of_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (n : ℕ) :
    Function.Surjective (Etale.cohomologyMap g F n) ↔
      Function.Surjective (Etale.cohomologyMap g G n) := by
  have h : Etale.cohomologyMap g G n ∘ Sheaf.H.map e.hom n =
      Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} g).mapIso e).hom n ∘
        Etale.cohomologyMap g F n :=
    funext fun x ↦ Etale.cohomologyMap_map g n e.hom x
  rw [← Function.Surjective.of_comp_iff (Etale.cohomologyMap g G n)
    (Sheaf.H.map_bijective_of_iso e n).2, h,
    Function.Surjective.of_comp_iff' (Sheaf.H.map_bijective_of_iso _ n)]

section Clopen

variable {σ : Type u} [Finite σ] {X : Scheme.{u}} (U : σ → X.Opens)
  (hU : ∀ i, IsClosed (U i : Set X)) (hdisj : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j))
  (hcov : ∀ x : X, ∃ i, x ∈ U i)
include hU hdisj hcov

/-- Let `U` be a finite clopen decomposition of `X`. If the cohomology of the constant sheaf
`Λ/nΛ` on every `Uᵢ` is finite in degree `q`, then so is that on `X`. -/
lemma Etale.finite_sheafH_constantModSheaf_of_isClopen (n q : ℕ)
    (h : ∀ i, Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ (U i) n)) q)) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X n)) q) := by
  obtain ⟨e⟩ := Etale.nonempty_equiv_pi_H_of_isClopen U hU hdisj hcov
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ X n)) q
  have (i : σ) := have := h i
    Finite.of_surjective _ (Sheaf.H.map_bijective_of_iso
      (Etale.upperStarConstantModSheafForgetIso Λ (U i).ι n).symm q).2
  exact Finite.of_equiv _ e.symm

/-- Let `U` be a finite clopen decomposition of `X`. If the cohomology of the constant sheaf
`Λ/nΛ` on every `Uᵢ` vanishes in degree `q`, then so does that on `X`. -/
lemma Etale.subsingleton_sheafH_constantModSheaf_of_isClopen (n q : ℕ)
    (h : ∀ i, Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ (U i) n)) q)) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X n)) q) :=
  Etale.subsingleton_H_of_isClopen U hU hdisj hcov _ q fun i ↦ have := h i
    (Sheaf.H.map_bijective_of_iso
      (Etale.upperStarConstantModSheafForgetIso Λ (U i).ι n) q).1.subsingleton

/-- Let `U` be a finite clopen decomposition of `X` and `g : Y ⟶ X`. If the pullback maps of
the constant sheaf `Λ/nΛ` along the restrictions `g⁻¹(Uᵢ) ⟶ Uᵢ` are bijective in degree `q`,
then so is the pullback map along `g`. -/
lemma Etale.bijective_cohomologyMap_constantModSheaf_of_isClopen {Y : Scheme.{u}} (g : Y ⟶ X)
    (n q : ℕ) (h : ∀ i, Function.Bijective (Etale.cohomologyMap (g ∣_ U i)
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ (U i) n)) q)) :
    Function.Bijective (Etale.cohomologyMap g
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X n)) q) :=
  Etale.bijective_cohomologyMap_of_isClopen U hU hdisj hcov g _ q fun i ↦
    (Etale.bijective_cohomologyMap_iff_of_iso (g ∣_ U i)
      (Etale.upperStarConstantModSheafForgetIso Λ (U i).ι n) q).2 (h i)

/-- Let `U` be a finite clopen decomposition of `X` and `g : Y ⟶ X`. If the pullback maps of
the constant sheaf `Λ/nΛ` along the restrictions `g⁻¹(Uᵢ) ⟶ Uᵢ` are surjective in degree `q`,
then so is the pullback map along `g`. -/
lemma Etale.surjective_cohomologyMap_constantModSheaf_of_isClopen {Y : Scheme.{u}} (g : Y ⟶ X)
    (n q : ℕ) (h : ∀ i, Function.Surjective (Etale.cohomologyMap (g ∣_ U i)
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ (U i) n)) q)) :
    Function.Surjective (Etale.cohomologyMap g
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X n)) q) :=
  Etale.surjective_cohomologyMap_of_isClopen U hU hdisj hcov g _ q fun i ↦
    (Etale.surjective_cohomologyMap_iff_of_iso (g ∣_ U i)
      (Etale.upperStarConstantModSheafForgetIso Λ (U i).ι n) q).2 (h i)

end Clopen

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-! ### Auxiliary lemmas -/

omit [IsAlgClosed k] in
/-- A curve over a field is quasi-compact and quasi-separated. -/
lemma compactSpace_and_quasiSeparatedSpace [IsCurve f] :
    CompactSpace C ∧ QuasiSeparatedSpace C :=
  ⟨(quasiCompact_iff_compactSpace f).mp inferInstance,
    (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance⟩

omit [IsAlgClosed k] in
/-- **The connected components of a curve.** The connected components of a curve over a field
form a finite decomposition into pairwise disjoint clopen connected opens. -/
lemma exists_isClopen_connectedSpace [IsCurve f] :
    ∃ (σ : Type u) (_ : Finite σ) (U : σ → C.Opens), (∀ i, IsClosed (U i : Set C)) ∧
      (Pairwise fun i j ↦ Disjoint (U i : Set C) (U j)) ∧ (∀ x : C, ∃ i, x ∈ U i) ∧
      ∀ i, ConnectedSpace (U i) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  choose x hx using _root_.ConnectedComponents.surjective_coe (α := C)
  let U (c : _root_.ConnectedComponents C) : C.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hU (y : C) : y ∈ U y := by
    change y ∈ connectedComponent (x y)
    rw [_root_.ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  refine ⟨_root_.ConnectedComponents C, inferInstance, U, fun c ↦ isClosed_connectedComponent,
    fun c d hcd ↦ ?_, fun y ↦ ⟨y, hU y⟩, fun c ↦
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent⟩
  refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
    (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
  rw [← hx c, ← hx d, _root_.ConnectedComponents.coe_eq_coe,
    connectedComponent_eq hyc, connectedComponent_eq hyd]

omit [IsAlgClosed k] in
/-- An open subscheme of a curve is a curve. -/
lemma isCurve_ι [IsCurve f] (V : C.Opens) : IsCurve (V.ι ≫ f) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  exact { krullDim_le_one :=
    (topologicalKrullDim_subspace_le C V).trans (IsCurve.krullDim_le_one f) }

omit [IsAlgClosed k] in
variable (k C) in
/-- If `p = char k`, a sheaf `Λ/pΛ` on a nonempty `k`-scheme with torsion of orders invertible
in `k` vanishes: `Λ/pΛ = 0`. -/
lemma subsingleton_quotient_of_isTorsionSheafOfInvertibleOrder [Nonempty C] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (Etale.constantModSheaf Λ C p)] :
    Subsingleton (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ)) := by
  refine Etale.subsingleton_quotient_of_forall_sheafFiber Λ C p fun Ω _ _ s x ↦ ?_
  obtain ⟨m, -, hm, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := Spec (.of k)) Ω s x
  refine ⟨m, ?_, hx⟩
  have hmk : IsUnit (m : k) := by
    simpa using hm.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
  have hnd : ¬ p ∣ m := fun hd ↦ hmk.ne_zero ((CharP.cast_eq_zero_iff k p m).2 hd)
  exact Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hnd)

/-- If the structure morphism of `C` is an isomorphism, so that `C` is the point `Spec k` with
`k` separably closed, every étale sheaf on `C` has no cohomology in positive degrees. -/
lemma subsingleton_sheafH_succ_of_isIso [IsIso f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H G (q + 1)) := by
  have := Scheme.subsingleton_H_of_isSepClosed k
    ((Etale.upperStar AddCommGrpCat.{u + 1} (inv f)).obj G) q
  exact (Etale.injective_cohomologyMap_of_comp_eq_id (inv f) f (IsIso.hom_inv_id _) G
    (q + 1)).subsingleton

/-- **`𝐅_p`-cohomology of a smooth connected curve in characteristic `p`.** For a smooth
separated connected curve `C` over an algebraically closed field of characteristic `p > 0`,
possibly a point, `Hᵠ(C, ℤ/p) = 0` for `q > 1`: this is the Artin–Schreier vanishing
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_constantZMod_of_charP` if `C` has
dimension one, and `C = Spec k` otherwise. -/
lemma subsingleton_sheafH_constantZMod_of_charP [IsCurve f] [Smooth f] [ConnectedSpace C]
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H (C.constantZMod p) q) := by
  by_cases hdim : topologicalKrullDim C = 1
  · have : IsConnectedCurve f := { connectedSpace := inferInstance, krullDim_eq_one := hdim }
    exact IsConnectedCurve.subsingleton_sheafH_constantZMod_of_charP f p q hq
  · have : IsIso f := IsCurve.isIso_of_connectedSpace f hdim
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    exact subsingleton_sheafH_succ_of_isIso f _ q

omit [IsAlgClosed k] in
/-- The pullback maps along the two sides of a cartesian square over a field extension agree up
to the isomorphism of the corner with the pullback: one is bijective if and only if the other is.
-/
lemma bijective_cohomologyMap_iff_of_isPullback {k' : Type u} [Field k'] {C' : Scheme.{u}}
    {a : CommRingCat.of k ⟶ CommRingCat.of k'} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map a)) (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι' G q) ↔
      Function.Bijective (Etale.cohomologyMap (Limits.pullback.fst f (Spec.map a)) G q) := by
  rw [← Etale.bijective_cohomologyMap_comp_iff h.isoPullback.hom
    (Limits.pullback.fst f (Spec.map a)) ι' h.isoPullback_hom_fst]
  exact ⟨fun H ↦ (Function.Bijective.of_comp_iff' (Etale.cohomologyMap_bijective _ _ _) _).1 H,
    fun H ↦ (Etale.cohomologyMap_bijective _ _ _).comp H⟩

omit [IsAlgClosed k] in
/-- The base change of a curve to a field extension is quasi-compact and quasi-separated. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback [IsCurve f] {k' : Type u} [Field k']
    (a : CommRingCat.of k ⟶ CommRingCat.of k') :
    CompactSpace (Limits.pullback f (Spec.map a) : Scheme.{u}) ∧
      QuasiSeparatedSpace (Limits.pullback f (Spec.map a) : Scheme.{u}) :=
  ⟨(quasiCompact_iff_compactSpace (Limits.pullback.snd f (Spec.map a))).mp inferInstance,
    (quasiSeparated_iff_quasiSeparatedSpace (Limits.pullback.snd f (Spec.map a))).mp
      inferInstance⟩

/-- **The constant sheaf `ℤ/p` in characteristic `p` under an algebraically closed extension,
away from degree one.** Let `C` be a smooth proper connected curve over `k` algebraically closed
of characteristic `p`, possibly a point, and `k'/k` an algebraically closed extension. The
pullback `Hᵠ(C, ℤ/p) ⟶ Hᵠ(C_{k'}, ℤ/p)` is bijective for `q ≠ 1`: both sides are `ℤ/p` in
degree zero, the map being injective, and vanish in degrees above one. -/
lemma bijective_fieldExtensionCohomologyMap_constantZMod_of_charP [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (p : ℕ) [Fact p.Prime] [CharP k p] (k' : Type u)
    [Field k'] [IsAlgClosed k'] [Algebra k k'] (q : ℕ) (hq : q ≠ 1) :
    Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod p) q) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  set C' := Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hinj := injective_cohomologyMap_pullback_fst_of_isAlgClosed f k' (C.constantZMod p) q
  let E := f.sheafHBaseChangeConstantZModAddEquiv k' p q
  -- the base change is again a smooth connected curve, possibly a point
  have key : ConnectedSpace C' ∧ (1 < q → Subsingleton (Sheaf.H (C'.constantZMod p) q)) := by
    by_cases hdim : topologicalKrullDim C = 1
    · have : IsConnectedCurve f := { connectedSpace := inferInstance, krullDim_eq_one := hdim }
      have : SmoothOfRelativeDimension 1 f := IsConnectedCurve.smoothOfRelativeDimension_one f
      obtain ⟨hs, -, -, -⟩ := f.baseChangeField_isCurve k'
      have : Smooth (f.baseChangeField k') := hs.smooth
      have := IsConnectedCurve.baseChangeField f k'
      exact ⟨IsConnectedCurve.connectedSpace' (f.baseChangeField k'), fun hq ↦
        IsConnectedCurve.subsingleton_sheafH_constantZMod_of_charP (f.baseChangeField k') p q hq⟩
    · have : IsIso f := IsCurve.isIso_of_connectedSpace f hdim
      have : Subsingleton C' := Scheme.subsingleton_of_iso (asIso (f.baseChangeField k'))
      obtain ⟨x₀⟩ := (inferInstance : Nonempty C)
      obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap k k'))) x₀
        (default : Spec (.of k')) (Subsingleton.elim _ _)
      have : Nonempty C' := ⟨z⟩
      refine ⟨inferInstance, fun hq ↦ ?_⟩
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact subsingleton_sheafH_succ_of_isIso (f.baseChangeField k') _ q
  obtain ⟨_, hvan⟩ := key
  rcases (show q = 0 ∨ 1 < q by omega) with rfl | hq
  · obtain ⟨e₀⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod p
    obtain ⟨e₀'⟩ := C'.nonempty_addEquiv_sheafH_zero_constantZMod p
    have : Finite (Sheaf.H (C'.constantZMod p) 0) := Finite.of_equiv _ e₀'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₀.toEquiv, Nat.card_congr e₀'.toEquiv]
  · have := hvan hq
    have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj
          (C.constantZMod p)) q) := E.toEquiv.subsingleton
    exact ⟨hinj, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **`H¹(C, ℤ/p)` of a smooth proper curve in characteristic `p` is finite.** Let `C` be a
smooth proper connected curve over an algebraically closed field `k` of characteristic `p > 0`.
Then `H¹(C, ℤ/p)` is finite: since `H⁰(C, 𝒪_C) = k` and `F - 1` is surjective on `k`, the
Artin–Schreier sequence `0 → ℤ/p → 𝔾ₐ → 𝔾ₐ → 0` (blueprint `lem-sc-as-sequence`) identifies
`H¹(C, ℤ/p)` with the kernel of `F - 1` on the finite-dimensional `H¹(C, 𝒪_C)`, which is finite
(blueprint `lem-sc-fixed-points-finite`). This is the degree-one, characteristic-`p` case of
blueprint `lem-sc-c5`.

TODO: the étale sheaf `𝔾ₐ`, the Artin–Schreier sequence and the comparison of the étale and
Zariski cohomology of `𝒪_C` are not available yet; the statement is recorded without proof. -/
theorem finite_sheafH_one_constantZMod_of_charP [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Finite (Sheaf.H (C.constantZMod p) 1) :=
  sorry

/-- **`H¹(C, ℤ/p)` of a smooth proper curve in characteristic `p` under an algebraically closed
extension.** Let `C` be a smooth proper connected curve over an algebraically closed field `k`
of characteristic `p > 0` and `k'/k` an algebraically closed extension. Then the pullback
`H¹(C, ℤ/p) ⟶ H¹(C_{k'}, ℤ/p)` is bijective: by the Artin–Schreier sequence (blueprint
`lem-sc-as-sequence`) it is the map `V^F ⟶ (V ⊗_k k')^{F ⊗ σ}` of Frobenius-fixed points of
`V = H¹(C, 𝒪_C)`, using `H¹(C_{k'}, 𝒪) = H¹(C, 𝒪) ⊗_k k'`
(blueprint `lem-sc-flat-base-change-coherent`), and this map is bijective (blueprint
`lem-sc-frobenius-fixed-invariance`). This is the degree-one, characteristic-`p` case of
blueprint `lem-sc-c7`.

TODO: the étale sheaf `𝔾ₐ`, the Artin–Schreier sequence and the comparison of the étale and
Zariski cohomology of `𝒪_C` are not available yet; the statement is recorded without proof. -/
theorem bijective_fieldExtensionCohomologyMap_one_constantZMod_of_charP [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (p : ℕ) [Fact p.Prime] [CharP k p] (k' : Type u)
    [Field k'] [IsAlgClosed k'] [Algebra k k'] :
    Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod p) 1) :=
  sorry

/-- **Opens of a smooth connected curve.** Let `C` be a smooth separated connected curve over
an algebraically closed field, possibly a point, and `a : W ⟶ C` an open immersion. Then either
`a` is an isomorphism, or `W` is an affine curve: a proper open of a smooth connected curve is
a proper open of its smooth compactification, hence affine
(`AlgebraicGeometry.IsConnectedCurve.isAffine_of_ne_top`). -/
lemma isIso_or_isAffine_of_isOpenImmersion [IsCurve f] [Smooth f] [ConnectedSpace C]
    {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a] :
    IsIso a ∨ (IsAffine W ∧ IsCurve (a ≫ f)) := by
  by_cases ha : Function.Surjective a
  · have : Surjective a := ⟨ha⟩
    exact Or.inl ((isIso_iff_isOpenImmersion_and_surjective a).mpr ⟨inferInstance, inferInstance⟩)
  refine Or.inr ⟨?_, ?_⟩
  · by_cases hdim : topologicalKrullDim C = 1
    · have : IsConnectedCurve f := { connectedSpace := inferInstance, krullDim_eq_one := hdim }
      obtain ⟨c, hc, hs, -, -⟩ := IsConnectedCurve.exists_smooth_properCompactification f
      let V := (a ≫ c.i).opensRange
      have hV : V ≠ ⊤ := by
        intro htop
        apply ha
        intro x
        have hx : c.i x ∈ V := by rw [htop]; trivial
        obtain ⟨w, hw⟩ := hx
        exact ⟨w, c.i.isOpenEmbedding.injective hw⟩
      have : IsAffine V := IsConnectedCurve.isAffine_of_ne_top c.g V hV
      exact IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq (a ≫ c.i) V.ι
        (by rw [Scheme.Opens.range_ι]; rfl)).hom
    · have : IsIso f := IsCurve.isIso_of_connectedSpace f hdim
      have : IsAffine C := IsAffine.of_isIso f
      have : Subsingleton C := Scheme.subsingleton_of_iso (asIso f)
      have : Subsingleton W := ⟨fun x y ↦ a.isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
      by_cases hW : Nonempty W
      · obtain ⟨w⟩ := hW
        exact absurd (fun x ↦ ⟨w, Subsingleton.elim _ _⟩) ha
      · have : IsEmpty W := not_nonempty_iff.mp hW
        infer_instance
  · have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
    have : QuasiCompact a := ⟨fun U _ _ ↦
      (a.isOpenEmbedding.isInducing.noetherianSpace).isCompact _⟩
    have hW : topologicalKrullDim W ≤ 1 :=
      a.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans (IsCurve.krullDim_le_one (f := f))
    exact { krullDim_le_one := hW }

/-! ### The assertions `C₁, …, C₈` for `𝐅_n` -/

/-- **`C₁` for `𝐅_n`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 2`, where `𝐅_n` is the constant
sheaf `Λ/nΛ` and `Hᵠ` is the cohomology of its underlying abelian sheaf. This is the
cohomological dimension bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`,
the constant sheaf being killed by `n`.
(blueprint: `lem-sc-c1`) -/
theorem subsingleton_sheafH_constantModSheaf_of_two_lt [IsCurve f] [Smooth f] [ConnectedSpace C]
    (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_three_le f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₂` for `𝐅_n`.** Let `C` be a smooth affine connected curve over an algebraically closed
field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 1`. This is the cohomological dimension
bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`, the constant sheaf
being killed by `n`.
(blueprint: `lem-sc-c2`) -/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsAffine C] (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_two_le_of_isAffine f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₃` for `𝐅_p`.** Let `k` be algebraically closed of characteristic `p > 0` and `C` a
smooth separated connected curve over `k`. Then `Hᵠ(C, 𝐅_p) = 0` for `q > 1`: by the
Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0` and the surjectivity of `F - 1`, the
`p`-cohomological dimension of `C` is at most one. The `p`-primary hypothesis of the field
`C₃` of `AlgebraicGeometry.IsCurve.Assertions` holds automatically for `𝐅_p` and is omitted.
(blueprint: `lem-sc-c3`) -/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP [IsCurve f] [Smooth f]
    [ConnectedSpace C] (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C p)) q) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
  exact Etale.subsingleton_sheafH_constantModSheaf Λ p q
    (subsingleton_sheafH_constantZMod_of_charP f p q hq)

/-- **`C₄` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `r` a prime different from `char k`. If `Λ/rΛ` is finite, then
`Hᵠ(C, 𝐅_r)` is finite for every `q`: `C` is proper or affine, and the
groups are computed by the Kummer sequence. The torsion hypothesis of the field `C₄` of
`AlgebraicGeometry.IsCurve.Assertions` is replaced by `(r : k) ≠ 0`.
(blueprint: `lem-sc-c4`) -/
theorem finite_sheafH_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0)
    [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  Etale.finite_sheafH_constantModSheaf Λ r q
    (IsCurve.finite_sheafH_constantZMod_of_connectedSpace f r hr q)

/-- **`C₅` for `𝐅_r`.** Let `C` be a smooth proper connected curve over an algebraically closed
field `k` and `r` an arbitrary prime. If `Λ/rΛ` is finite, then `Hᵠ(C, 𝐅_r)` is finite for
every `q`: for `r ≠ char k` by the curve estimates, and for
`r = char k = p` by the Artin–Schreier sequence, which identifies `H¹(C, 𝐅_p)` with the
Frobenius-fixed part of `H¹(C, 𝒪_C)` and kills the higher groups.
(blueprint: `lem-sc-c5`) -/
theorem finite_sheafH_constantModSheaf_of_isProper [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))]
    (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) := by
  by_cases hr : (r : k) = 0
  · have : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).2 hr
    have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
    rcases (show q = 0 ∨ q = 1 ∨ 1 < q by omega) with rfl | rfl | hq
    · obtain ⟨e₀⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod r
      exact Etale.finite_sheafH_constantModSheaf Λ r 0 (Finite.of_equiv _ e₀.symm.toEquiv)
    · exact Etale.finite_sheafH_constantModSheaf Λ r 1
        (finite_sheafH_one_constantZMod_of_charP f r)
    · have := subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f r q hq
      infer_instance
  · exact finite_sheafH_constantModSheaf_of_ne_zero Λ f r hr q

/-- **`C₆` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth separated
connected curve over `k` and `r` a prime different from `char k`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `Λ = ℤ` and
the standard square this is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`. The
torsion hypothesis of the field `C₆` of `AlgebraicGeometry.IsCurve.Assertions` is replaced by
`(r : k) ≠ 0`.
(blueprint: `lem-sc-c6`) -/
theorem bijective_cohomologyMap_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f]
    [ConnectedSpace C] (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0) (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective ι
  let : Algebra k k' := a.hom.toAlgebra
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback f a
  rw [bijective_cohomologyMap_iff_of_isPullback f h]
  exact Etale.bijective_cohomologyMap_constantModSheaf Λ r q _
    (IsCurve.bijective_fieldExtensionCohomologyMap_of_connectedSpace f k' r hr q)

/-- **`C₇` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth proper
connected curve over `k` and `r` an arbitrary prime. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `r = char k`
this is the invariance of the Frobenius-fixed part of `H¹(C, 𝒪_C)` under the extension `k'/k`.
(blueprint: `lem-sc-c7`) -/
theorem bijective_cohomologyMap_constantModSheaf_of_isProper [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) := by
  by_cases hr : (r : k) = 0
  · have : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).2 hr
    obtain ⟨a, rfl⟩ := Spec.map_surjective ι
    let : Algebra k k' := a.hom.toAlgebra
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback f a
    rw [bijective_cohomologyMap_iff_of_isPullback f h]
    by_cases hq : q = 1
    · subst hq
      exact Etale.bijective_cohomologyMap_constantModSheaf Λ r 1 _
        (bijective_fieldExtensionCohomologyMap_one_constantZMod_of_charP f r k')
    · exact Etale.bijective_cohomologyMap_constantModSheaf Λ r q _
        (bijective_fieldExtensionCohomologyMap_constantZMod_of_charP f r k' q hq)
  · exact bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ f r hr k' h q

/-- **`C₈` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k`, `a : W ⟶ C` an open immersion and `r` a prime. Then the restriction
`H²(C, 𝐅_r) ⟶ H²(W, a^* 𝐅_r)` is surjective: either `W = C`, or `W` is affine and
`H²(W, 𝐅_r) = 0`.
(blueprint: `lem-sc-c8`) -/
theorem surjective_cohomologyMap_constantModSheaf_two [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a] :
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 2) := by
  obtain ha | ⟨_, _⟩ := isIso_or_isAffine_of_isOpenImmersion f a
  · exact (Etale.cohomologyMap_bijective a _ 2).surjective
  · have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ C r))) 2) :=
      subsingleton_sheafH_of_two_le_of_isAffine (a ≫ f) _ (Etale.isTorsion_upperStar a
        (Etale.isTorsion_constantModSheaf Λ C (Fact.out : r.Prime).pos)) 2 le_rfl
    exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩

/-! ### The smooth-curve calculations -/

/-- **The smooth-curve calculations.** Let `C` be a smooth separated connected curve over an
algebraically closed field `k` and `n` a prime. The constant sheaf `𝐅_n` (read over `Λ` as
`Λ/nΛ`) satisfies

* `C₁` and `C₈`;
* `C₂` when `C` is affine, `C₅` and `C₇` when `C` is proper;
* `C₄` and `C₆` when `n ≠ char k` (part (a) of the blueprint statement), the finiteness in
  `C₄` and `C₅` when `Λ/nΛ` is finite;
* `C₃` when `n = char k` (part (b));

each in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`, with the
coefficient hypotheses specialised to `𝐅_n` as in the lemmas above. The maps in `C₆`, `C₇`,
`C₈` are the pullback maps `AlgebraicGeometry.Etale.cohomologyMap` (part (c)).

Only the assertions are stated here; the explicit groups of part (a) are the curve estimates
`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`,
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one` and
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`, and their invariance
under algebraically closed extension is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`.
(blueprint: `thm-sc-main`) -/
theorem constantModSheaf_curveCalculations [IsCurve f] [Smooth f] [ConnectedSpace C] (n : ℕ)
    [Fact n.Prime] :
    let F := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ C n)
    (∀ q, 2 < q → Subsingleton (Sheaf.H F q)) ∧
    (IsAffine C → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    (CharP k n → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    (IsProper f → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (IsProper f → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (∀ {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a],
      Function.Surjective (Etale.cohomologyMap a F 2)) :=
  ⟨subsingleton_sheafH_constantModSheaf_of_two_lt Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f n,
    fun hn _ ↦ finite_sheafH_constantModSheaf_of_ne_zero Λ f n hn,
    fun _ _ ↦ finite_sheafH_constantModSheaf_of_isProper Λ f n,
    fun hn k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ f n hn k' h,
    fun _ k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_isProper Λ f n k' h,
    fun a _ ↦ surjective_cohomologyMap_constantModSheaf_two Λ f n a⟩

/-! ### The eight assertions on smooth curves -/

/-- **The eight assertions for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve.** Let `k` be
algebraically closed, `C` a smooth separated `k`-scheme of finite type of dimension at most
one (not necessarily connected) and `ℓ` a prime different from `char k`. Then the constant sheaf
`𝐅_ℓ` (read over `Λ` as `Λ/ℓΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`; their maps are the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`. The proof goes through the Kummer sequence, the
compactification of `C` and purity for the boundary points.
(blueprint: `lemma-weil-pbc-smooth-curve-kummer-localization`) -/
theorem assertions_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) [Finite (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C ℓ) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
  obtain ⟨σ, _, U, hU, hdisj, hcov, hconn⟩ := exists_isClopen_connectedSpace f
  have hcurve (i : σ) : IsCurve ((U i).ι ≫ f) := isCurve_ι f (U i)
  have htors := Etale.isTorsion_constantModSheaf Λ C (Fact.out : ℓ.Prime).pos
  -- the base change assertions, componentwise
  have hbc (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
      (h : IsPullback ι' f' f ι) (q : ℕ) :=
    Etale.bijective_cohomologyMap_constantModSheaf_of_isClopen Λ U hU hdisj hcov ι' ℓ q
      fun i ↦ have := hconn i; have := hcurve i
      bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ ((U i).ι ≫ f) ℓ hℓ k'
        ((isPullback_morphismRestrict ι' (U i)).paste_vert h) q
  refine ⟨fun q hq ↦ subsingleton_sheafH_of_three_le f _ htors q hq,
    fun q hq ↦ subsingleton_sheafH_of_two_le_of_isAffine f _ htors q hq, ?_,
    fun q ↦ ?_, fun q ↦ ?_, fun k' _ _ _ _ _ _ h q ↦ hbc k' h q,
    fun k' _ _ _ _ _ _ h q ↦ hbc k' h q, fun a _ ↦ ?_⟩
  · -- `C₃`: a `p`-primary sheaf `Λ/ℓΛ` with `p ≠ ℓ` vanishes
    intro p _ _ hF q hq
    rcases isEmpty_or_nonempty C with hC | hC
    · exact Etale.subsingleton_sheafH_of_isEmpty _ q
    have hpℓ : p ≠ ℓ := by
      rintro rfl
      exact hℓ (CharP.cast_eq_zero k p)
    have hcop : p.Coprime ℓ := (Nat.coprime_primes Fact.out Fact.out).2 hpℓ
    have : Subsingleton (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ)) :=
      Etale.subsingleton_quotient_of_forall_sheafFiber Λ C ℓ fun Ω _ _ s x ↦
        have ⟨m, hm⟩ := hF Ω s x
        ⟨p ^ m, hcop.pow_left m, hm⟩
    exact Etale.subsingleton_H_of_isZero
      (Functor.map_isZero _ (Etale.isZero_constantModSheaf Λ C ℓ)) q
  · -- `C₄`, componentwise
    exact Etale.finite_sheafH_constantModSheaf_of_isClopen Λ U hU hdisj hcov ℓ q fun i ↦
      have := hconn i; have := hcurve i
      finite_sheafH_constantModSheaf_of_ne_zero Λ ((U i).ι ≫ f) ℓ hℓ q
  · -- `C₅`, componentwise
    exact Etale.finite_sheafH_constantModSheaf_of_isClopen Λ U hU hdisj hcov ℓ q fun i ↦
      have := hconn i; have := hcurve i
      finite_sheafH_constantModSheaf_of_ne_zero Λ ((U i).ι ≫ f) ℓ hℓ q
  · -- `C₈`, componentwise
    exact Etale.surjective_cohomologyMap_constantModSheaf_of_isClopen Λ U hU hdisj hcov a ℓ 2
      fun i ↦ have := hconn i; have := hcurve i
      surjective_cohomologyMap_constantModSheaf_two Λ ((U i).ι ≫ f) ℓ (a ∣_ U i)

/-- **The eight assertions for `𝐅_p`, `p = char k`, on a smooth curve.** Let `k` be
algebraically closed of characteristic `p > 0` and `C` a smooth separated `k`-scheme of finite
type of dimension at most one (not necessarily connected). Then the constant sheaf `𝐅_p` (read
over `Λ` as `Λ/pΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`
(`C₄` and `C₆` hold since their torsion hypothesis forces the sheaf to vanish). The proof goes
through the Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0`; for proper `C` the invariance
`C₇` comes from that of the kernel of `F - 1` on `H¹(C, 𝒪_C)` (this description of the map is
not stated).
(blueprint: `lemma-weil-pbc-smooth-curve-artin-schreier`) -/
theorem assertions_constantModSheaf_of_charP [IsCurve f] [Smooth f] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C p) := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace f
  obtain ⟨σ, _, U, hU, hdisj, hcov, hconn⟩ := exists_isClopen_connectedSpace f
  have hcurve (i : σ) : IsCurve ((U i).ι ≫ f) := isCurve_ι f (U i)
  have hproper [IsProper f] (i : σ) : IsProper ((U i).ι ≫ f) := by
    have : IsClosedImmersion (U i).ι := .of_isOpenImmersion _ (by simpa using hU i)
    infer_instance
  have htors := Etale.isTorsion_constantModSheaf Λ C (Fact.out : p.Prime).pos
  refine ⟨fun q hq ↦ subsingleton_sheafH_of_three_le f _ htors q hq,
    fun q hq ↦ subsingleton_sheafH_of_two_le_of_isAffine f _ htors q hq, ?_,
    fun q ↦ ?_, fun q ↦ ?_, fun k' _ _ _ _ _ _ h q ↦ ?_,
    fun k' _ _ _ _ _ _ h q ↦ ?_, fun a _ ↦ ?_⟩
  · -- `C₃`, componentwise
    intro p' _ _ _ q hq
    obtain rfl := CharP.eq k ‹CharP k p'› ‹CharP k p›
    exact Etale.subsingleton_sheafH_constantModSheaf_of_isClopen Λ U hU hdisj hcov p' q
      fun i ↦ have := hconn i; have := hcurve i
      subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ ((U i).ι ≫ f) p' q hq
  · -- `C₄`: a sheaf `Λ/pΛ` with torsion prime to `p` vanishes
    rcases isEmpty_or_nonempty C with hC | hC
    · have := Etale.subsingleton_sheafH_of_isEmpty
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (Etale.constantModSheaf Λ C p)) q
      infer_instance
    have := subsingleton_quotient_of_isTorsionSheafOfInvertibleOrder Λ k C p
    have := Etale.subsingleton_H_of_isZero
      (Functor.map_isZero (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
        (Etale.isZero_constantModSheaf Λ C p)) q
    infer_instance
  · -- `C₅`, componentwise
    exact Etale.finite_sheafH_constantModSheaf_of_isClopen Λ U hU hdisj hcov p q fun i ↦
      have := hconn i; have := hcurve i; have := hproper i
      finite_sheafH_constantModSheaf_of_isProper Λ ((U i).ι ≫ f) p q
  · -- `C₆`: a sheaf `Λ/pΛ` with torsion prime to `p` vanishes
    rcases isEmpty_or_nonempty C with hC | hC
    · exact Etale.bijective_cohomologyMap_of_isEmpty _ _ q
    have := subsingleton_quotient_of_isTorsionSheafOfInvertibleOrder Λ k C p
    exact (Assertions.of_isZero (f := f) (Etale.isZero_constantModSheaf Λ C p)).6 k' h q
  · -- `C₇`, componentwise
    exact Etale.bijective_cohomologyMap_constantModSheaf_of_isClopen Λ U hU hdisj hcov _ p q
      fun i ↦ have := hconn i; have := hcurve i; have := hproper i
      bijective_cohomologyMap_constantModSheaf_of_isProper Λ ((U i).ι ≫ f) p k'
        ((isPullback_morphismRestrict _ (U i)).paste_vert h) q
  · -- `C₈`, componentwise
    exact Etale.surjective_cohomologyMap_constantModSheaf_of_isClopen Λ U hU hdisj hcov a p 2
      fun i ↦ have := hconn i; have := hcurve i
      surjective_cohomologyMap_constantModSheaf_two Λ ((U i).ι ≫ f) p (a ∣_ U i)

end IsCurve

end AlgebraicGeometry
