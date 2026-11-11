/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# The sharp cohomological bound on pro-étale affines

Let `X` be of finite type over a field `k`, of dimension at most `d`, and suppose that
`cd_ℓ(k) ≤ c`. For every classical pro-étale sheaf `F` of `A`-modules, with `A` a ring in which
`ℓ` is nilpotent (e.g. a finite `ℓ`-primary ring), and every pro-étale affine `U` over `X`, the
pro-étale cohomology `Hᵠ(U, F)` vanishes for `q > d + c`
(`AlgebraicGeometry.ProEtale.isZero_cohomology_of_proAffineEtale_of_isClassicalModuleFor`,
blueprint `lemma-uniform-bounds-pro-etale-affines--1`).

The proof follows the blueprint: `F = ν^* G` for an étale sheaf `G`, pro-étale cohomology of
`ν^* G` on `U` is étale cohomology of `G|_U`, which is the filtered colimit of the étale
cohomology of `G` on the affine étale stages `Uᵢ` of `U`
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`), and on each stage the
`ℓ`-primary version of affine Artin vanishing gives the bound `d + c`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_nsmul_of_isAffine`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open ProEtale

/-- An object of an abelian category killed by `ℓ ^ e` is `ℓ`-power torsion in the
kernel-colimit convention `AlgebraicGeometry.ProEtale.IsEllPowerTorsion`. -/
theorem ProEtale.isEllPowerTorsion_of_nsmul_id_eq_zero {C : Type*} [Category* C] [Abelian C]
    [HasColimitsOfShape ℕ C] (ℓ : ℕ) (hℓ : ℓ.Prime) (M : C) (e : ℕ)
    (he : (ℓ ^ e) • 𝟙 M = 0) : IsEllPowerTorsion ℓ hℓ M := by
  have hi : 𝟙 M ≫ ((ℓ ^ e) • 𝟙 M) = 0 := by simpa using he
  let D := ellPowerKernelFunctor ℓ (F := M)
  let a := ellPowerKernelColimitMap ℓ (F := M)
  let b : M ⟶ colimit D :=
    kernel.lift ((ℓ ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e
  have hba : b ≫ a = 𝟙 M := by
    dsimp [b, a, ellPowerKernelColimitMap]
    rw [Category.assoc, colimit.ι_desc]
    exact kernel.lift_ι _ _ _
  have hab : a ≫ b = 𝟙 (colimit D) := by
    apply colimit.hom_ext
    intro r
    let t := e + r
    have her : e ≤ t := Nat.le_add_right e r
    have hrt : r ≤ t := Nat.le_add_left r e
    have hmap : kernel.ι ((ℓ ^ r) • 𝟙 M) ≫
        kernel.lift ((ℓ ^ e) • 𝟙 M) (𝟙 M) hi ≫ D.map (homOfLE her) =
        D.map (homOfLE hrt) := by
      apply (cancel_mono (kernel.ι ((ℓ ^ t) • 𝟙 M))).mp
      simp only [D, ellPowerKernelFunctor, ellPowerKernelMap, Category.assoc,
        kernel.lift_ι, Category.comp_id]
    calc
      colimit.ι D r ≫ a ≫ b =
          kernel.ι ((ℓ ^ r) • 𝟙 M) ≫
            kernel.lift ((ℓ ^ e) • 𝟙 M) (𝟙 M) hi ≫ colimit.ι D e := by
        dsimp [a, b, ellPowerKernelColimitMap]
        rw [← Category.assoc, colimit.ι_desc]
        rfl
      _ = kernel.ι ((ℓ ^ r) • 𝟙 M) ≫
            kernel.lift ((ℓ ^ e) • 𝟙 M) (𝟙 M) hi ≫
              D.map (homOfLE her) ≫ colimit.ι D t := by rw [colimit.w]
      _ = D.map (homOfLE hrt) ≫ colimit.ι D t := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ colimit.ι D t) hmap
      _ = colimit.ι D r ≫ 𝟙 _ := by rw [colimit.w, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

namespace Scheme

/-- Vanishing of higher direct images along the structure morphism `a : X ⟶ Spec K` of a
`K`-scheme of finite type, from a torsion cohomological-dimension bound `e` on the base change
of `X` to an algebraic closure of `K`: `Rᵠa_* F = 0` for torsion `F` and `q > e`. This is the
first half of the proof of `hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure`. -/
theorem isZero_rightDerived_lowerStar_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {e : ℕ}
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : e < q) : IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} a).rightDerived q).obj F) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := {}
  have : QuasiSeparated a := inferInstance
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  let s₀ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let T := strictLocalizationToBase s₀ ≫ 𝟙 (Spec (.of K))
  let u := Spec.map (strictHenselizationEval s₀)
  have hu : IsUniversalHomeomorphism u := isUniversalHomeomorphism_spec_strictHenselizationEval
  have hs : s₀ = u ≫ T := by
    simp only [T, Category.comp_id]
    exact (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s₀).symm
  let φ : pullback a s₀ ⟶ pullback a T :=
    (pullback.congrHom rfl hs).hom ≫ (pullbackLeftPullbackSndIso a T u).inv ≫ pullback.fst _ _
  have hP := hX.of_isUniversalHomeomorphism φ
  refine isZero_of_isZero_upperStar_of_surjective (s₀ ≫ 𝟙 _) ?_ _
    (Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H a (𝟙 _) F s₀ q (by lia)
      (hP _ (Etale.isTorsion_upperStar _ hF) q hq))
  exact fun x ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩

/-- `ℓ`-primary descent of a geometric cohomological-dimension bound: let `X` be of finite type
over a field `K`, assume the étale cohomology of `ℓ`-power torsion sheaves on `Spec K` vanishes
above `c` and `cd_tor(X_K̄) ≤ e` for an algebraic closure `K̄`. Then `Hⁿ(X, F) = 0` for
`n > c + e` and every abelian sheaf `F` killed by a power of `ℓ` (Leray spectral sequence of
the structure morphism; its higher direct images are again killed by that power). -/
theorem subsingleton_H_of_nsmul_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (ℓ : ℕ) (hℓ : ℓ.Prime)
    {c e : ℕ}
    (hK : ∀ G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
      IsEllPowerTorsion ℓ hℓ G → ∀ p : ℕ, c < p → Subsingleton (Sheaf.H G p))
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {m : ℕ} (hm : (ℓ ^ m) • 𝟙 F = 0)
    (n : ℕ) (hn : c + e < n) : Subsingleton (Sheaf.H F n) :=
  Etale.subsingleton_H_of_rightDerived_lowerStar a F
    (fun q hq ↦ isZero_rightDerived_lowerStar_of_isAlgClosure L a hX F
      (isTorsion_of_nsmul_id_eq_zero (pow_pos hℓ.pos m) hm) q hq)
    (fun p _ hp ↦ hK _ (isEllPowerTorsion_of_nsmul_id_eq_zero ℓ hℓ _ m
      (Functor.nsmul_id_obj_eq_zero _ hm)) p hp) n hn

/-- **`ℓ`-primary affine Artin vanishing.** Let `X` be an affine scheme of finite type over a
field `K`, of dimension at most `d`, and assume the étale cohomology of `ℓ`-power torsion
sheaves on `Spec K` vanishes above `c`. Then `Hⁿ(X, F) = 0` for `n > d + c` and every abelian
sheaf `F` killed by a power of `ℓ` [Stacks, Tag 0F0V]. -/
theorem subsingleton_H_of_nsmul_of_isAffine {K : Type u} [Field K] (ℓ : ℕ) (hℓ : ℓ.Prime)
    {c d : ℕ}
    (hK : ∀ G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
      IsEllPowerTorsion ℓ hℓ G → ∀ p : ℕ, c < p → Subsingleton (Sheaf.H G p))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {m : ℕ} (hm : (ℓ ^ m) • 𝟙 F = 0)
    (n : ℕ) (hn : d + c < n) : Subsingleton (Sheaf.H F n) := by
  let L := AlgebraicClosure K
  let q := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : QuasiCompact a := quasiCompact_of_compactSpace a
  have : IsAffine (pullback a q) := isAffine_of_isAffineHom (pullback.snd a q)
  have hL := hasTorsionCohomologicalDimensionLE_of_isAffine
    (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed L) (pullback.snd a q)
    ((topologicalKrullDim_pullback_le_of_field a q).trans hX)
  exact subsingleton_H_of_nsmul_of_isAlgClosure L a ℓ hℓ hK hL F hm n (by omega)

end Scheme

namespace ProEtale

/-- A bound `cd_ℓ(K) ≤ c` on the `ℓ`-cohomological dimension of a field (in the sense of
`AlgebraicGeometry.ProEtale.cohomologicalDimension`) gives the vanishing of the étale cohomology
of `ℓ`-power torsion sheaves on `Spec K` above `c`. -/
theorem subsingleton_H_of_cohomologicalDimension_le (ℓ : ℕ) (hℓ : ℓ.Prime) {K : Type u}
    [Field K] {c : ℕ} (hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ c)
    (G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsEllPowerTorsion ℓ hℓ G) (p : ℕ) (hp : c < p) : Subsingleton (Sheaf.H G p) := by
  have hz : IsZero ((Etale.cohomology AddCommGrpCat.{u + 1}
      (Spec (.of K)) (p : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
    by_contra hn
    have hpc : (p : WithTop ℕ) ≤ etaleCohomologicalDimension ℓ hℓ (Spec (.of K)) :=
      le_sSup ⟨p, rfl, G, hG, hn⟩
    rw [← cohomologicalDimension_eq_etaleCohomologicalDimension] at hpc
    exact (not_le_of_gt hp) (WithTop.coe_le_coe.mp (hpc.trans hK))
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of K)) p
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hz.of_iso (e.app G))

/-- **Étale cohomology on a pro-étale affine.** Let `X` be locally of finite type over a field
`k`, of dimension at most `d`, and assume the étale cohomology of `ℓ`-power torsion sheaves on
`Spec k` vanishes above `c`. For every pro-affine étale `v : U ⟶ X` (a cofiltered limit of
affine étale `X`-schemes `Uᵢ`) and every abelian étale sheaf `F` on `X` killed by a power of
`ℓ`, `Hⁿ(U_ét, F|_U) = 0` for `n > d + c`: the group is the filtered colimit of the
`Hⁿ((Uᵢ)_ét, F|_{Uᵢ})` [Stacks, Tag 03Q6], each of which vanishes by `ℓ`-primary
affine Artin vanishing, since `dim Uᵢ ≤ dim X`. -/
theorem subsingleton_H_upperStar_of_proAffineEtale (ℓ : ℕ) (hℓ : ℓ.Prime) {k : Type u}
    [Field k] {c d : ℕ}
    (hk : ∀ G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1},
      IsEllPowerTorsion ℓ hℓ G → ∀ p : ℕ, c < p → Subsingleton (Sheaf.H G p))
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {U : Scheme.{u}} (v : U ⟶ X)
    (hv : proAffineEtale v) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {m : ℕ}
    (hm : (ℓ ^ m) • 𝟙 F = 0) (n : ℕ) (hn : d + c < n) :
    Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj F) n) := by
  obtain ⟨I, _, _, D, t, s, hs, ht⟩ := hv
  have (i : I) : IsAffine (D.obj i) := (ht i).1.2.1
  have (i : I) : Etale (t.app i) := (ht i).1.1
  have : Nonempty I := IsCofiltered.nonempty
  let E := Over.lift D t
  let b := Over.liftCone D t (Cone.mk U s) v (fun i ↦ (ht i).2)
  have hb : IsLimit ((Over.forget X).mapCone b) := hs
  have (i : I) : CompactSpace (E.obj i).left := inferInstanceAs (CompactSpace (D.obj i))
  have (i : I) : QuasiSeparatedSpace (E.obj i).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have {i j : I} (g : i ⟶ j) : IsAffineHom (E.map g).left :=
    inferInstanceAs (IsAffineHom (D.map g))
  have hstage (i : I) :
      Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (E.obj i).hom).obj F) n) :=
    Scheme.subsingleton_H_of_nsmul_of_isAffine (X := D.obj i) ℓ hℓ hk (t.app i ≫ aX)
      ((t.app i).topologicalKrullDim_le_of_etale.trans hd) _
      (Functor.nsmul_id_obj_eq_zero _ hm) n hn
  suffices h0 : ∀ z : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} b.pt.hom).obj F) n,
      z = 0 from ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩
  intro z
  obtain ⟨i, w, hw⟩ := (Etale.cohomologyMap_isColimit_of_isLimit F E b hb n).1 z
  let e := (Etale.upperStarComp AddCommGrpCat.{u + 1} (b.π.app i).left (E.obj i).hom
    b.pt.hom (Over.w (b.π.app i)).symm).app F
  have hz : Sheaf.H.map e.hom n z = 0 := by
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact hw.symm
  calc z = Sheaf.H.map (e.hom ≫ e.inv) n z := by rw [e.hom_inv_id, Sheaf.H.map_id_apply]
    _ = 0 := by rw [Sheaf.H.map_comp_apply, hz, map_zero]

/-- **Comparison of cohomology in a single degree.** For an étale sheaf `G` on a scheme `W`
with coefficients in a Grothendieck abelian category, if the étale cohomology `Hⁿ(W_ét, G)`
vanishes, then so does the pro-étale cohomology `Hⁿ(W_proét, ν^* G)`. -/
theorem isZero_homology_rightDerivedGlobalSections_comparisonUpperStar
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology C) (n : ℕ)
    (h : IsZero ((Etale.cohomology C W n).obj ((DerivedCategory.singleFunctor _ 0).obj G))) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj
      ((rightDerivedGlobalSections C W).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((comparisonUpperStar C W).obj G)))) := by
  let Γe := Sheaf.Γ W.smallEtaleTopology C
  let Γp := Sheaf.Γ (Scheme.ProEt.topology W) C
  let ee := Sheaf.ΓNatIsoSheafSections W.smallEtaleTopology C
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale W)
  let ep := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology W) C
    (Scheme.ProEt.isTerminalMkId W)
  have : ((sheafSections W.smallEtaleTopology C).obj
      (Opposite.op (MorphismProperty.Over.mk ⊤ (𝟙 W) (by infer_instance)))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ C).obj _).Additive
  have : ((sheafSections (Scheme.ProEt.topology W) C).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 W)))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ C).obj _).Additive
  have he := h.of_iso (Γe.homologyRightDerivedFunctorObjSingleFunctorIso G n).symm
  have he' := he.of_iso ((NatIso.rightDerived ee n).app G).symm
  have hp := isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj C W G n he'
  have hp' := hp.of_iso ((NatIso.rightDerived ep n).app ((comparisonUpperStar C W).obj G))
  exact hp'.of_iso (Γp.homologyRightDerivedFunctorObjSingleFunctorIso
    ((comparisonUpperStar C W).obj G) n)

/-- **Uniform bound on pro-étale affines** (blueprint
`lemma-uniform-bounds-pro-etale-affines--1`). Let `X` be locally of finite type over a field
`k`, with `dim X ≤ d` and `cd_ℓ(k) ≤ c` (the `ℓ`-cohomological dimension
`AlgebraicGeometry.ProEtale.cohomologicalDimension`), and let `A` be a ring in which `ℓ` is
nilpotent (e.g. a finite `ℓ`-primary ring). For every classical sheaf `F` of `A`-modules on
`X_proét` and every pro-étale affine `U` over `X` (an object of `X_proét` whose structure map is
pro-affine étale), `Hᵠ(U, F) = 0` for `q > d + c`.

Proof (blueprint): write `F = ν^* G` (`proEtaleClassicalSheaves`) and `U = lim Uᵢ`; then
`Hᵠ(U_proét, F|_U) = Hᵠ(U_ét, G|_U)`, whose underlying abelian group is the étale
cohomology of the underlying abelian sheaf, killed by a power of `ℓ`; it vanishes by
`subsingleton_H_upperStar_of_proAffineEtale`. -/
theorem isZero_cohomology_of_proAffineEtale_of_isClassicalModuleFor (ℓ : ℕ) (hℓ : ℓ.Prime)
    {k : Type u} [Field k] {c d : ℕ} (hk : cohomologicalDimension ℓ hℓ (Spec (.of k)) ≤ c)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (A : Type (u + 1)) [CommRing A] (hA : IsNilpotent (ℓ : A))
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (hF : IsClassicalModuleFor X A F) (U : X.ProEt) (hU : proAffineEtale U.hom)
    (q : ℤ) (hq : ((d + c : ℕ) : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) U.left).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) U.hom).obj F)))) := by
  obtain ⟨m, hm⟩ := hA
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  have hn : d + c < n := by exact_mod_cast hq
  obtain ⟨Φ, hΦ, _, _, _⟩ := (proEtaleClassicalSheaves X).2.2 A
  let G := Φ.objPreimage ⟨F, hF⟩
  let eF : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G ≅ F :=
    (eqToIso (Functor.congr_obj hΦ G)).symm ≪≫
      (ObjectProperty.ι _).mapIso (Φ.objObjPreimageIso ⟨F, hF⟩)
  let w := U.hom
  let GU := (Etale.upperStar (ModuleCat.{u + 1} A) w).obj G
  let Fo := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have h0 (V : X.Etaleᵒᵖ) (y : G.obj.obj V) : (ℓ ^ m) • y = 0 := by
    rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, hm, zero_smul]
  have hmo : (ℓ ^ m) • 𝟙 (Fo.obj G) = 0 := by
    apply Sheaf.hom_ext
    ext V x
    exact h0 V x
  have hsub := subsingleton_H_upperStar_of_proAffineEtale ℓ hℓ
    (subsingleton_H_of_cohomologicalDimension_le ℓ hℓ hk) aX hd w hU (Fo.obj G) hmo n hn
  obtain ⟨eU⟩ := Etale.exists_upperStar_forget₂_natIso A w
  let eI := eU.app G
  have hinj : Function.Injective (Sheaf.H.map eI.hom n) := fun x y hxy ↦ by
    rw [← Sheaf.H.map_id_apply x, ← Sheaf.H.map_id_apply y, ← eI.hom_inv_id,
      Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply, hxy]
  have hsub' : Subsingleton (Sheaf.H ((sheafCompose U.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj GU) n) :=
    ⟨fun x y ↦ hinj (@Subsingleton.elim _ hsub _ _)⟩
  obtain ⟨e1⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso U.left A n
  obtain ⟨e2⟩ := Scheme.nonempty_sheafH_extDerivedIso U.left n
  have hab : IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} U.left n).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((sheafCompose U.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj GU))) :=
    (AddCommGrpCat.isZero_iff_subsingleton.mpr hsub').of_iso (e2.app _).symm
  have hmod : IsZero ((Etale.cohomology (ModuleCat.{u + 1} A) U.left n).obj
      ((DerivedCategory.singleFunctor _ 0).obj GU)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp
      (hab.of_iso (e1.app GU)))
  exact (isZero_homology_rightDerivedGlobalSections_comparisonUpperStar _ GU n hmod).of_iso
    ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) U.left).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) w).mapIso eF.symm ≪≫
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) w).app G))))

end ProEtale

end AlgebraicGeometry

end
