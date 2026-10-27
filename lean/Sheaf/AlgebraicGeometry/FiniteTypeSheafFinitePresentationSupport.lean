/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.AnnihilatorAffineBasicOpen
import WeilConjectures.AlgebraicGeometry.Modules.Annihilator
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback

/-!
# A finitely presented closed subscheme supporting a finite type sheaf on one fibre

Source: Stacks Project, More on Flatness, Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-finite-type-sheaf-fp-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private theorem exists_fg_subideal_map_eq {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (hI : (I.map φ).FG) :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ J.map φ = I.map φ := by
  classical
  obtain ⟨s, hs, he⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := B) (φ '' (I : Set A))).mp hI
  have hpre (b : s) : ∃ a : A, a ∈ I ∧ φ a = b := hs b.property
  choose a ha haφ using hpre
  let J : Ideal A := Ideal.span (Set.range a)
  refine ⟨J, Submodule.fg_span (Set.finite_range a), Ideal.span_le.mpr ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ha b
  · have himage : φ '' Set.range a = (s : Set B) := by
      ext b
      constructor
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        rw [haφ c]
        exact c.property
      · intro hb
        exact ⟨a ⟨b, hb⟩, Set.mem_range_self _, haφ _⟩
    change (Ideal.span (Set.range a)).map φ = Ideal.span (φ '' (I : Set A))
    rw [Ideal.map_span, himage]
    exact he.symm

private theorem preimage_zeroLocus_appTop {Y X : Scheme.{u}} (g : Y ⟶ X)
    (s : Set Γ(X, ⊤)) :
    g ⁻¹' X.zeroLocus s = Y.zeroLocus (g.appTop.hom '' s) := by
  exact Scheme.preimage_zeroLocus g s

private theorem support_eq_zeroLocus_top {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
      X.zeroLocus (U := ⊤) (Module.annihilator Γ(X, ⊤) Γ(F, ⊤)) := by
  simpa only [IsAffineOpen.fromSpec_image_zeroLocus, TopologicalSpace.Opens.coe_top,
    Set.inter_univ] using
    (finite_type_module_support_closed X F).2.2.1 ⟨⊤, isAffineOpen_top X⟩

private theorem exists_closedImmersion_of_fg_annihilator
    {X : Scheme.{u}} [IsAffine X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : Ideal Γ(X, ⊤)) (hJ : J.FG)
    (hJF : J ≤ Module.annihilator Γ(X, ⊤) Γ(F, ⊤)) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
      IsClosedImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
        QuasiSeparated j ∧
        ∃ H : Z.Modules, H.IsFiniteType ∧ H.IsQuasicoherent ∧
          Nonempty ((pushforward j).obj H ≅ F) ∧
          Set.range j.base = X.zeroLocus (U := ⊤) J := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop J
  let A : X.IdealSheafData :=
    { ideal U := Module.annihilator Γ(X, U.1) Γ(F, U.1)
      map_ideal_basicOpen U a := annihilator_affine_basicOpen X F U a }
  have hIA : I ≤ A := Scheme.IdealSheafData.le_of_isAffine (by simpa [I, A] using hJF)
  have hkill : ∀ U : X.affineOpens, ∀ a ∈ I.ideal U, ∀ m : Γ(F, U.1), a • m = 0 := by
    intro U a ha m
    exact Module.mem_annihilator.mp (hIA U ha) m
  have hfp : LocallyOfFinitePresentation I.subschemeι :=
    Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι fun U ↦ by
      exact hJ.map _
  have hunit : IsIso (pullbackUnit I.subschemeι F) :=
    isIso_pullbackUnit_subschemeι_of_smul_eq_zero F I hkill
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction I.subschemeι
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction I.subschemeι)).app F
  let H := (tensorPullback I.subschemeι).obj F
  have hHfin : H.IsFiniteType := (tensorPullback_isFiniteType _ _ I.subschemeι F).1
  have hHqc : H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent I.subscheme.ringCatSheaf).prop_of_iso e.symm
      inferInstance
  refine ⟨I.subscheme, I.subschemeι, inferInstance, hfp, inferInstance, inferInstance,
    H, hHfin, hHqc, ⟨(pushforward I.subschemeι).mapIso e ≪≫ (asIso
      (pullbackUnit I.subschemeι F)).symm⟩, ?_⟩
  simpa only [I, Scheme.IdealSheafData.coe_support_ofIdealTop] using I.range_subschemeι

/-- A finite type quasi-coherent module on an affine finite type scheme is the pushforward
of a finite type quasi-coherent module on a finitely presented closed subscheme whose
fibre at the image of the chosen point is precisely the support of the pulled-back module.
The fibre is identified with its image under the canonical base change of the immersion;
support means the locus of nonzero stalks.
Source: Stacks Project, More on Flatness, Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-finite-type-sheaf-fp-support).

Proof:
1. Write S = Spec A, X = Spec B and F = tilde M using
   lem-weil-pbc-affine-tilde-gamma-adjunction. By lem-weil-pbc-lft-affine-pairs,
   A → B is finite type. By lem-weil-pbc-quasi-coherent-finite-type-affine,
   M is finite over B. Set I = Ann_B(M).
2. Put s = f(x), k = κ(s), R = B ⊗_A k. The affine fibre-product and tilde-pullback
   formulas (lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-tilde-pullback-base-change and def-pc-module-pullback) identify
   X_s with Spec R and F_s with the tilde of M ⊗_A k. The support theorems
   lem-weil-pbc-finite-type-module-support-closed and
   lem-weil-pbc-support-pullback-finite-type give Supp(F_s) = V(IR): pulling back
   V(I) along Spec R → Spec B gives V(IR).
3. By lem-wf-affine-noetherian-components, the finite type k-algebra R is Noetherian.
   Choose finitely many elements of I whose images generate IR and let J be their
   ideal in B. Then J ⊆ I and JR = IR.
4. Set Z = Spec(B/J). The quotient map defines a closed immersion j : Z → X
   (def-weil-closed-immersion), of finite presentation since J is finitely generated
   (def-sbc-locally-finite-presentation); affine morphisms are quasi-compact and
   quasi-separated. Regard M as a B/J-module and let H be its tilde on Z.
   It is quasi-coherent and finite type by lem-weil-pbc-quasi-coherent-finite-type-affine.
   The affine pushforward formula (lem-weil-pbc-pushforward-tilde-spec and
   lem-weil-pbc-spec-module-tilde-sections) gives j_*H ≅ F.
5. By lem-weil-pbc-fibre-product-affine-spectra and right exactness of tensor,
   Z_s = Spec(R/JR), whose image in Spec R is V(JR) = V(IR) = Supp(F_s). -/
theorem exists_finitePresentation_closedImmersion_fiber_support
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
      IsClosedImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
        QuasiSeparated j ∧
        ∃ H : Z.Modules, H.IsFiniteType ∧ H.IsQuasicoherent ∧
          Nonempty ((pushforward j).obj H ≅ F) ∧
          Set.range
            (pullback.map (j ≫ f) (S.fromSpecResidueField (f x))
              f (S.fromSpecResidueField (f x)) j
              (𝟙 (Spec (S.residueField (f x)))) (𝟙 S) (by simp) (by simp)).base =
            {z : Limits.pullback (C := Scheme.{u}) f (S.fromSpecResidueField (f x)) |
              ¬ Subsingleton
                (((tensorPullback
                  (pullback.fst f (S.fromSpecResidueField (f x)))).obj F).presheaf.stalk z)} := by
  classical
  let g := pullback.fst f (S.fromSpecResidueField (f x))
  let T := Limits.pullback f (S.fromSpecResidueField (f x))
  have : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  let I := Module.annihilator Γ(X, ⊤) Γ(F, ⊤)
  obtain ⟨J, hJ, hJI, hmap⟩ := exists_fg_subideal_map_eq g.appTop.hom I
    (IsNoetherian.noetherian _)
  obtain ⟨Z, j, hj, hjfp, hjqc, hjqs, H, hHfin, hHqc, e, hrange⟩ :=
    exists_closedImmersion_of_fg_annihilator F J hJ hJI
  refine ⟨Z, j, hj, hjfp, hjqc, hjqs, H, hHfin, hHqc, e, ?_⟩
  have hzero : g ⁻¹' X.zeroLocus (U := ⊤) J = g ⁻¹' X.zeroLocus (U := ⊤) I := by
    rw [preimage_zeroLocus_appTop, preimage_zeroLocus_appTop,
      ← T.zeroLocus_span (g.appTop.hom '' (J : Set Γ(X, ⊤))),
      ← T.zeroLocus_span (g.appTop.hom '' (I : Set Γ(X, ⊤)))]
    change T.zeroLocus (U := ⊤) (J.map g.appTop.hom) =
      T.zeroLocus (U := ⊤) (I.map g.appTop.hom)
    rw [hmap]
  have hsupport := ((finiteType_module_support_pullback F).2.2 T g).2
  rw [support_eq_zeroLocus_top F] at hsupport
  change Set.range (pullback.map (j ≫ f) (S.fromSpecResidueField (f x))
    f (S.fromSpecResidueField (f x)) j
    (𝟙 (Spec (S.residueField (f x)))) (𝟙 S) (by simp) (by simp)) = _
  rw [Scheme.Pullback.range_map]
  simpa only [hrange, Scheme.Hom.id_base, TopCat.coe_id, Set.range_id,
    Set.preimage_univ, Set.inter_univ] using hzero.trans hsupport.symm

end AlgebraicGeometry.Scheme.Modules
