/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidLaws
public import Mathlib.RingTheory.Norm.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Invariance of the source norm of a target pullback

Source: Stacks Project, Groupoid Schemes, Tag 03BH, `lemma-determinant-trick`,
and Divisors, Tag 0BD2, `lemma-finite-locally-free-has-norm`
(blueprint: lem-a1-affine-groupoid-invariant-norm).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Right cancellation, expressed on the chosen scheme pullback. -/
private theorem groupoid_cancel
    {U R H : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
    {c : pullback s t ⟶ R} (hG : Scheme.IsGroupoid s t e i c)
    (p : H ⟶ pullback s t) :
    ∃ q : H ⟶ pullback s t,
      q ≫ pullback.fst s t = p ≫ c ∧
      q ≫ pullback.snd s t = p ≫ pullback.snd s t ≫ i ∧
      q ≫ c = p ≫ pullback.fst s t := by
  let b := p ≫ pullback.snd s t
  let a := p ≫ pullback.fst s t
  have hab : a ≫ s = b ≫ t := by
    simpa only [a, b, Category.assoc] using congrArg (p ≫ ·) (pullback.condition (f := s) (g := t))
  let q : _ ⟶ pullback s t := pullback.lift b (b ≫ i) (by simp [Category.assoc, hG.target_inv])
  have hq : q ≫ c = b ≫ t ≫ e := hG.comp_inv H b q (by simp [q]) (by simp [q])
  let r : _ ⟶ pullback s t := pullback.lift (p ≫ c) (b ≫ i) (by
    simp [Category.assoc, hG.source_comp, hG.target_inv, b])
  let z : _ ⟶ pullback s t := pullback.lift a (q ≫ c) (by
    rw [hq]
    simpa [Category.assoc, hG.target_id] using hab)
  refine ⟨r, by simp [r], by simp [r, b], ?_⟩
  calc
    r ≫ c = z ≫ c := hG.assoc H p q r z (by simp [q, b])
      (by simp [r]) (by simp [r, q]) (by simp [z, a]) (by simp [z])
    _ = a := hG.comp_id H a z (by simp [z]) (by
      simp only [z, pullback.lift_snd, hq]
      simpa only [Category.assoc] using congrArg (· ≫ e) hab.symm)

/-- The lower right square in the standard groupoid diagram is cartesian. -/
private theorem groupoid_isPullback
    {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
    {c : pullback s t ⟶ R} (hG : Scheme.IsGroupoid s t e i c) :
    IsPullback c (pullback.snd s t) s s := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk c (pullback.snd s t) hG.source_comp)
  apply PullbackCone.isLimitAux'
  intro k
  let a := k.fst
  let b := k.snd
  let q : _ ⟶ pullback s t := pullback.lift (b ≫ i) b (by simp [Category.assoc, hG.source_inv])
  have hq : q ≫ c = b ≫ s ≫ e := hG.inv_comp k.pt b q (by simp [q]) (by simp [q])
  let p : _ ⟶ pullback s t := pullback.lift a (b ≫ i) (by
    simpa [Category.assoc, hG.target_inv, a, b] using k.condition)
  let r : _ ⟶ pullback s t := pullback.lift (p ≫ c) b (by
    simp [Category.assoc, hG.source_comp, hG.source_inv, p])
  let z : _ ⟶ pullback s t := pullback.lift a (q ≫ c) (by
    rw [hq]
    simpa [Category.assoc, hG.target_id, a, b] using k.condition)
  have hr : r ≫ c = a := by
    calc
      r ≫ c = z ≫ c := hG.assoc k.pt p q r z (by simp [p, q])
        (by simp [r]) (by simp [r, q]) (by simp [z, p]) (by simp [z])
      _ = a := hG.comp_id k.pt a z (by simp [z]) (by
        simp only [z, pullback.lift_snd, hq]
        simpa only [a, b, Category.assoc] using congrArg (· ≫ e) k.condition.symm)
  refine ⟨r, hr, by simp [r, b], ?_⟩
  intro m hm₁ hm₂
  change m ≫ c = k.fst at hm₁
  change m ≫ pullback.snd s t = k.snd at hm₂
  obtain ⟨v, hv₁, hv₂, hv⟩ := groupoid_cancel hG m
  have hvp : v = p := by
    apply pullback.hom_ext
    · simpa [p, a] using hv₁.trans hm₁
    · simpa only [p, pullback.lift_snd, ← Category.assoc, hm₂, b] using hv₂
  refine pullback.hom_ext (f := s) (g := t) (k := m) (l := r) ?_ ?_
  · simpa [r, hvp] using hv.symm
  · simpa [r, b] using hm₂

/-- Norms on a finite free affine chart commute with an arbitrary affine base change. -/
private theorem norm_baseChange_chart
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {s : X ⟶ S} {q : Y ⟶ T}
    (H : IsPullback g q s f) [IsFinite s]
    {V : S.Opens} {W : T.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V)
    (hfree : letI := (s.app V).hom.toAlgebra; Module.Free Γ(S, V) Γ(X, s ⁻¹ᵁ V))
    (a : Γ(X, s ⁻¹ᵁ V)) :
    (f.appLE V W hWV).hom
        (letI := (s.app V).hom.toAlgebra; Algebra.norm Γ(S, V) a) =
      (letI := (q.app W).hom.toAlgebra
       Algebra.norm Γ(T, W) ((g.appLE (s ⁻¹ᵁ V) (q ⁻¹ᵁ W) (by
         rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
         exact q.preimage_mono hWV)).hom a)) := by
  have hsub : q ⁻¹ᵁ W ≤ g ⁻¹ᵁ (s ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hWV
  have hUY : q ⁻¹ᵁ W = g ⁻¹ᵁ (s ⁻¹ᵁ V) ⊓ q ⁻¹ᵁ W :=
    (inf_eq_right.mpr hsub).symm
  have hpo := (isIso_pushoutSection_iff H hWV le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hWV le_rfl hUY hV hW (hV.preimage s))
  rw [← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE] at hpo
  let : Algebra Γ(S, V) Γ(X, s ⁻¹ᵁ V) := (s.app V).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(T, W) := (f.appLE V W hWV).hom.toAlgebra
  let : Algebra Γ(X, s ⁻¹ᵁ V) Γ(Y, q ⁻¹ᵁ W) :=
    (g.appLE (s ⁻¹ᵁ V) (q ⁻¹ᵁ W) hsub).hom.toAlgebra
  let : Algebra Γ(T, W) Γ(Y, q ⁻¹ᵁ W) := (q.app W).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(Y, q ⁻¹ᵁ W) :=
    (s.app V ≫ g.appLE (s ⁻¹ᵁ V) (q ⁻¹ᵁ W) hsub).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, s ⁻¹ᵁ V) Γ(Y, q ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) Γ(T, W) Γ(Y, q ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (s.app V ≫ g.appLE _ _ hsub).hom = (f.appLE V W hWV ≫ q.app W).hom
      exact congrArg CommRingCat.Hom.hom hpo.w)
  have : Module.Free Γ(S, V) Γ(X, s ⁻¹ᵁ V) := hfree
  have : Module.Finite Γ(S, V) Γ(X, s ⁻¹ᵁ V) := s.finite_app V hV
  have : Algebra.IsPushout Γ(S, V) Γ(X, s ⁻¹ᵁ V) Γ(T, W) Γ(Y, q ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo
  have : Algebra.IsPushout Γ(S, V) Γ(T, W) Γ(X, s ⁻¹ᵁ V) Γ(Y, q ⁻¹ᵁ W) :=
    Algebra.IsPushout.symm inferInstance
  let E := Algebra.IsPushout.equiv Γ(S, V) Γ(T, W) Γ(X, s ⁻¹ᵁ V) Γ(Y, q ⁻¹ᵁ W)
  open scoped TensorProduct in
  have he : E (1 ⊗ₜ a) = (g.appLE (s ⁻¹ᵁ V) (q ⁻¹ᵁ W) hsub).hom a := by
    simp only [E, Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  rw [← he, Algebra.norm_eq_of_algEquiv E]
  simp only [Algebra.norm_apply]
  rw [← Algebra.baseChange_lmul, LinearMap.det_baseChange]
  rfl

/-- Apply an affine base-change chart to sections on the whole schemes. -/
private theorem norm_baseChange_global_chart
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {s : X ⟶ S} {q : Y ⟶ T}
    (H : IsPullback g q s f) [IsFinite s]
    {V : S.Opens} {W : T.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V)
    (hfree : letI := (s.app V).hom.toAlgebra; Module.Free Γ(S, V) Γ(X, s ⁻¹ᵁ V))
    (n : Γ(S, ⊤)) (a : Γ(X, ⊤))
    (hn : S.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op n =
      (letI := (s.app V).hom.toAlgebra
       Algebra.norm Γ(S, V)
         (X.presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op a))) :
    (f.appLE ⊤ W (by simp)).hom n =
      (letI := (q.app W).hom.toAlgebra
       Algebra.norm Γ(T, W) ((g.appLE ⊤ (q ⁻¹ᵁ W) (by simp)).hom a)) := by
  have he := congrArg (f.appLE V W hWV).hom hn
  have hb := norm_baseChange_chart H hV hW hWV hfree
    (X.presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op a)
  have hh := he.trans hb
  simpa only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] using hh

/-- The source norm of a target pullback belongs to the invariant subring.
Source: Stacks Project, Tag 03BH, `lemma-determinant-trick`, with the norm of
Tag 0BD2 (blueprint: lem-a1-affine-groupoid-invariant-norm).

Here `n` is the norm section, specified by exactly the local finite-free determinant
charts of `exists_finiteLocallyFree_norm_charts` for `W = ⊤` and the section corresponding
to `t`-sharp of `f`. The hypothesis `hn` characterizes that section, rather than assuming
that the source algebra is globally free. `Scheme.ΓSpecIso` identifies coordinate-ring
elements with global sections; `Spec.preimage` gives the source and target ring maps.

Proof:
1. Put `P = pullback s t`, with projections `p₀`, `p₁`. The groupoid laws give
   `c ≫ s = p₁ ≫ s` and `c ≫ t = p₀ ≫ t`. Besides the defining pullback square
   with top `p₀` and bottom `t`, the square with top `c` and bottom `s` is a pullback.
   Indeed `(a,b) ↦ (c(a,b),b)` is an isomorphism from `P` to `pullback s s`, with
   inverse `(h,b) ↦ (c(h,i(b)),b)`. Associativity, the inverse laws and the identity
   laws show both composites are identities; the pullback universal property makes
   these morphisms. Thus `p₁` is a base change of `s` in two ways. For `a = t♯(f)`,
   the target-composition law says `c♯(a) = p₀♯(a)`.
2. Use the charts in `hn`, as supplied by `lem-pd-finite-locally-free-norm-charts`.
   Refine intersections of their source and target inverse images to affine opens `W`
   of `Spec B`. The two pullback squares identify the section algebra over `p₁⁻¹(W)`
   with the scalar extensions of the two chart algebras; these are the tensor-product
   identifications of `lem-weil-pbc-fibre-product-affine-spectra`. A basis of either
   chart algebra pulls back to a basis, and its multiplication matrix is obtained by
   applying the base ring map entrywise. The Leibniz determinant formula
   (`def-weil-pbc-matrix-determinant`) then identifies the restrictions of `s♯(n)`
   and `t♯(n)` with the determinants of multiplication by `c♯(a)` and `p₀♯(a)` on
   the same algebra.
3. These endomorphisms agree by step 1. Their determinants agree in any bases by
   `def-weil-endomorphism-determinant`. Equality on the affine cover of `Spec B`
   gives equality of global sections by the structure-sheaf equality axiom
   (`def-pc-scheme`). Hence `s♯(n) = t♯(n)`, exactly membership in `RingHom.eqLocus`.
   The calculation is local on finite-free charts, permits varying ranks and
   nilpotents, and uses determinant `1` on rank-zero charts. -/
theorem affineGroupoid_invariant_norm
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (f n : A)
    (hn : ∀ x : Spec A, ∃ V : (Spec A).Opens, x ∈ V ∧ IsAffineOpen V ∧
      (letI := (s.app V).hom.toAlgebra
       Module.Free Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       Module.Finite Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
           ((Scheme.ΓSpecIso A).inv n) =
         Algebra.norm Γ(Spec A, V)
           ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op
             ((Scheme.ΓSpecIso B).inv ((Spec.preimage t).hom f))))) :
    n ∈ RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom := by
  classical
  let N := (Scheme.ΓSpecIso A).inv n
  let F := (Scheme.ΓSpecIso A).inv f
  let a := t.appTop F
  have ha : a = (Scheme.ΓSpecIso B).inv ((Spec.preimage t).hom f) := by
    have h := congrArg (fun φ : A ⟶ Γ(Spec B, ⊤) ↦ φ f)
      (Scheme.ΓSpecIso_inv_naturality (Spec.preimage t))
    simpa only [CommRingCat.comp_apply, Spec.map_preimage, a, F] using h.symm
  have hlocal (z : Spec B) :
      ∃ W : (Spec B).Opens, z ∈ W ∧ IsAffineOpen W ∧
        (s.appLE ⊤ W (by simp)).hom N = (t.appLE ⊤ W (by simp)).hom N := by
    obtain ⟨Vs, hzs, hVs, hfs, hfinS, hnS⟩ := hn (s z)
    obtain ⟨Vt, hzt, hVt, hft, hfinT, hnT⟩ := hn (t z)
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWle⟩ :=
      (Spec B).isBasis_affineOpens.exists_subset_of_mem_open
        (show z ∈ s ⁻¹ᵁ Vs ⊓ t ⁻¹ᵁ Vt from ⟨hzs, hzt⟩)
        (s ⁻¹ᵁ Vs ⊓ t ⁻¹ᵁ Vt).isOpen
    refine ⟨W, hzW, hW, ?_⟩
    have hs := norm_baseChange_global_chart (groupoid_isPullback hG)
      hVs hW (hWle.trans inf_le_left) hfs N a (by simpa only [N, ha] using hnS)
    have ht := norm_baseChange_global_chart (IsPullback.of_hasPullback s t)
      hVt hW (hWle.trans inf_le_right) hft N a (by simpa only [N, ha] using hnT)
    have he' : (c.appLE ⊤ (pullback.snd s t ⁻¹ᵁ W) (by simp)).hom a =
        ((pullback.fst s t).appLE ⊤ (pullback.snd s t ⁻¹ᵁ W) (by simp)).hom a := by
      have hh := congrArg (fun φ : Γ(Spec A, ⊤) ⟶ Γ(pullback s t, ⊤) ↦ φ F)
        (congrArg Scheme.Hom.appTop hG.target_comp)
      exact congrArg
        ((pullback s t).presheaf.map
          (homOfLE (le_top : pullback.snd s t ⁻¹ᵁ W ≤ ⊤)).op).hom hh
    exact hs.trans ((congrArg (fun b ↦
      letI := ((pullback.snd s t).app W).hom.toAlgebra
      Algebra.norm Γ(Spec B, W) b) he').trans ht.symm)
  choose W hzW hW he using hlocal
  have hcover : (⊤ : (Spec B).Opens) ≤ ⨆ z, W z := by
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzW z⟩
  have hglobal : s.appTop N = t.appTop N := by
    apply TopCat.Sheaf.eq_of_locally_eq' (Spec B).sheaf W ⊤
      (fun _ ↦ homOfLE le_top) hcover
    intro z
    change ((Spec B).presheaf.map (homOfLE (le_top : W z ≤ ⊤)).op).hom
        (s.appTop N) =
      ((Spec B).presheaf.map (homOfLE (le_top : W z ≤ ⊤)).op).hom (t.appTop N)
    exact he z
  change (Spec.preimage s).hom n = (Spec.preimage t).hom n
  apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
  have hs := Scheme.ΓSpecIso_inv_naturality (Spec.preimage s)
  have ht := Scheme.ΓSpecIso_inv_naturality (Spec.preimage t)
  change (Spec.preimage s ≫ (Scheme.ΓSpecIso B).inv).hom n =
    (Spec.preimage t ≫ (Scheme.ΓSpecIso B).inv).hom n
  rw [hs, ht]
  simpa only [CommRingCat.comp_apply, Spec.map_preimage, N] using hglobal

end AlgebraicGeometry
