/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BertiniSingularFibreCoordinates
public import WeilConjectures.AlgebraicGeometry.BertiniLocalFirstJets
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import Mathlib.LinearAlgebra.TensorProduct.Prod
import WeilConjectures.AlgebraicGeometry.SourceFibreDifferentialSections

/-! # Comparing the universal equation with its tensor of local first jets

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of lemma-bertini;
Morphisms, base change of differentials.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local irreducible] bertiniSingularIdeal bertiniUniversalIdeal
attribute [local irreducible] bertiniSingularFibreCoordinates bertiniSingularFibreCoefficient

private theorem tensor_unit_free {X Y : Scheme.{u}} (q : X ⟶ Y)
    (L : Y.Modules) (W : Y.Opens) (e : Γ(L, W))
    (he : Scheme.Modules.IsFreeGenerator e) :
    Scheme.Modules.IsFreeGenerator (M := (Scheme.Modules.tensorPullback q).obj L)
      (U := q ⁻¹ᵁ W)
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app L).app
        W e) := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)
  let ord := Scheme.Modules.pullbackPushforwardAdjunction q
  let E := adj.leftAdjointUniq ord
  have h := (he.pullback_unit_app q).app_hom (E.app L).symm
  have hu := congrArg (fun t ↦ t.app W e) (adj.unit_leftAdjointUniq_hom_app ord L)
  change (E.hom.app L).app (q ⁻¹ᵁ W) ((adj.unit.app L).app W e) =
    (ord.unit.app L).app W e at hu
  change Scheme.Modules.IsFreeGenerator (M := (Scheme.Modules.tensorPullback q).obj L)
    ((E.app L).inv.app (q ⁻¹ᵁ W) ((ord.unit.app L).app W e)) at h
  rw [← hu] at h
  have hi := congrArg
    (fun t ↦ t.app (q ⁻¹ᵁ W) ((adj.unit.app L).app W e)) (E.app L).hom_inv_id
  change (E.app L).inv.app (q ⁻¹ᵁ W)
    ((E.app L).hom.app (q ⁻¹ᵁ W) ((adj.unit.app L).app W e)) =
      (adj.unit.app L).app W e at hi
  exact hi ▸ h

private theorem tensor_frame_expansion {X Y : Scheme.{u}} (q : X ⟶ Y)
    (L : Y.Modules) (W : Y.Opens) (e : Γ(L, W))
    (he : Scheme.Modules.IsFreeGenerator e)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) (x : I → Γ(X, ⊤)) :
    let M := (Scheme.Modules.tensorPullback q).obj L
    let V := q ⁻¹ᵁ W
    ∃ (ep : Γ(M, V)) (hep : Scheme.Modules.IsFreeGenerator ep),
      hep.coeff (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (∑ i, x i • Scheme.Modules.tensorSectionsUnit q L (s i))) =
      ∑ i, X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (x i) *
        q.app W (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))) := by
  classical
  let M := (Scheme.Modules.tensorPullback q).obj L
  let V := q ⁻¹ᵁ W
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).unit.app L
  let ep : Γ(M, V) := η.app W e
  have hep : Scheme.Modules.IsFreeGenerator ep := tensor_unit_free q L W e he
  have hu (m : Γ(L, ⊤)) : Scheme.Modules.tensorSectionsUnit q L m = η.app ⊤ m := by
    change M.presheaf.map (homOfLE q.preimage_top.ge).op (η.app ⊤ m) = _
    exact Scheme.Modules.presheaf_map_id_apply _ _
  have ht (i : I) : M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (Scheme.Modules.tensorSectionsUnit q L (s i)) =
      q.app W (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))) • ep := by
    rw [hu]
    have hn := Scheme.Modules.Hom.app_presheaf_map η
      (homOfLE (le_top : W ≤ ⊤)) (s i)
    change η.app W (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)) =
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (η.app ⊤ (s i)) at hn
    rw [← hn]
    conv_lhs =>
      rw [← he.coeff_smul (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))]
    rw [Scheme.Modules.Hom.app_smul]
    rfl
  refine ⟨ep, hep, (hep.coeff_eq_iff _ _).2 ?_⟩
  rw [Finset.sum_smul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Scheme.Modules.map_smul, ht, mul_smul]

private theorem tensor_section_eq_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : Y.Modules) (V : Y.Opens) (m : Γ(N, V)) :
    Scheme.Modules.tensorPullbackSection g N V m =
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app N).app
        V m := by
  exact ((Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g))
    N (Opposite.op V) m).symm

private theorem appLE_restrict_top {X Y : Scheme.{u}} (g : X ⟶ Y)
    (V : Y.Opens) (hV : (⊤ : X.Opens) ≤ g ⁻¹ᵁ V) (a : Γ(Y, ⊤)) :
    g.appLE V ⊤ hV (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) = g.appTop a := by
  change (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ g.appLE V ⊤ hV) a = _
  rw [Scheme.Hom.map_appLE]
  exact Scheme.presheaf_map_id_apply _ _

private theorem appLE_eq_of_eq {X Y : Scheme.{u}} (g h : X ⟶ Y) (e : g = h)
    (W : Y.Opens) (V : X.Opens) (hg : V ≤ g ⁻¹ᵁ W) (hh : V ≤ h ⁻¹ᵁ W)
    (a : Γ(Y, W)) : g.appLE W V hg a = h.appLE W V hh a := by
  subst h
  rfl

private theorem relative_d_restrict_base {X B : Scheme.{u}} (p : X ⟶ B)
    (V : X.Opens) (b : Γ(B, ⊤)) :
    p.relativeDifferentialsDerivation.d (X := Opposite.op V)
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (p.appTop b)) = 0 := by
  have ht : p.relativeDifferentialsDerivation.d (X := Opposite.op ⊤) (p.appTop b) = 0 :=
    p.relativeDifferentialsDerivation.d_app_app ⊤ b
  have hm := p.relativeDifferentialsDerivation.d_map
    (homOfLE (le_top : V ≤ ⊤)).op (p.appTop b)
  change p.relativeDifferentialsDerivation.d (X := Opposite.op V)
    (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (p.appTop b)) =
    p.relativeDifferentials.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (p.relativeDifferentialsDerivation.d (X := Opposite.op ⊤) (p.appTop b)) at hm
  exact hm.trans (by rw [ht, map_zero])

attribute [local irreducible] Scheme.Modules.tensorPullbackSection
attribute [local irreducible] Scheme.Hom.relativeDifferentialsDerivation
attribute [local irreducible] Scheme.Hom.relativeDifferentials

set_option maxHeartbeats 800000 in
-- The fibre and sheaf restriction equalities require substantial dependent elaboration.
/-- Expansion of the universal equation and its differential after passage to a source
fibre. This is a comparison identity and asserts no vanishing on the singular locus.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of lemma-bertini,
and Morphisms, lemma-base-change-differentials.
(blueprint: lem-zl-bertini-fibre-jet-comparison).

Proof: Pull the frame e back along the second ambient projection. The section-normalized
pullback unit preserves a free generator, giving ep. In that frame the universal equation
has coefficient F = sum x_i pr_2^*(a_i), with a_i = coeff_e(s_i). The relative derivation
over coefficient affine space kills x_i; Leibniz therefore gives dF = sum x_i d(a_i).
The actual map of the source fibre to Y factors through Spec kappa_U(z) and U. Its
image lies in W, proving hV. Restriction to U preserves the germs used to define the
local jets. Base change for differentials identifies the pullback of the ambient
relative differential module with the pullback from Spec kappa_U(z) of the actual
cotangent fibre. The value coordinate similarly identifies the structure-sheaf factor.
For the finite dimensional cotangent fibre, taking sections identifies its constant
pullback with A tensor that fibre: choose a finite basis, where this is the identity
on a finite power of A, and then use basis independence. The resulting map J is an
additive isomorphism, hence injective. Its value on every pure tensor is scalar
multiplication of the pulled-back value and differential. Apply this to the displayed
sum; the projection identities for bertiniSingularFibreCoordinates identify its
coefficients with rho(X i) and rho(C a). This gives the stated pair (F,dF). If the
fibre is empty, both sides and the source tensor are zero. No vanishing criterion is
used in this comparison. -/
theorem exists_bertini_fibre_jet_comparison
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤))
    (U : Y.Opens) (z : U) (W : Y.Opens) (hz : U.ι z ∈ W)
    (e : Γ(L, W)) (he : Scheme.Modules.IsFreeGenerator e) :
    let c := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
    let p := pullback.fst c f
    let M := (Scheme.Modules.tensorPullback (pullback.snd c f)).obj L
    let V := (pullback.snd c f) ⁻¹ᵁ W
    let t := (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
      ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι
    let j := (bertiniSingularIdeal f L s).subschemeι ≫
      (bertiniUniversalIdeal f L s).subschemeι
    let g := t ≫ j
    let K := (U : Scheme).residueField z
    let A := Γ((bertiniSingularToSource f L s ∣_ U).fiber z, ⊤)
    let ρ := bertiniSingularFibreRingMap f L s U z
    letI : Algebra K A := (ρ.comp MvPolynomial.C).toAlgebra
    ∃ (hV : (⊤ : ((bertiniSingularToSource f L s ∣_ U).fiber z).Opens) ≤ g ⁻¹ᵁ V)
      (ep : Γ(M, V)) (hep : Scheme.Modules.IsFreeGenerator ep),
      let F := hep.coeff (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (bertiniUniversalSection f L s))
      ∃ J : (A ⊗[K] (K × bertiniCotangentFibre f U z)) →+
          (A × Γ((Scheme.Modules.tensorPullback g).obj p.relativeDifferentials, ⊤)),
        Function.Injective J ∧
        J (∑ i, ρ (MvPolynomial.X i) ⊗ₜ[K]
          bertiniLocalFirstJet f U z W hz
            (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i)))) =
          (g.appLE V ⊤ hV F,
            ((Scheme.Modules.tensorPullback g).obj p.relativeDifferentials).presheaf.map
              (homOfLE hV).op (Scheme.Modules.tensorPullbackSection g p.relativeDifferentials
                V (p.relativeDifferentialsDerivation.d (X := Opposite.op V) F))) := by
  classical
  let c := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
  let q := pullback.snd c f
  let p := pullback.fst c f
  let M := (Scheme.Modules.tensorPullback q).obj L
  let V := q ⁻¹ᵁ W
  let T := (bertiniSingularToSource f L s ∣_ U).fiber z
  let t := (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
    ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι
  let j := (bertiniSingularIdeal f L s).subschemeι ≫
    (bertiniUniversalIdeal f L s).subschemeι
  let g : T ⟶ pullback c f := t ≫ j
  let h := (bertiniSingularToSource f L s ∣_ U).fiberToSpecResidueField z
  let K := (U : Scheme).residueField z
  let A := Γ(T, ⊤)
  let ρ := bertiniSingularFibreRingMap f L s U z
  let : Algebra K A := (ρ.comp MvPolynomial.C).toAlgebra
  have hg : g ≫ q = h ≫ (U : Scheme).fromSpecResidueField z ≫ U.ι := by
    change (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
      ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι ≫ bertiniSingularToSource f L s = _
    rw [← morphismRestrict_ι, Scheme.Hom.fiber_fac_assoc]
  have hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ V := by
    intro x _
    change q (g x) ∈ W
    have hx := congrArg (fun r : T ⟶ Y ↦ r x) hg
    change q (g x) = U.ι ((U : Scheme).fromSpecResidueField z (h x)) at hx
    rw [hx, Scheme.fromSpecResidueField_apply]
    exact hz
  have hα : ρ.comp MvPolynomial.C = ((Scheme.ΓSpecIso (.of K)).inv ≫ h.appTop).hom := by
    change (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial I K) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial I K))).inv ≫
      (bertiniSingularFibreCoordinates f L s U z).appTop).hom = _
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
      bertiniSingularFibreCoordinates_C]
  obtain ⟨ep, hep, hF⟩ := tensor_frame_expansion q L W e he s
    (fun i ↦ p.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i)))
  change ∃ (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ V) (ep : Γ(M, V))
    (hep : Scheme.Modules.IsFreeGenerator ep), _
  refine ⟨hV, ep, hep, ?_⟩
  let F := hep.coeff (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (bertiniUniversalSection f L s))
  change ∃ J : (A ⊗[K] (K × bertiniCotangentFibre f U z)) →+
    (A × Γ((Scheme.Modules.tensorPullback g).obj p.relativeDifferentials, ⊤)),
    Function.Injective J ∧ J _ = (g.appLE V ⊤ hV F, _)
  have hF' : F = ∑ i,
      (pullback c f : Scheme).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (p.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i))) *
      q.app W (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))) := hF
  obtain ⟨D, hD, hDa⟩ := exists_source_fibre_differential_sections f c U z h g hg
    (ρ.comp MvPolynomial.C) hα
  let N := (Scheme.Modules.tensorPullback g).obj p.relativeDifferentials
  let E := TensorProduct.prodRight K A A K (bertiniCotangentFibre f U z)
  let R := TensorProduct.AlgebraTensorModule.rid K A A
  let J : (A ⊗[K] (K × bertiniCotangentFibre f U z)) →ₗ[A] (A × Γ(N, ⊤)) :=
    (R.toLinearMap.prodMap D).comp E.toLinearMap
  have hJ (b : A) (v : K × bertiniCotangentFibre f U z) :
      J (b ⊗ₜ[K] v) = (v.1 • b, D (b ⊗ₜ[K] v.2)) := by
    rfl
  have hinj : Function.Injective J :=
    (R.injective.prodMap hD).comp E.injective
  refine ⟨J.toAddMonoidHom, hinj, ?_⟩
  let a : I → Γ(Y, W) := fun i ↦
    he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))
  let x : I → Γ(pullback c f, V) := fun i ↦
    (pullback c f : Scheme).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (p.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i)))
  have hx (i : I) : g.appLE V ⊤ hV (x i) = ρ (MvPolynomial.X i) := by
    rw [appLE_restrict_top]
    have hc := congrArg
      (fun r ↦ (Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv ≫ r.appTop)
      (bertiniSingularFibreCoordinates_map f L s U z)
    simp only [Scheme.Hom.comp_appTop] at hc
    have hgp : g ≫ p = bertiniSingularFibreCoefficient f L s U z := by
      unfold bertiniSingularFibreCoefficient
      simp only [g, t, j, p, bertiniUniversalProjection, c, Category.assoc]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hgp]
    change ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv ≫
      (bertiniSingularFibreCoefficient f L s U z).appTop) (MvPolynomial.X i) = _
    rw [← hc]
    have hn := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MvPolynomial.map (σ := I) ((U.ι ≫ f).residueFieldAlgebraMap z)))
    have hn' := congrArg (fun r ↦ r ≫ (bertiniSingularFibreCoordinates f L s U z).appTop) hn
    have hi := congrArg (fun r ↦ r (MvPolynomial.X i)) hn'
    change
      (bertiniSingularFibreCoordinates f L s U z).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial I K))).inv
          (MvPolynomial.map ((U.ι ≫ f).residueFieldAlgebraMap z) (MvPolynomial.X i))) =
      (bertiniSingularFibreCoordinates f L s U z).appTop
        ((Spec.map (CommRingCat.ofHom
          (MvPolynomial.map (σ := I) ((U.ι ≫ f).residueFieldAlgebraMap z)))).appTop
            ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i))) at hi
    rw [MvPolynomial.map_X] at hi
    exact hi.symm
  have hvalue (b : Γ(Y, W)) :
      g.appLE V ⊤ hV (q.app W b) =
        (bertiniLocalFirstJet f U z W hz b).1 • (1 : A) := by
    let r := (U : Scheme).fromSpecResidueField z
    have hw : (⊤ : (Spec (.of K)).Opens) ≤ r ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
      intro y _
      change U.ι ((U : Scheme).fromSpecResidueField z y) ∈ W
      rwa [Scheme.fromSpecResidueField_apply]
    have hv : r.appLE (U.ι ⁻¹ᵁ W) ⊤ hw =
        (U : Scheme).evaluation (U.ι ⁻¹ᵁ W) z hz ≫ (Scheme.ΓSpecIso (.of K)).inv := by
      apply (cancel_mono (Scheme.ΓSpecIso (.of K)).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (U : Scheme).fromSpecResidueField_appLE_ΓSpecIso_hom z (U.ι ⁻¹ᵁ W) hz
    rw [Algebra.smul_def, mul_one]
    change _ = (ρ.comp MvPolynomial.C) ((bertiniLocalFirstJet f U z W hz b).1)
    rw [hα]
    change _ = h.appTop ((Scheme.ΓSpecIso (.of K)).inv
      ((U : Scheme).evaluation (U.ι ⁻¹ᵁ W) z hz (U.ι.app W b)))
    have hvb := congrArg (fun l ↦ h.appTop (l (U.ι.app W b))) hv
    apply Eq.trans _ hvb
    change (q.app W ≫ g.appLE V ⊤ hV) b =
      (U.ι.app W ≫ r.appLE (U.ι ⁻¹ᵁ W) ⊤ hw ≫ h.appTop) b
    have ht : h.appTop = h.appLE ⊤ ⊤ (by simp) :=
      (Scheme.Hom.appLE_top_top_fiberDegree h _).symm
    rw [ht, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.comp_appLE]
    change (g ≫ q).appLE W ⊤ hV b =
      (h ≫ r ≫ U.ι).appLE W ⊤ _ b
    exact appLE_eq_of_eq _ _ hg W ⊤ _ _ b
  have hd (i : I) : p.relativeDifferentialsDerivation.d (X := Opposite.op V) (x i) = 0 := by
    exact relative_d_restrict_base p V _
  have hFsum : F = ∑ i, x i * q.app W (a i) := hF'
  let δ : Γ(pullback c f, V) →+ Γ(N, ⊤) :=
    { toFun := fun b ↦ N.presheaf.map (homOfLE hV).op
        (Scheme.Modules.tensorPullbackSection g p.relativeDifferentials V
          (p.relativeDifferentialsDerivation.d (X := Opposite.op V) b))
      map_zero' := by simp only [tensor_section_eq_unit, map_zero]
      map_add' := by intros; simp only [tensor_section_eq_unit, map_add] }
  have hder (i : I) : N.presheaf.map (homOfLE hV).op
      (Scheme.Modules.tensorPullbackSection g p.relativeDifferentials V
        (p.relativeDifferentialsDerivation.d (X := Opposite.op V) (x i * q.app W (a i)))) =
      ρ (MvPolynomial.X i) • N.presheaf.map (homOfLE hV).op
        (Scheme.Modules.tensorPullbackSection g p.relativeDifferentials V
          (p.relativeDifferentialsDerivation.d (X := Opposite.op V) (q.app W (a i)))) := by
    rw [PresheafOfModules.Derivation.d_mul, hd, smul_zero, add_zero,
      tensor_section_eq_unit, tensor_section_eq_unit, Scheme.Modules.Hom.app_smul]
    change N.presheaf.map (homOfLE hV).op ((g.app V (x i)) • _) = _
    rw [Scheme.Modules.map_smul]
    change g.appLE V ⊤ hV (x i) • _ = _
    rw [hx]
  apply Prod.ext
  · change (J (∑ i, ρ (MvPolynomial.X i) ⊗ₜ[K]
        bertiniLocalFirstJet f U z W hz (a i))).1 = g.appLE V ⊤ hV F
    rw [map_sum, hFsum, map_sum]
    simp only [hJ, Prod.fst_sum, map_mul, hx, hvalue]
    apply Finset.sum_congr rfl
    intro i _
    change _ = ρ (MvPolynomial.X i) * ((bertiniLocalFirstJet f U z W hz (a i)).1 • 1)
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_comm]
  · change (J (∑ i, ρ (MvPolynomial.X i) ⊗ₜ[K]
        bertiniLocalFirstJet f U z W hz (a i))).2 = δ F
    rw [map_sum, hFsum, map_sum]
    simp only [hJ, Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro i _
    change D _ = N.presheaf.map (homOfLE hV).op _
    exact (hDa W hz hV (a i) (ρ (MvPolynomial.X i))).trans (hder i).symm

end AlgebraicGeometry
