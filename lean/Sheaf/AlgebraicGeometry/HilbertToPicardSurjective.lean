/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.HilbertToPicardMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# Surjectivity of the Hilbert-to-Picard morphism

Source: Stacks Project, Tag 0BA0, clause (5) and proof, fourth paragraph
(blueprint: lem-sc-hilb-to-pic-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The effectiveness argument in Stacks Tag 0BA0 (5), following
`exists_abelClass_eq` with the numerical inequality `genus ≤ d`.
(blueprint: lem-sc-hilb-to-pic-surjective) -/
private theorem exists_abelClass_eq_of_genus_le {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]
    (d : ℕ) (hd : Scheme.arithmeticGenus k X ≤ d) (K : Type u) [Field K] [Algebra k K]
    (L : (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor.obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ D : (hilbertPresheaf (X ↘ Spec (.of k)) d).obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      abelClass (X ↘ Spec (.of k)) D = L.1 := by
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let XK := pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let π : XK ⟶ Spec (.of K) :=
    pullback.snd (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : XK.Over (Spec (.of K)) := ⟨π⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd
      (X ↘ Spec (.of k)) K
  have : SmoothOfRelativeDimension 1 (XK ↘ Spec (.of K)) := h₁
  have : IsProper (XK ↘ Spec (.of K)) := h₂
  have : GeometricallyIntegral (XK ↘ Spec (.of K)) := h₃
  have : IsIntegral XK := h₄
  have : Scheme.GlobalSectionsBijective K XK := .of_geometricallyIntegral
  let ℒ : XK.Modules := (fromSkeleton _).obj (Scheme.Pic.val (Y := XK) L.1)
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := Scheme.Pic.isInvertible (Y := XK) L.1
  have : Scheme.Modules.IsInvertible ℒ := Scheme.Modules.IsInvertible.of_sheafOfModules _
  have hdeg : ℒ.degree K = (d : ℤ) := by
    have h := L.2 K (𝟙 T)
    rwa [picardFibreDegree, baseChangeMap_id, Scheme.Pic.map_id] at h
  have hχ := Scheme.Modules.eulerChar_eq_degree_add (k := K) ℒ
  have hg : Scheme.arithmeticGenus K XK = Scheme.arithmeticGenus k X :=
    Scheme.arithmeticGenus_pullback (k := k) K
  rw [hdeg, hg] at hχ
  have h01 := Scheme.Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K) ℒ
  have hpos : 0 < ℒ.finrankH K 0 := by omega
  have : Nontrivial (ℒ.H 0) := Module.nontrivial_of_finrank_pos (R := K) hpos
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_ne_zero_of_nontrivial_H_zero ℒ
  -- the zero scheme `D` of `s`
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (CategoryTheory.MonoidalCategory.tensorUnit XK.Modules)
  let D := Scheme.Modules.Hom.zeroLocus s
  have hD : D.IsInvertible := (Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus s).isInvertible
    fun h ↦ hs ((Scheme.Modules.Hom.zeroLocus_eq_bot_iff s).1 h)
  have := hD.isInvertible_dual_toModules
  obtain ⟨e⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj s hD
  have hfin : IsFinite (D.subschemeι ≫ π) := hD.isFinite_subschemeι_comp (k := K)
  have hrank : (D.subschemeι ≫ π).finrankΓ = d := by
    have h := hD.degree_dual_toModules (k := K)
    rw [← Scheme.Modules.degree_congr K
      (e ≪≫ CategoryTheory.MonoidalCategory.rightUnitor _), hdeg] at h
    exact_mod_cast h.symm
  have hflat : Flat (D.subschemeι ≫ π) := inferInstance
  have hlfp : LocallyOfFinitePresentation (D.subschemeι ≫ π) := inferInstance
  refine ⟨⟨D, hfin, hflat, hlfp, fun t ↦ ?_⟩, ?_⟩
  · exact (Scheme.Hom.finrank_eq_fiberDegree (D.subschemeι ≫ π) t).trans
      ((fiberDegree_eq_finrankΓ _ t).trans hrank)
  · refine Scheme.Pic.eq_iff_nonempty_iso.2 ⟨abelClassIso (X ↘ Spec (.of k)) _ ≪≫ ?_⟩
    exact (e ≪≫ CategoryTheory.MonoidalCategory.rightUnitor _).symm

/-- For a smooth projective geometrically integral curve over a separably closed field,
the morphism from the Hilbert scheme of degree `d` divisors to the degree-`d` Picard
scheme is surjective when `d` is at least the genus.
Source: Stacks Project, Tag 0BA0, clause (5) and proof, fourth paragraph.
(blueprint: lem-sc-hilb-to-pic-surjective)

Proof: (1) The integral smooth curve has a rational point over the separably closed
field (lem-pc-rational-points-dense). After any field extension it is integral,
proper and one-dimensional, with H⁰(O) = K, h¹(O) = g, and no higher coherent
cohomology (prop-pc-xk-integral, lem-pc-projective-proper, lem-pc-vanishing-above-dim,
lem-pc-euler-characteristic-well-defined); hence χ(O) = 1 - g.
(2) A K-point of P corresponds to a Picard class represented by an invertible module
L on C_K, since the rational point splits the Picard functor (thm-pc-pic-split,
lem-pc-rational-hyp). Its degree is d by the definition of the degree component
(def-pd-degree-morphism, def-pd-fibrewise-degree, def-pc-degree-line-bundle).
(3) Thus χ(L) = d + 1 - g ≥ 1, so h⁰(L) ≥ 1 and L has a nonzero section
(def-pc-euler-characteristic).
(4) Its zero scheme D is an effective Cartier divisor on the integral curve and
L ≅ O(D) (lem-pc-nonzero-section-integral-cartier, lem-pc-zero-scheme-divisor-iso,
def-pc-divisor-line-bundle).
(5) D is finite over K and its length equals deg O(D) = d; over a field it is flat
and finitely presented, hence a degree-d Hilbert point
(lem-pc-cartier-divisor-finite-over-field, lem-pc-degree-base-change,
def-pc-finite-locally-free, def-pc-hilb-functor).
(6) Under the Hilbert representing equivalence D gives x : Spec K ⟶ H. The
classifying equality below and lem-sc-hilb-to-pic-morphism identify x ≫ γ with
the original Picard point, by naturality and Yoneda (lem-pc-yoneda).
(7) Apply this to K = κ(p) for each point p of P, with its canonical residue-field
point (def-weil-residue-field, lem-weil-pbc-residue-field-point-naturality).
The resulting lift maps to p, proving surjectivity on underlying points
(def-weil-surjective-morphism).
-/
theorem surjective_hilbertToPicardMorphism {k : Type u} [Field k] [IsSepClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve f]
    [GeometricallyIntegral f] (d : ℕ) (hd : @Scheme.arithmeticGenus k _ C ⟨f⟩ ≤ d)
    (H P : Over (Spec (.of k))) (eH : (hilbertPresheaf f d).RepresentableBy H)
    (eP : (picardFunctorDegree f d).obj.RepresentableBy P)
    (L : (pullback f H.hom).Pic)
    (hL : L ∈ (picardSubfunctorDegree f d).obj (op H))
    (hD : Nonempty ((fromSkeleton _).obj L.val ≅ ((eH.homEquiv (𝟙 H)).1).toModulesᵛ))
    (γ : H ⟶ P)
    (hγ : eP.homEquiv γ =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree f d).toFunctor).app (op H) ⟨L, hL⟩) :
    Surjective γ.left := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsSmoothProjectiveCurve (C ↘ Spec (.of k)) := ‹IsSmoothProjectiveCurve f›
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  let J := Scheme.fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f d
  let Φ := abelMapPresheaf f d
  have hclass : L = abelClass f (eH.homEquiv (𝟙 H)) := by
    obtain ⟨e⟩ := hD
    exact Scheme.Pic.eq_iff_nonempty_iso.2 ⟨e ≪≫ (abelClassIso f _).symm⟩
  have hγ' : eP.homEquiv γ =
      (toSheafify J S.toFunctor).app _ (Φ.app _ (ULift.up (eH.homEquiv (𝟙 H)))) :=
    hγ.trans (congrArg _ (Subtype.ext hclass))
  have hab {T : Over (Spec (.of k))} (h : T ⟶ H) :
      eP.homEquiv (h ≫ γ) =
        (toSheafify J S.toFunctor).app _ (Φ.app _ (ULift.up (eH.homEquiv h))) := by
    rw [eP.homEquiv_comp, hγ']
    have h₃ : eH.homEquiv h = (hilbertPresheaf f d).map h.op (eH.homEquiv (𝟙 H)) := by
      simpa using eH.homEquiv_comp h (𝟙 H)
    rw [h₃]
    refine (NatTrans.naturality_apply (toSheafify J S.toFunctor) h.op _).symm.trans ?_
    exact congrArg _ (NatTrans.naturality_apply Φ h.op _).symm
  refine ⟨fun p ↦ ?_⟩
  let κ := P.left.residueField p
  let φ : CommRingCat.of k ⟶ κ := Spec.preimage (P.left.fromSpecResidueField p ≫ P.hom)
  let K := AlgebraicClosure κ
  let : Algebra k K := ((algebraMap κ K).comp φ.hom).toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ P.left.fromSpecResidueField p ≫ P.hom := by
    rw [← Spec.map_preimage (P.left.fromSpecResidueField p ≫ P.hom), ← Spec.map_comp]
    rfl
  let x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ P :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ P.left.fromSpecResidueField p)
      (by rw [Category.assoc]; exact hK.symm)
  obtain ⟨LK, hLK⟩ := exists_toSheafify_app_eq_of_isAlgClosed S.toFunctor (eP.homEquiv x)
  obtain ⟨D, hD⟩ := exists_abelClass_eq_of_genus_le d hd K LK
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ H :=
    eH.homEquiv.symm D
  have hx : h ≫ γ = x := by
    refine eP.homEquiv.injective ?_
    rw [hab, ← hLK]
    refine congrArg _ (Subtype.ext ?_)
    rw [abelMapPresheaf_app_val]
    change abelClass f D = LK.1 at hD
    simpa only [h, Equiv.apply_symm_apply] using hD
  obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨h.left pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
  change (P.left.fromSpecResidueField p) _ = p
  exact Scheme.fromSpecResidueField_apply _ _

end AlgebraicGeometry
