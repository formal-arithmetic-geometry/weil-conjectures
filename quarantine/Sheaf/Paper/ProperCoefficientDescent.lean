/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.ProperCoefficientDescentData
import Sheaf.CategoryTheory.ScalarLocalizationNaturalIso
import Sheaf.Paper.ProperIntegralScalarSquare
import Sheaf.Paper.ProperRationalScalarSquare

/-! # Descent of the proper comparison through coefficient stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ProperCoefficientDescent
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients
open TensorProduct

private theorem inverse_heq {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (hA : A = A') (hB : B = B')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hA
  cases hB
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]


private theorem rationalSystem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (R : SfStrictDirectImageScalar.Comparisons l Ω f D)
    (hR : SfStrictDirectImageScalar.HasComparisonLaws l Ω f D R) :
    ∃ G : (stageSystem l Ω X).Morphism (stageSystem l Ω Y),
      (∀ E, G.Φ E = R.rational E) ∧
      ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
        HEq ((G.β h).hom.app K) ((R.theta E L h).inv.app K) := by
  let T (W : Scheme.{u}) : StageSystem (Stage l Ω W) :=
    { T := fun {E L} h ↦ transition l Ω W E L h
      assoc := fun {E L M} h j ↦ associator l Ω W E L M h j
      cocycle := fun h j k K ↦ associator_cocycle l Ω W _ _ _ _ h j k K }
  have hT (W : Scheme.{u}) : stageSystem l Ω W = T W :=
    (stageSystem_existsUnique l Ω W).unique
      (stageSystem_existsUnique l Ω W).exists.choose_spec
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
  rw [hT X, hT Y]
  let G : (T X).Morphism (T Y) :=
    { Φ := R.rational
      β := fun {E L} h ↦ (R.theta E L h).symm
      coh := by
        intro E L M h j K
        change (transition l Ω Y L M j).map ((R.theta E L h).inv.app K) ≫
          (R.theta L M j).inv.app ((transition l Ω X E L h).obj K) ≫
          (R.rational M).map ((associator l Ω X E L M h j).hom.app K) =
          (associator l Ω Y E L M h j).hom.app ((R.rational E).obj K) ≫
            (R.theta E M (h.trans j)).inv.app K
        apply (cancel_mono ((R.theta E M (h.trans j)).hom.app K)).1
        have hc := hR.2.2.2.2.2.2.2 E L M h j K
        simp only [Category.assoc]
        rw [← hc]
        simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
          Iso.inv_hom_id_app_assoc]
        simp }
  exact ⟨G, fun _ ↦ rfl, fun _ _ _ _ ↦ HEq.rfl⟩

section Descent
variable (B : FiniteFieldDatum.{u}) (hl : l ≠ B.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))] [IsProper f]

omit [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))] in
private theorem rationalizeComparison
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (R : SfStrictDirectImageScalar.Comparisons l Ω f D)
    (hR : SfStrictDirectImageScalar.HasComparisonLaws l Ω f D R)
    (S : SfCompactSupportCoefficientAction l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) Ω (Compactification.ofIsProper f))
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image) :
    ∃ r : ∀ E : Index l Ω, S.system.Φ E ≅ R.rational E,
      ∀ (E : Index l Ω) (K : Stage l Ω X E),
        HEq ((r E).hom.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
            ((θ E).hom.app K.obj)) ∧
        HEq ((r E).inv.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
            ((θ E).inv.app K.obj)) := by
  classical
  have h (E : Index l Ω) :
      ∃ r : S.system.Φ E ≅ R.rational E,
        ∀ K : Stage l Ω X E,
          HEq (r.hom.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
              ((θ E).hom.app K.obj)) ∧
          HEq (r.inv.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
              ((θ E).inv.app K.obj)) := by
    let QX := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X
    let QY := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y
    have := (sfCompactSupportFiniteIntegralFunctor_linear l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) (Compactification.ofIsProper f)
      (Coefficient.{u} l Ω E)).1
    have := (sfCompactSupportFiniteIntegralFunctor_linear l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) (Compactification.ofIsProper f)
      (Coefficient.{u} l Ω E)).2
    have hc : QX ⋙ S.system.Φ E = compactIntegral l Ω B hl f E ⋙ QY := by
      rw [S.finite_eq]
      exact CategoryTheory.Functor.ext (fun _ ↦ rfl)
    let c : QX ⋙ S.system.Φ E ≅ QX ⋙ R.rational E :=
      eqToIso hc ≪≫ isoWhiskerRight (θ E) QY ≪≫ (R.localization E).symm
    have : ∀ n : ℤ,
        (shiftFunctor (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) n).Linear
          (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E)) :=
      fun n ↦ sfIntegralConstructibleShift_linear l (Coefficient.{u} l Ω E) X n
    have : ∀ n : ℤ,
        (shiftFunctor (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) n).Additive :=
      fun n ↦ by infer_instance
    obtain ⟨r, hr, _⟩ := ScalarLocalization.naturalIso_of_integral.{u, u + 2, u + 2, u + 2, u + 2}
      (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
      (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))
      (S.system.Φ E) (R.rational E) c
    have hrhom (K : Stage l Ω X E) :
        HEq (r.hom.app K) (QY.map ((θ E).hom.app K.obj)) := by
      have he := hr K.obj
      have hi := inverse_heq ((R.localization E).app K.obj)
        (Iso.refl (QY.obj ((D.integral E).image.obj K.obj)))
        (hR.1 E K) rfl (hR.2.2.1 E K.obj)
      dsimp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        isoWhiskerRight_hom, whiskerRight_app, eqToIso.hom] at he
      simp only [eqToHom_app] at he
      apply (heq_of_eq he).trans
      apply (eqToHom_comp_heq _ _).trans
      have hh := heq_comp rfl rfl (hR.1 E K)
        (HEq.rfl : HEq (QY.map ((θ E).hom.app K.obj)) _ ) hi
      simpa only [Iso.app_inv, Iso.refl_inv, Category.comp_id] using hh
    refine ⟨r, fun K ↦ ⟨hrhom K, ?_⟩⟩
    exact inverse_heq (r.app K) (QY.mapIso ((θ E).app K.obj))
      (congrArg (fun F ↦ F.obj K) (S.finite_eq E))
      (hR.1 E K) (hrhom K)
  choose r hr using h
  exact ⟨r, hr⟩

/-- Descent of the given integral identity-compactification comparison, with the
specified scalar square, literal rationalized components and same-stage naturality.
The final natural isomorphism is on the actual quotient Hom groups; its naturality
for isoToStage includes independence of canonical scalar-extension presentations.

Source: current blueprint, prop-weil-proper-compact-coincidence.proof.md, first paragraph
(blueprint: lem-weil-proper-coefficient-descent).

Proof:
1. The identity-open tensor and restriction maps are identity on tensor sections,
by lem-sf-open-tensor-normalization. The given tower-induced comparison preserves
all quotient transitions and its chosen limit projections. InducedOnFullTower
fixes it before finite evaluation by the section-normalized ordinary maps, their
derivation, and the published compact and strict reconstruction comparisons.
The displayed projection condition is its adjunct equation from
lem-weil-proper-integral-tower-comparison.
2. Reduce the scalar square on the full coherent coefficient systems. Both scalar
maps are tensor-linear lifts through the same mixed unit. Naturality of the identity
open map and its restriction square identify their adjuncts. The universal property
in lem-pur-coefficient-extension-reduction-model identifies the coherent maps,
including their quotient transitions, not just their separate evaluations.
3. Apply lem-pod-integral-system-reduction-fully-faithful and cancel the target
reduction identification. This proves the integral square. Compose with the two
inverses to obtain its inverse version.
4. Apply raw rationalization to theta and its inverse. For a finite sum of tensors,
bilinearity reduces naturality to the integral naturality equations term by term.
The integral inverse equations give inverse rational natural transformations.
5. Rationalize the integral scalar square. The recorded compact-support beta and
ordinary comparison are precisely these localized maps. Unit and successive-field
identifications persist because functors preserve the original equations.
6. For a representative u over L, expand both mapAt expressions as beta, the image
of u, and inverse beta. The scalar square and rational naturality cancel the adjacent
betas and give the equation over this very L.
7. Scalar extension and the specified associators preserve that equation over every
further field. Equal representatives agree at a further common stage, so this gives
a natural transformation on quotient Hom groups. Its inverse descends the same way.
The identity representative gives the stated component; applying the same naturality
square to isoToStage gives independence of the scalar-extension presentation. -/
theorem properCoefficientDescent
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (_hD : SfStrictDirectImageScalar.HasIntegralLaws l Ω f D)
    (R : SfStrictDirectImageScalar.Comparisons l Ω f D)
    (_hR : SfStrictDirectImageScalar.HasComparisonLaws l Ω f D R)
    (S : SfCompactSupportCoefficientAction l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) Ω (Compactification.ofIsProper f))
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image)
    (_hθ : PreservesProjections l Ω B hl f D θ)
    (_hθtower : InducedOnFullTower l Ω B hl f D θ) :
    (∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
      (integralTransition l Ω Y E L h).map ((θ E).hom.app K) ≫
          (D.integralComparison E L h).inv.app K =
        (S.integralBeta h).hom.app K ≫
          (θ L).hom.app ((integralTransition l Ω X E L h).obj K)) ∧
    ∃ (r : ∀ E : Index l Ω, S.system.Φ E ≅ R.rational E),
      (∀ (E : Index l Ω) (K : Stage l Ω X E),
        HEq ((r E).hom.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
            ((θ E).hom.app K.obj)) ∧
        HEq ((r E).inv.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
            ((θ E).inv.app K.obj))) ∧
      ∃ (G : (stageSystem l Ω X).Morphism (stageSystem l Ω Y)),
        (∀ E : Index l Ω, G.Φ E = R.rational E) ∧
        (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
          HEq ((G.β h).hom.app K) ((R.theta E L h).inv.app K)) ∧
        ∃ (e : S.system.functor ≅ G.functor),
          (∀ A : Pair l Ω X,
            HEq (e.hom.app A) ((inclusion (l := l) (Ω := Ω) (Y := Y) A.stage).map
              ((r A.stage).hom.app A.obj)) ∧
            HEq (e.inv.app A) ((inclusion (l := l) (Ω := Ω) (Y := Y) A.stage).map
              ((r A.stage).inv.app A.obj))) ∧
          ∃ (τ : S.system.Hom G),
            (∀ E : Index l Ω, HEq (τ.τ E) (r E).hom) ∧
            e.hom = StageSystem.Morphism.descNatTrans τ ∧
            (∀ (A C : Pair l Ω X) (L : Index l Ω) (hA : A.stage ≤ L) (hC : C.stage ≤ L)
              (a : StageHom A C ⟨L, hA, hC⟩),
              S.system.mapAt a ≫ (stageTransition l Ω Y C.stage L hC).map
                  ((τ.τ C.stage).app C.obj) =
                (stageTransition l Ω Y A.stage L hA).map ((τ.τ A.stage).app A.obj) ≫
                  G.mapAt a) ∧
            (∀ (A C : Pair l Ω X) (L M : Index l Ω)
              (hA : A.stage ≤ L) (hC : C.stage ≤ L) (hLM : L ≤ M)
              (a : StageHom A C ⟨L, hA, hC⟩),
              S.system.mapAt ((stageSystem l Ω X).tr hLM a) ≫
                  (stageTransition l Ω Y C.stage M (hC.trans hLM)).map
                    ((τ.τ C.stage).app C.obj) =
                (stageTransition l Ω Y A.stage M (hA.trans hLM)).map
                    ((τ.τ A.stage).app A.obj) ≫
                  G.mapAt ((stageSystem l Ω X).tr hLM a)) ∧
            (∀ (A : Pair l Ω X) (L : Index l Ω) (h : A.stage ≤ L),
              S.system.functor.map ((stageSystem l Ω X).isoToStage A h).hom ≫
                  e.hom.app (((stageSystem l Ω X).ι L).obj (A.toStage h)) =
                e.hom.app A ≫ G.functor.map ((stageSystem l Ω X).isoToStage A h).hom) := by
  classical
  have hI := integralScalarSquare l Ω B hl f D _hD S θ _hθ _hθtower
  obtain ⟨r, hr⟩ := rationalizeComparison l Ω B hl f D R _hR S θ
  obtain ⟨⟨Φ, β, coh⟩, hΦ, hβ⟩ := rationalSystem l Ω f D R _hR
  have hΦ' : Φ = R.rational := funext hΦ
  subst Φ
  let G : (stageSystem l Ω X).Morphism (stageSystem l Ω Y) :=
    ⟨R.rational, β, coh⟩
  have hs := rationalScalarSquare l Ω B hl f D R _hR S θ hI r
    (fun E K ↦ (hr E K).1) G.β hβ
  let τ : S.system.Hom G :=
    { τ := fun E ↦ (r E).hom
      comm := fun {E L} h K ↦ eq_of_heq (hs E L h K) }
  let σ : G.Hom S.system :=
    { τ := fun E ↦ (r E).inv
      comm := by
        intro E L h K
        apply (cancel_epi ((stageTransition l Ω Y E L h).map ((r E).hom.app K))).1
        simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        rw [← Category.assoc, τ.comm h K]
        change (stageTransition l Ω Y E L h).map (𝟙 _) ≫ _ =
          ((S.system.β h).hom.app K ≫
            (r L).hom.app ((stageTransition l Ω X E L h).obj K)) ≫
              (r L).inv.app ((stageTransition l Ω X E L h).obj K)
        simp }
  have hτσ : τ.comp σ = StageSystem.Morphism.Hom.id S.system := by
    ext E K
    exact (r E).hom_inv_id_app K
  have hστ : σ.comp τ = StageSystem.Morphism.Hom.id G := by
    ext E K
    exact (r E).inv_hom_id_app K
  let e := StageSystem.Morphism.descNatIso τ σ hτσ hστ
  refine ⟨hI, r, hr, G, (fun _ ↦ rfl), hβ, e, ?_, τ,
    (fun _ ↦ HEq.rfl), rfl, ?_, ?_, ?_⟩
  · intro A
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro A C L hA hC a
    exact τ.mapAt_naturality a
  · intro A C L M hA hC hLM a
    exact τ.mapAt_naturality ((stageSystem l Ω X).tr hLM a)
  · intro A L h
    exact e.hom.naturality ((stageSystem l Ω X).isoToStage A h).hom

end Descent
end WeilConjectures.ProperCoefficientDescent
