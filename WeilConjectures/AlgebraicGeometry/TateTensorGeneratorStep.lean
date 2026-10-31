/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorGeneratorCompatibility
import WeilConjectures.AlgebraicGeometry.ComparisonPureSections
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationTensorComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-step)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local instance] Sheaf.monoidalCategory
private instance smallSite (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt
private noncomputable instance smallAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
private noncomputable instance smallAbLocal (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
private noncomputable abbrev tensorModules (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    MonoidalCategory (pbcModules T R) :=
  @SheafOfModules.cochainModulesMonoidal.{u + 1, u, u + 1}
    T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
    (ProEt.topology T) inferInstance R
attribute [local instance 2000] tensorModules
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.tensorObjIsoSheafification
open scoped TensorProduct ChangeOfRings

private theorem fixedTensor_local (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    (ProEt.topology T).W (Functor.LaxMonoidal.μ
      (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) M N) := by
  let a := presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)
  let adj := sheafificationAdjunction (ProEt.topology T) (ModuleCat.{u + 1} A)
  let m := Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) M N
  have h := adj.map_μ_comp_counit_app_tensor M N
  have : IsIso (a.map m ≫ adj.counit.app (M ⊗ N)) := by rw [h]; infer_instance
  have : IsIso (a.map m) := IsIso.of_isIso_comp_right _ (adj.counit.app (M ⊗ N))
  exact ((ProEt.topology T).W_iff m).2 this

private theorem realizedTensor_isIso (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (M N : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) :
    IsIso ((PresheafOfModules.sheafification.{u + 1} (scalars.{u} T ell n)).map
      ((ProEtale.finiteCoefficientModulePresheaf.{u, u, u + 1} T.ProEt
        (coefficient.{u} ell (n + 1))).map
        (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) M N))) := by
  let m := Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) M N
  have hi := (fixedTensor_local T _ M N).isLocallyInjective
  have hs := (fixedTensor_local T _ M N).isLocallySurjective
  let q := Functor.whiskerRight m
    (forget₂ (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) AddCommGrpCat.{u + 1})
  have : Presheaf.IsLocallyInjective (ProEt.topology T) q :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology T) m x y h⟩
  have : Presheaf.IsLocallySurjective (ProEt.topology T) q :=
    ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology T) m x⟩
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  change IsIso ((presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).map q)
  exact ((ProEt.topology T).W_iff q).1
    ((ProEt.topology T).W_of_isLocallyBijective q)

private theorem realization_tensor (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (M N : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) :
    ∃ t : (realization.{u} T ell n).obj (M ⊗ N) ⟶
        (realization.{u} T ell n).obj M ⊗ (realization.{u} T ell n).obj N,
      ∀ (W : T.ProEtᵒᵖ) (y : M.obj.obj W) (z : N.obj.obj W),
        t.val.app W
          ((toSheafify (ProEt.topology T)
            ((M ⊗ N).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
              ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
                (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) M N).app W
                  (y ⊗ₜ[coefficient.{u} ell (n + 1)] z))) =
        SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
          ((pbcAdicRings T (datum.{u} ell)).obj (op n))
          ((realization.{u} T ell n).obj M) ((realization.{u} T ell n).obj N) W
          ((toSheafify (ProEt.topology T)
            (M.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W y)
          ((toSheafify (ProEt.topology T)
            (N.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W z) := by
  let A := coefficient.{u} ell (n + 1)
  let R := (pbcAdicRings T (datum.{u} ell)).obj (op n)
  let P := ProEtale.finiteCoefficientModulePresheaf.{u, u, u + 1} T.ProEt A
  let S := PresheafOfModules.sheafification.{u + 1} (scalars.{u} T ell n)
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} (scalars.{u} T ell n)).unit
  let m := Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} A)) M N
  let O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A)
  let : MonoidalCategory (_root_.PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A))) :=
    PresheafOfModules.monoidalCategory (R := O)
  let q : P.obj M.obj ⊗ P.obj N.obj ≅ P.obj (M.obj ⊗ N.obj) :=
    PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  obtain ⟨e, he⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses.{u}
    (O := O) (R := R) (scalars.{u} T ell n)
  let r := S.map (P.map m)
  have : IsIso r := realizedTensor_isIso T ell n M N
  let t := inv r ≫ S.map q.inv ≫ e.inv.app (P.obj M.obj, P.obj N.obj)
  refine ⟨t, ?_⟩
  intro W y z
  have hn := congrArg (fun k ↦ k.app W (y ⊗ₜ[A] z)) (η.naturality (P.map m))
  change (η.app (P.obj (M ⊗ N).obj)).app W (m.app W (y ⊗ₜ[A] z)) =
    r.val.app W ((η.app (P.obj (M.obj ⊗ N.obj))).app W (y ⊗ₜ[A] z)) at hn
  change t.val.app W ((η.app (P.obj (M ⊗ N).obj)).app W
    (m.app W (y ⊗ₜ[A] z))) = _
  erw [hn]
  have hi := congrArg (fun k : S.obj (P.obj (M.obj ⊗ N.obj)) ⟶
      S.obj (P.obj (M.obj ⊗ N.obj)) ↦ k.val.app W
    ((η.app (P.obj (M.obj ⊗ N.obj))).app W (y ⊗ₜ[A] z)))
    (IsIso.hom_inv_id r)
  change (inv r).val.app W (r.val.app W _) = _ at hi
  change (e.inv.app (P.obj M.obj, P.obj N.obj)).val.app W
    ((S.map q.inv).val.app W ((inv r).val.app W (r.val.app W _))) = _
  rw [hi]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app]
  have hq := congrArg (fun k ↦ k.app W (y ⊗ₜ[A] z)) (η.naturality q.inv)
  change (η.app (P.obj M.obj ⊗ P.obj N.obj)).app W (y ⊗ₜ[A] z) =
    (S.map q.inv).val.app W ((η.app (P.obj (M.obj ⊗ N.obj))).app W
      (y ⊗ₜ[A] z)) at hq
  erw [← hq]
  exact he (P.obj M.obj) (P.obj N.obj) W y z

private def extensionIso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) :
    (pbcExtend φ).obj M ≅ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
  eqToIso ((pbcExtensionExistence φ).choose_spec.choose M)

private theorem extensionIso_section (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (W : T.ProEtᵒᵖ) (s : S.obj.obj W) (x : M.val.obj W) :
    (extensionIso T φ M).hom.val.app W (pbcTensorSection.{u} φ M W s x) =
      SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1} φ M W x s := by
  unfold extensionIso pbcTensorSection completedAdicChangeTensor
  have h := eqToHom_trans
    ((pbcExtensionExistence φ).choose_spec.choose M).symm
    ((pbcExtensionExistence φ).choose_spec.choose M)
  have hh := congrArg (fun k : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ↦ k.val.app W
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app W
        (s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] x))) h
  exact hh

private theorem extensionIso_inv_section (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (W : T.ProEtᵒᵖ) (s : S.obj.obj W) (x : M.val.obj W) :
    (extensionIso T φ M).inv.val.app W
        (SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1} φ M W x s) =
      pbcTensorSection φ M W s x := by
  have he := extensionIso_section T φ M W s x
  have hi := congrArg (fun k : (pbcExtend φ).obj M ⟶ (pbcExtend φ).obj M ↦
    k.val.app W (pbcTensorSection φ M W s x)) (extensionIso T φ M).hom_inv_id
  change (extensionIso T φ M).inv.val.app W
    ((extensionIso T φ M).hom.val.app W (pbcTensorSection φ M W s x)) =
      pbcTensorSection φ M W s x at hi
  exact (congrArg ((extensionIso T φ M).inv.val.app W) he).symm.trans hi

private theorem realization_map_section (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) {M N : Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))}
    (k : M ⟶ N) (W : T.ProEtᵒᵖ) (y : M.obj.obj W) :
    ((realization.{u} T ell n).map k).val.app W
      ((toSheafify (ProEt.topology T)
        (M.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W y) =
    (toSheafify (ProEt.topology T)
      (N.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W (k.hom.app W y) := by
  let q := Functor.whiskerRight k.hom
    (forget₂ (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) AddCommGrpCat.{u + 1})
  exact (ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality (ProEt.topology T) q) W) y).symm

section RootContraction

attribute [local semireducible] SheafOfModules.monoidalCategory

private def contractRoot (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] :
    integralLine T ell 1 ⟶ integralRoot T ell :=
  (λ_ (integralRoot T ell)).hom

private theorem contractRoot_generator (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (W : T.ProEtᵒᵖ) (x : Fin 1 → (purTwistZlOne T ell).obj.obj W) :
    (contractRoot T ell).val.app W (integralGenerator T ell W 1 x) = x 0 := by
  change (λ_ (integralRoot T ell)).hom.val.app W
    (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
      (pbcAdicCompletion T (datum.{u} ell)) (𝟙_ _) (integralRoot T ell) W
      (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj W) (x 0)) = _
  exact (SheafOfModules.pure_left_unit (pbcAdicCompletion T (datum.{u} ell))
    (integralRoot T ell) W 1 (x 0)).trans (one_smul _ _)

end RootContraction

set_option maxHeartbeats 1200000 in
-- The coefficient presentations require additional definitional equality checking.
/-- Tensor two already normalized maps to append one root factor.

Source: smooth-purity transport, Step 2, tensoring the root projections in order.
(blueprint: lem-pur-tate-tensor-generator-step)

Proof: for positive degree, the finite etale twist of degree d+2 is by definition
the tensor of its degree d+1 twist with the first root line. The comparison
pullback is strong monoidal, with pure-section formula given by the comparison
adjunction. Realization along `scalars` preserves this tensor: constant sections
are locally all sections of the constant coefficient sheaf, so the fixed-scalar
and sheaf-scalar balancing relations agree after sheafification. Apply f tensor g
after these comparisons. Scalar extension along the completed coefficient
projection is strong monoidal. In its target, contract the unit factor in
`integralLine 1` by the left unitor before appending the final root factor to
`integralLine (d+1)`. This defines the required morphism without choosing any
roots. For the generator equation, split each Fin(d+2) tuple into castSucc and
last. Place a in the first factor and 1 in the last factor; the defining finite
power generator is exactly that pure tensor. The hypotheses for f and g apply
to these subtuples. The normalized tensor constraints carry their two values to
scalars(a) tensor the integral generator of degree d+2. This is its defining
recursion. The argument is balanced in arbitrary scalars and is natural under
restriction; neither invertibility of ell nor a choice of root basis is needed.
The positive-degree restriction avoids identifying the separate finite degree-one
root-line definition with a tensor product containing a degree-zero factor. -/
theorem tateTensorQuotient_generator_step
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime] (n d : ℕ)
    (f : (realization T ell n).obj (finiteSheaf T ell n (d + 1)) ⟶
      quotientLine T ell n (d + 1))
    (g : (realization T ell n).obj (finiteSheaf T ell n 1) ⟶ quotientLine T ell n 1)
    (hf : GeneratorCompatible T ell n (d + 1) f)
    (hg : GeneratorCompatible T ell n 1 g) :
    ∃ h : (realization T ell n).obj (finiteSheaf T ell n (d + 2)) ⟶
      quotientLine T ell n (d + 2),
      GeneratorCompatible T ell n (d + 2) h := by
  let A := coefficient.{u} ell (n + 1)
  let R := pbcAdicCompletion T (datum.{u} ell)
  let S := (pbcAdicRings T (datum.{u} ell)).obj (op n)
  let φ := pbcAdicProjection T (datum.{u} ell) n
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let M := finiteEtaleTateTwist T (ell ^ (n + 1)) A (CharP.cast_eq_zero _ _) (d + 1)
  let N := finiteEtaleTateTwist T (ell ^ (n + 1)) A (CharP.cast_eq_zero _ _) 1
  let L := integralLine T ell (d + 1)
  let K := integralLine T ell 1
  let H := integralLine T ell (d + 2)
  obtain ⟨t, ht⟩ := realization_tensor T ell n (F.obj M) (F.obj N)
  obtain ⟨D⟩ := SheafOfModules.scalarExtension_constraint_coherence
    (J := ProEt.topology T) R S φ
  let c : L ⊗ K ⟶ H := 𝟙 L ⊗ₘ contractRoot T ell
  let fM : (realization T ell n).obj (F.obj M) ⟶ (pbcExtend φ).obj L := f
  let gN : (realization T ell n).obj (F.obj N) ⟶ (pbcExtend φ).obj K := g
  let h := (realization T ell n).map (Functor.OplaxMonoidal.δ F M N) ≫ t ≫
    (fM ⊗ₘ gN) ≫ ((extensionIso T φ L).hom ⊗ₘ (extensionIso T φ K).hom) ≫
    (D.tensorIso L K).inv ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ (L ⊗ K) c ≫
    (extensionIso T φ H).inv
  refine ⟨h, ?_⟩
  intro U W v a z x hx
  let z₁ : Fin (d + 1) → _ := fun i ↦ z i.castSucc
  let z₂ : Fin 1 → _ := fun _ ↦ z (Fin.last (d + 1))
  let x₁ : Fin (d + 1) → _ := fun i ↦ x i.castSucc
  let x₂ : Fin 1 → _ := fun _ ↦ x (Fin.last (d + 1))
  let y := (F.obj M).obj.map v.op
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
      (finiteTateEtalePowerGenerator T A (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) U a (d + 1) z₁))
  let w := (F.obj N).obj.map v.op
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app N).hom.app U
      (finiteTateEtalePowerGenerator T A (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) U 1 1 z₂))
  have hy := hf U W v a z₁ x₁ (fun i ↦ hx i.castSucc)
  have hw := hg U W v 1 z₂ x₂ (fun _ ↦ hx (Fin.last (d + 1)))
  simp only [one_smul, id_eq] at hy hw ⊢
  have hc : c.val.app W
      (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1} R L K W
        (integralGenerator T ell W (d + 1) x₁) (integralGenerator T ell W 1 x₂)) =
      integralGenerator T ell W (d + 2) x := by
    have hn := SheafOfModules.pure_natural R (𝟙 L) (contractRoot T ell) W
      (integralGenerator T ell W (d + 1) x₁) (integralGenerator T ell W 1 x₂)
    have hu := congrArg
      (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
        R L (integralRoot T ell) W (integralGenerator T ell W (d + 1) x₁))
      (contractRoot_generator T ell W x₂)
    simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hn
    exact hn.trans hu
  let b := (F.obj (M ⊗ N)).obj.map v.op
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
      (M ⊗ N)).hom.app U
        (finiteTateEtalePowerGenerator T A (ell ^ (n + 1))
          (CharP.cast_eq_zero _ _) U a (d + 2) z))
  let s := (toSheafify (ProEt.topology T)
    ((F.obj (M ⊗ N)).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W b
  let y₀ := (toSheafify (ProEt.topology T)
    ((F.obj M).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W y
  let w₀ := (toSheafify (ProEt.topology T)
    ((F.obj N).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W w
  let l := integralGenerator T ell W (d + 1) x₁
  let k := integralGenerator T ell W 1 x₂
  let j := integralGenerator T ell W (d + 2) x
  let aS := ((scalars T ell n).app W).hom a
  let bS := ((scalars T ell n).app W).hom 1
  let p₀ := SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
    S ((realization T ell n).obj (F.obj M)) ((realization T ell n).obj (F.obj N)) W y₀ w₀
  let p₁ := SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
    S ((pbcExtend φ).obj L) ((pbcExtend φ).obj K) W
      (pbcTensorSection φ L W aS l) (pbcTensorSection φ K W bS k)
  let p₂ := SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
    S (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ L)
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ K) W
      (SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1} φ L W l aS)
      (SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1} φ K W k bS)
  let p₃ := SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
    R L K W l k
  let p₄ := SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1}
    φ (L ⊗ K) W p₃ aS
  let p₅ := SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1} φ H W j aS
  let q₁ := (fM ⊗ₘ gN).val.app W
  let q₂ := ((extensionIso T φ L).hom ⊗ₘ (extensionIso T φ K).hom).val.app W
  let q₃ := (D.tensorIso L K).inv.val.app W
  let q₄ := (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ (L ⊗ K) c).val.app W
  let q₅ := (extensionIso T φ H).inv.val.app W
  have hp : (Functor.OplaxMonoidal.δ F M N).hom.app W b =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} A)) (F.obj M) (F.obj N)).app W (y ⊗ₜ[A] w) :=
    (comparison_pure_sections A T).1 M N U W v
      (finiteTateEtalePowerGenerator T A (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) U a (d + 1) z₁)
      (finiteTateEtalePowerGenerator T A (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) U 1 1 z₂)
  have hm := realization_map_section T ell n (Functor.OplaxMonoidal.δ F M N) W b
  have hm' := hm.trans (congrArg
    ((toSheafify (ProEt.topology T)
      ((F.obj M ⊗ F.obj N).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W) hp)
  have hstart : t.val.app W
      (((realization T ell n).map (Functor.OplaxMonoidal.δ F M N)).val.app W s) = p₀ :=
    (congrArg (t.val.app W) hm').trans (ht W y w)
  have hfy : fM.val.app W y₀ = pbcTensorSection φ L W aS l := hy
  have hgw : gN.val.app W w₀ = pbcTensorSection φ K W bS k := hw
  have hfg : q₁ p₀ = p₁ :=
    (SheafOfModules.pure_natural S fM gN W y₀ w₀).trans
      (congrArg₂
        (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
          S ((pbcExtend φ).obj L) ((pbcExtend φ).obj K) W) hfy hgw)
  have hext : q₂ p₁ = p₂ :=
    (SheafOfModules.pure_natural S (extensionIso T φ L).hom (extensionIso T φ K).hom W
      (pbcTensorSection φ L W aS l) (pbcTensorSection φ K W bS k)).trans
        (congrArg₂
          (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
            S (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ L)
              (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ K) W)
          (extensionIso_section T φ L W aS l) (extensionIso_section T φ K W bS k))
  have hab : aS * bS = aS := by simp only [aS, bS, map_one, mul_one]
  have hinv : q₃ p₂ = p₄ :=
    (D.tensor_inv L K W l k aS bS).trans
      (congrArg (fun v ↦ SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1}
        φ (L ⊗ K) W p₃ v) hab)
  have hchange : q₄ p₄ = p₅ :=
    (SheafOfModules.extension_map_tmul φ c W p₃ aS).trans
      (congrArg (fun v ↦ SheafOfModules.scalarExtensionConstraintTmul.{u + 1, u, u + 1}
        φ H W v aS) hc)
  have hfinal : q₅ p₅ = pbcTensorSection φ H W aS j :=
    extensionIso_inv_section T φ H W aS j
  change h.val.app W s = pbcTensorSection φ H W aS j
  calc
    h.val.app W s = q₅ (q₄ (q₃ (q₂ (q₁ p₀)))) :=
      congrArg (fun v ↦ q₅ (q₄ (q₃ (q₂ (q₁ v))))) hstart
    _ = q₅ (q₄ (q₃ (q₂ p₁))) := congrArg (fun v ↦ q₅ (q₄ (q₃ (q₂ v)))) hfg
    _ = q₅ (q₄ (q₃ p₂)) := congrArg (fun v ↦ q₅ (q₄ (q₃ v))) hext
    _ = q₅ (q₄ p₄) := congrArg (fun v ↦ q₅ (q₄ v)) hinv
    _ = q₅ p₅ := congrArg (fun v ↦ q₅ v) hchange
    _ = pbcTensorSection φ H W aS j := hfinal

end AlgebraicGeometry.Scheme.PurityIntegralTower
