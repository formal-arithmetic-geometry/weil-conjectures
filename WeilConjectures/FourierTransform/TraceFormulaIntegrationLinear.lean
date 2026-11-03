/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceFormulaIntegrationNative
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Linearity of finite-coefficient integration

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-d-integral/lem-trf-integration-linear.md and
lem-trf-integration-linear.proof.md
(blueprint: lem-trf-integration-linear).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

private instance pointAdditive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  let : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem scalar_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (a : MonObj.Γ Λ) :
    (MonObj.Γ.mapFunctor (upperStarFromPoint Y) a).hom ≫ condensedPushforwardHom Λ f =
      Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} f) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          (MonObj.Γ.mapFunctor (upperStarFromPoint X) a).hom := by
  simp only [MonObj.Γ.mapFunctor_hom, condensedPushforwardHom,
    Adjunction.unitAlgHom, Category.assoc]
  exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).ε_comp_map_comp_unit_app_comp_map
    (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom a.hom

set_option maxHeartbeats 1600000 in
-- Compare the induced actions through the module-object coefficient map.
private theorem lowerLinearOfScalars
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (A : Type) [CommRing A] (φ : A →+* MonObj.Γ Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := Mod.linearOfRingHom ((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp φ)
    let := Mod.linearOfRingHom ((MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp φ)
    (lowerStar Λ f).Linear A := by
  dsimp only
  exact Mod.linear_mapMod_comp_comap (ProEtale.lowerStar Ab.{u + 1} f)
    (condensedPushforwardHom Λ f)
    ((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp φ)
    ((MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp φ)
    (fun a ↦ scalar_mate Λ f (φ a))

private instance lowerLinear (A : Type) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar (FiniteRingTrace.coefficient A) f).Linear A := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact lowerLinearOfScalars (FiniteRingTrace.coefficient A) A
    (Profinite.continuousMapConstRingHom A) f

private instance upperLinear (A : Type) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (FiniteRingTrace.coefficient A) f).Linear A :=
  (upperStarLowerStarAdjunction (FiniteRingTrace.coefficient A) f).left_adjoint_linear

private instance openLinear (A : Type) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (openImmersionLowerShriek (FiniteRingTrace.coefficient A) f).Linear A :=
  (openImmersionLowerShriekUpperStarAdjunction
    (FiniteRingTrace.coefficient A) f).left_adjoint_linear

private instance supportLinear (A : Type) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (rightDerivedLowerShriekOfCompactification (FiniteRingTrace.coefficient A) c).Linear A :=
  inferInstanceAs (((openImmersionLowerShriek
    (FiniteRingTrace.coefficient A) c.i).mapDerivedCategory ⋙
      (lowerStar (FiniteRingTrace.coefficient A) c.g).rightDerivedFunctor).Linear A)

private theorem scalar_map (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) (a : A) :
    (DerivedCategory.singleFunctor _ 0).map
      (Mod.regularEndRingHom (FiniteRingTrace.scalarRingHom A (Spec (.of D.k)) a)) =
      a • 𝟙 (traceFormulaIntegrationConstant A (Spec (.of D.k))) := by
  rw [Mod.regularEndRingHom_eq_smul, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id]
  rfl

private theorem scalar_surjective (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) :
    Function.Surjective (fun a : A ↦
      a • 𝟙 (traceFormulaIntegrationConstant A (Spec (.of D.k)))) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let F := upperStarFromPoint (Spec (.of D.k))
  let R := FiniteRingTrace.coefficient A
  let S := DerivedCategory.singleFunctor
    (Mod (Sheaf (ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
      (condensedRingObj R (Spec (.of D.k)))) 0
  have h := F.bijective_regularEndRingHom_comp_mapFunctor R
    (Functor.FullyFaithful.ofFullyFaithful (F.mapMod R))
  intro v
  obtain ⟨m, hm⟩ := S.map_surjective v
  obtain ⟨b, hb⟩ := (h.2.comp (Profinite.continuousMapConstRingHom_surjective A)) m
  refine ⟨b, ?_⟩
  dsimp only
  rw [← scalar_map A D b]
  change S.map _ = v
  rw [show Mod.regularEndRingHom (FiniteRingTrace.scalarRingHom A (Spec (.of D.k)) b) = m
    from hb]
  exact hm

private theorem scalar_on_scalar (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) (a : A) :
    traceFormulaIntegrationScalar A D
      (a • 𝟙 (traceFormulaIntegrationConstant A (Spec (.of D.k)))) = a := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  rw [← scalar_map A D a]
  unfold traceFormulaIntegrationScalar
  simp only [Functor.preimage_map, Mod.regularEndRingHom_apply,
    Mod.one_comp_regularLift_regular, FiniteRingTrace.scalarRingHom,
    RingHom.comp_apply, MonObj.Γ.mapFunctor_hom,
    Functor.Monoidal.εIso_inv, Functor.Monoidal.η_ε_assoc, Functor.preimage_map]
  change (Sheaf.unitHomEval (Profinite.of PUnit.{u + 1})
    (Profinite.continuousMapConstRingHom A a).hom).down PUnit.unit = a
  have h := Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u})
    (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapRingSheaf.{u} A)
    (Profinite.continuousMapConstSectionRingHom.{u} A) (fun _ _ ↦ rfl) a
  exact congrArg (fun x ↦ x.down PUnit.unit) h

private theorem scalar_linear (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u})
    (v w : End (traceFormulaIntegrationConstant A (Spec (.of D.k)))) (a : A) :
    traceFormulaIntegrationScalar A D (v + a • w) =
      traceFormulaIntegrationScalar A D v + a * traceFormulaIntegrationScalar A D w := by
  obtain ⟨b, rfl⟩ := scalar_surjective A D v
  obtain ⟨c, rfl⟩ := scalar_surjective A D w
  rw [smul_smul, ← add_smul, scalar_on_scalar, scalar_on_scalar, scalar_on_scalar]

set_option maxHeartbeats 1600000 in
-- The selected constructible adjunction has several dependent full-subcategory instances.
private theorem endomorphism_linear (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (Y : Over (Spec (.of D.k))) [IsProper Y.hom]
    (tau tau' : traceFormulaIntegrationConstant A Y.left ⟶
      FiniteRingTrace.dualizingComplex A D ell hell hA Y) (a : A) :
    traceFormulaIntegrationEndomorphism A D ell hell hA Y (tau + a • tau') =
      traceFormulaIntegrationEndomorphism A D ell hell hA Y tau +
        a • traceFormulaIntegrationEndomorphism A D ell hell hA Y tau' := by
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  let : QuasiCompact (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  let : IsSeparated (Over.mk (𝟙 (Spec (.of D.k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  let d := traceFormulaIntegrationAdmissible A D ell hell hA Y
  let P := (constantModelBoundedConstructible (FiniteRingTrace.coefficient A)
    (Spec (.of D.k)) ⊓ DerivedCategory.finiteTorAmplitude _)
  let F := d.lower ⋙ P.ι
  have hF : F = (constantModelBoundedConstructible (FiniteRingTrace.coefficient A)
      Y.left ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
      rightDerivedLowerShriekOfCompactification (FiniteRingTrace.coefficient A)
        (compactificationOverField (Over.mkIdTerminal.from Y)) := d.lower_eq
  let : F.Additive := by rw [hF]; infer_instance
  let : F.Linear A := by rw [hF]; infer_instance
  let U := traceFormulaIntegrationUnit A Y.left
  let V := traceFormulaIntegrationUnit A (Spec (.of D.k))
  let t : U ⟶ d.right.obj V :=
    ⟨tau ≫ (traceFormulaIntegrationDualizingIso A D ell hell hA Y).inv⟩
  let t' : U ⟶ d.right.obj V :=
    ⟨tau' ≫ (traceFormulaIntegrationDualizingIso A D ell hell hA Y).inv⟩
  have ht : (⟨(tau + a • tau') ≫
      (traceFormulaIntegrationDualizingIso A D ell hell hA Y).inv⟩ : U ⟶ d.right.obj V) =
      t + a • t' := by
    ext
    simp only [t, t', Preadditive.add_comp, Linear.smul_comp]
    rfl
  have hmap : (d.lower.map (t + a • t')).hom =
      (d.lower.map t).hom + a • (d.lower.map t').hom := by
    change F.map (t + a • t') = F.map t + a • F.map t'
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_smul]
  unfold traceFormulaIntegrationEndomorphism
  dsimp only
  rw [ht, hmap]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul]
  rfl

/-- Integration is A-linear on every ambient morphism from A_beta to omega_beta,A.
The finite-field datum, prime distinct from p, finite extension E and positive quotient
level supply precisely the standing coefficient conventions. Properness supplies finite
type and separation; the current finite-primary theorem supplies the constructible
exceptional adjunction, including its specified counit. Scalar multiplication is the
standard linear structure on the native category FiniteRingTrace.Ambient.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-d-integral/lem-trf-integration-linear.md
(blueprint: lem-trf-integration-linear).

Proof: write F = RΓ(s,Ra_! -). Properness identifies the first fixed arrow with the
ordinary adjunction unit followed by the proper comparison; the last fixed arrow is the
specified exceptional counit followed by exact point sections. The finite-coefficient
compact-support functor is A-linear, so F(tau + a tau') = F(tau) + a F(tau'). Compose
with these two fixed arrows in D(A), distributing composition by its A-bilinearity.
Reading H^0 of the resulting endomorphism at 1 preserves addition and coefficient
multiplication and gives exactly the displayed scalar identity. -/
theorem traceFormulaIntegration_linear (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : IntermediateField (Padic ell) (PadicAlgCl ell))
    [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Over (Spec (.of D.k))) [IsProper Y.hom] :
    let A := Padic.coefficientExtensionRing ell E n
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    let hA := FiniteRingTrace.coefficientExtensionRing_primary ell E n hn
    ∀ (tau tau' : traceFormulaIntegrationConstant A Y.left ⟶
        FiniteRingTrace.dualizingComplex A D ell hell hA Y) (a : A),
      traceFormulaIntegration D ell hell E n hn Y (tau + a • tau') =
        traceFormulaIntegration D ell hell E n hn Y tau +
          a * traceFormulaIntegration D ell hell E n hn Y tau'  := by
  let A := Padic.coefficientExtensionRing ell E n
  let : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  let hA := FiniteRingTrace.coefficientExtensionRing_primary ell E n hn
  change ∀ (tau tau' : traceFormulaIntegrationConstant A Y.left ⟶
    FiniteRingTrace.dualizingComplex A D ell hell hA Y) (a : A), _
  intro tau tau' a
  change traceFormulaIntegrationScalar A D
    (traceFormulaIntegrationEndomorphism A D ell hell hA Y (tau + a • tau')) = _
  rw [endomorphism_linear, scalar_linear]
  rfl

end WeilConjectures
