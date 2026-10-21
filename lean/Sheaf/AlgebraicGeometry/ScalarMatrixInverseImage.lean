/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import Sheaf.Paper.RegularExtensionComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Inverse image of finite scalar matrices

Source: blueprint main-20261015, proper base change unbounded pullback proof,
paragraph “Constructible complexes”, local coefficient models on strata
(blueprint: lem-sfb-scalar-matrix-inverse-image).

The comparisons below use the canonical coefficient morphism and the regular-module
scalar-extension comparison, followed by the finite biproduct comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {V U : Scheme.{u}} (h : V ⟶ U)

/-- The regular-module comparison induced by the canonical coefficient map α_h.
First transport the regular module along the monoidal inverse image, and then use
extension of scalars along α_h. The forward map sends b ⊗ x to b α_h(x).
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”;
the explicit regular-module construction is step 2 of the node proof
(blueprint: lem-sfb-scalar-matrix-inverse-image). -/
noncomputable def scalarMatrixRegularPullbackIso :
    (CondensedRing.upperStar Λ h).obj (Mod.regular (condensedRingObj Λ U)) ≅
      Mod.regular (condensedRingObj Λ V) :=
  (Mod.extendScalars (condensedPullbackHom Λ h)).mapIso
      ((upperStar Ab.{u + 1} h).mapModUnitIso (R := condensedRingObj Λ U)).symm ≪≫
    Mod.regularExtensionIso (condensedPullbackHom Λ h)

/-- The canonical finite-coproduct extension of the regular-module comparison.
This definition also includes rank zero, using the empty biproduct comparison.
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”;
the finite-coproduct construction is step 3 of the node proof
(blueprint: lem-sfb-scalar-matrix-inverse-image). -/
noncomputable def scalarMatrixFreePullbackIso (r : ℕ) :
    (CondensedRing.upperStar Λ h).obj (Mod.finiteFree (condensedRingObj Λ U) r) ≅
      Mod.finiteFree (condensedRingObj Λ V) r :=
  (CondensedRing.upperStar Λ h).mapBiproduct
      (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) ≪≫
    biproduct.mapIso (fun _ ↦ scalarMatrixRegularPullbackIso Λ h)

set_option backward.isDefEq.respectTransparency.types false

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem scalarSection_image (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    scalarSection Λ X a = Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map
        (Functor.LaxMonoidal.ε
            (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
          (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
          (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
            Profinite.isTerminalPUnit).counit.app Λ) := by
  simp only [scalarSection, scalarCoefficientHom, Functor.map_comp]
  rfl

omit [IsCommMonObj Λ] in
private theorem scalarEndomorphism_image (X : Scheme.{u})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (Mod.regularLift (Mod.regular (condensedRingObj Λ X)) (scalarSection Λ X a)).hom =
      (upperStarFromPoint X).map
        (Mod.regularLift (Mod.regular Λ)
          (Functor.LaxMonoidal.ε
              (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
            (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
            (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
              Profinite.isTerminalPUnit).counit.app Λ)).hom := by
  let P := upperStarFromPoint X
  let d := Functor.LaxMonoidal.ε
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ
  let e : (P.mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) := Mod.isoMk (Iso.refl _) (by simp)
  have hm : (P.mapMod Λ).map (Mod.regularLift (Mod.regular Λ) d) ≫ e.hom =
      e.hom ≫ Mod.regularLift (Mod.regular (condensedRingObj Λ X))
        (scalarSection Λ X a) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ _ ⟶ P.obj Λ) ≫
        (P.map (Mod.regularLift (Mod.regular Λ) d).hom ≫ 𝟙 _) =
      (MonObj.one : 𝟙_ _ ⟶ P.obj Λ) ≫ (𝟙 _ ≫ _)
    simp only [Category.comp_id, Category.id_comp]
    rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
      ← P.map_comp, Mod.one_comp_regularLift, scalarSection_image]
  have ht := congrArg Mod.Hom.hom hm
  change P.map (Mod.regularLift (Mod.regular Λ) d).hom ≫ 𝟙 _ =
    𝟙 _ ≫ (Mod.regularLift (Mod.regular (condensedRingObj Λ X))
      (scalarSection Λ X a)).hom at ht
  simpa only [Category.comp_id, Category.id_comp] using ht.symm

omit [IsCommMonObj Λ] in
private theorem scalarEndomorphism_naturality
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (upperStar Ab.{u + 1} h).map
        (Mod.regularLift (Mod.regular (condensedRingObj Λ U)) (scalarSection Λ U a)).hom ≫
      condensedPullbackHom Λ h =
    condensedPullbackHom Λ h ≫
      (Mod.regularLift (Mod.regular (condensedRingObj Λ V)) (scalarSection Λ V a)).hom := by
  rw [scalarEndomorphism_image, scalarEndomorphism_image]
  exact (upperStarFromPointComp h).hom.naturality (X := Λ) (Y := Λ) _

private theorem scalarRegular_pullback
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) :
    (CondensedRing.upperStar Λ h).map
        (Mod.regularLift (Mod.regular (condensedRingObj Λ U)) (scalarSection Λ U a)) ≫
      (scalarMatrixRegularPullbackIso Λ h).hom =
    (scalarMatrixRegularPullbackIso Λ h).hom ≫
      Mod.regularLift (Mod.regular (condensedRingObj Λ V)) (scalarSection Λ V a) := by
  let F := upperStar Ab.{u + 1} h
  let R := condensedRingObj Λ U
  let S := condensedRingObj Λ V
  let φ := condensedPullbackHom Λ h
  let e : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by simp)
  have heq : (F.mapModUnitIso (R := R)).inv = e.hom := by
    apply (cancel_mono (F.mapModUnitIso (R := R)).hom).mp
    rw [Iso.inv_hom_id]
    apply Mod.hom_ext
    change 𝟙 (F.obj R) = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
  let f := Mod.regularLift (Mod.regular R) (scalarSection Λ U a)
  let q := Mod.regularLift (Mod.regular S) (scalarSection Λ V a)
  let p := e.inv ≫ (F.mapMod R).map f ≫ e.hom
  have hc : p.hom ≫ φ = φ ≫ q.hom := by
    change (𝟙 _ ≫ F.map f.hom ≫ 𝟙 _) ≫ φ = φ ≫ q.hom
    simp only [Category.id_comp, Category.comp_id]
    exact scalarEndomorphism_naturality Λ h a
  have he := Mod.regularExtensionIso_naturality φ p q hc
  have he' := congrArg (fun k ↦ (Mod.extendScalars φ).map e.hom ≫ k) he
  dsimp only [CondensedRing.upperStar, scalarMatrixRegularPullbackIso, Functor.comp_map,
    Iso.trans_hom, Functor.mapIso_hom]
  change (Mod.extendScalars φ).map ((F.mapMod R).map f) ≫
      (Mod.extendScalars φ).map (F.mapModUnitIso (R := R)).inv ≫
        (Mod.regularExtensionIso φ).hom =
    (Mod.extendScalars φ).map (F.mapModUnitIso (R := R)).inv ≫
      (Mod.regularExtensionIso φ).hom ≫ q
  rw [heq]
  simpa only [p, Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc] using he'

/-- Pullback preserves matrices of the same condensed scalars and their cokernels.
The entries are maps ℤ → Λ(*), equivalently elements of the scalar ring Λ(*).
As in `scalarMatrix`, the first index is the source column and the second the target row.
Source: blueprint proper base change unbounded pullback proof, “Constructible complexes”,
local coefficient models on strata (blueprint: lem-sfb-scalar-matrix-inverse-image).

Proof in words (the six steps of the node proof):
1. Naturality of `upperStarFromPointComp` at multiplication by a scalar, together with
   the transported unit and multiplication of the coefficient ring, identifies the
   inverse images of the canonical scalar endomorphisms. This uses the scalar maps of
   `det-def-sfb-constructible-local-model`, rather than arbitrary coefficient sections.
2. Transport identifies the inverse image of the regular module with the regular module
   over the inverse-image ring. The mixed-bimodule right unitor identifies its extension
   along α_h with Λ_V, by b ⊗ x ↦ b α_h(x), with inverse b ↦ b ⊗ 1.
3. The module adjunction makes pullback preserve finite coproducts and coequalizers.
   Its zero-object comparison gives preservation of zero maps. Extending the regular
   comparison to biproducts gives the displayed finite-free comparisons, compatible
   with injections and projections, including the empty biproduct.
4. Precompose the two regular-module scalar endomorphism composites with the balancing
   coequalizer projection. Step 1 and associativity and commutativity of multiplication
   identify them; uniqueness of coequalizer descent proves equality.
5. Precompose with each transported input injection and postcompose with each output
   projection. The matrix entries reduce the square to step 4. The coproduct and product
   universal properties give the matrix equation, also when either rank is zero.
6. Pullback preserves the cokernel, a coequalizer of the matrix and zero. The matrix
   square induces maps in both directions between the two cokernels. Their defining
   projection equations make both composites identities by cokernel uniqueness. The
   forward projection equation is exactly the compatibility stated below. -/
theorem scalarMatrix_inverseImage {m n : ℕ}
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
        (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A ∧
    ∃ e : (CondensedRing.upperStar Λ h).obj (cokernel (scalarMatrix Λ U A)) ≅
        cokernel (scalarMatrix Λ V A),
      (CondensedRing.upperStar Λ h).map (cokernel.π (scalarMatrix Λ U A)) ≫ e.hom =
        (scalarMatrixFreePullbackIso Λ h n).hom ≫ cokernel.π (scalarMatrix Λ V A) := by
  have hm : (scalarMatrixFreePullbackIso Λ h m).inv ≫
      (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
      (scalarMatrixFreePullbackIso Λ h n).hom = scalarMatrix Λ V A := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [scalarMatrixFreePullbackIso, Iso.trans_inv, Iso.trans_hom,
      biproduct.mapIso_inv, biproduct.mapIso_hom, Category.assoc,
      biproduct.ι_map_assoc, Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
      biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π,
      scalarMatrix, biproduct.matrix]
    erw [biproduct.lift_π_assoc]
    simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc,
      biproduct.lift_π]
    simp only [Category.assoc]
    rw [scalarRegular_pullback, Iso.inv_hom_id_assoc]
  have hs : (CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A) ≫
      (scalarMatrixFreePullbackIso Λ h n).hom =
      (scalarMatrixFreePullbackIso Λ h m).hom ≫ scalarMatrix Λ V A := by
    rw [← hm, Iso.hom_inv_id_assoc]
  refine ⟨hs, ?_⟩
  let e := PreservesCokernel.iso (CondensedRing.upperStar Λ h) (scalarMatrix Λ U A) ≪≫
    cokernel.mapIso ((CondensedRing.upperStar Λ h).map (scalarMatrix Λ U A)) (scalarMatrix Λ V A)
      (scalarMatrixFreePullbackIso Λ h m) (scalarMatrixFreePullbackIso Λ h n) hs
  refine ⟨e, ?_⟩
  simp [e]

end AlgebraicGeometry.ProEtale

#print axioms AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage
