/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

public import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Coefficient and symmetry transport for strict-local sections
Source: Stacks Project, Tags 03D3, 03D7, and 03Q9.
(blueprint: lem-weil-pbc-strict-local-module-sections-set-transport)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The canonical equivalence of strict-local terminal sections after forgetting module
coefficients and interchanging the two pullback factors.
Source: Stacks Project, Tags 03D3, 03D7, and 03Q9.
(blueprint: def-weil-pbc-strict-local-module-sections-set-equiv).
The coefficient comparison, composition of inverse images, restriction along the
pullback symmetry, and terminal/global section comparisons are all actual isomorphisms.
The composition comparison is determined by its unit identity and fixed-sheaf uniqueness.
No existence theorem about sections or stalks is used to choose the equivalence. -/
noncomputable def strictLocalModuleSectionsSetEquiv
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
    ((Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F)) ≃
      ((Scheme.etaleSetPullback
        (pullback.snd (Scheme.strictHenselizationStructuralMap s) f)).obj H).obj.obj
          (op (Scheme.Etale.mk (𝟙 _))) := by
  classical
  let ρ := Scheme.strictHenselizationStructuralMap s
  let A := pullback f ρ
  let B := pullback ρ f
  let g : A ⟶ X := pullback.fst f ρ
  let h : B ⟶ X := pullback.snd ρ f
  let σ : A ⟶ B := (pullbackSymmetry f ρ).hom
  have hσ : σ ≫ h = g := pullbackSymmetry_hom_comp_snd f ρ
  let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
  let M := (upperStar (ModuleCat.{u + 1} Λ) g).obj F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g) (Type (u + 1))
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (A.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let q := (adj.homEquiv H
    ((sheafCompose A.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj M)).symm
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F))
  have : IsIso q := isIso_upperStar_forget_comparison Λ g F
  let c := Classical.choose (etaleSetInverseImageCompositionUnits.{u}).2.2
  let r := Classical.choose (etaleSetInverseImageRestriction σ)
  let T := Scheme.Etale.mk (𝟙 A)
  let T' := Scheme.Etale.mk (𝟙 B)
  let d : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale σ)).obj T ≅
      T' := MorphismProperty.Over.isoMk (pullbackSymmetry f ρ) (by
        change σ ≫ 𝟙 B = 𝟙 A ≫ σ
        exact (Category.comp_id σ).trans (Category.id_comp σ).symm)
  let t := IsTerminal.isTerminalOfObj
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ A) T Over.mkIdTerminal
  let eΓ := (Sheaf.ΓNatIsoSheafSections A.smallEtaleTopology
    (ModuleCat.{u + 1} Λ) t).app M
  let V := sheafToPresheaf A.smallEtaleTopology (Type (u + 1))
  let eq := (V.mapIso (asIso q)).app (op T)
  let eg : (Scheme.etaleSetPullback (σ ≫ h)).obj H ≅
      (Scheme.etaleSetPullback g).obj H :=
    eqToIso (congrArg (fun k ↦ (Scheme.etaleSetPullback k).obj H) hσ)
  let ec := (V.mapIso (((c X B A h σ).app H) ≪≫ eg)).app (op T)
  let er := (V.mapIso (r.app ((Scheme.etaleSetPullback h).obj H))).app (op T)
  let ed := ((Scheme.etaleSetPullback h).obj H).obj.mapIso d.op
  let e0 := (forget (ModuleCat.{u + 1} Λ)).mapIso eΓ
  let e1 := e0 ≪≫ eq.symm ≪≫ ec.symm ≪≫ er ≪≫ ed.symm
  exact e1.toEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting coefficients and interchanging the two pullback factors identifies terminal
sections, compatibly with restriction of a section from any affine pointed neighbourhood.
Source: Stacks Project, Tags 03D3 and 03D7 (inverse images), and Tag 03Q9 (degree zero).
(blueprint: lem-weil-pbc-strict-local-module-sections-set-transport).

Proof: Put S = Spec of the strict henselization, A = X ×_Y S, B = S ×_Y X,
g = A → X, h = B → X, and σ : A → B the pullback symmetry, so σ ≫ h = g.
Write H for the underlying set sheaf and K = h⁻¹H. Expand the equivalence in
strictLocalModuleSectionsSetEquiv. Its global-section comparison cancels the inverse
comparison at the end of the displayed module restriction map. Let q : g⁻¹H → U(g*F)
be the coefficient comparison. By Adjunction.homEquiv_unit, the forgotten module unit
is the set unit followed by q. Naturality of q⁻¹ therefore sends the restricted module
section to the g-unit section restricted to the terminal object of A.
The chosen composition isomorphism c : σ⁻¹(h⁻¹H) ≅ (σ ≫ h)⁻¹H satisfies its unit
formula by Classical.choose_spec etaleSetInverseImageCompositionUnits. After transport
along σ ≫ h = g, naturality of c⁻¹ sends that restricted g-unit section to the iterated
h-unit and σ-unit section, restricted along the terminal-to-iterated-pullback map.
The chosen restriction comparison r : σ⁻¹K ≅ K restricted along σ satisfies the unit
formula of Classical.choose_spec (etaleSetInverseImageRestriction σ). Use its naturality
to move the preceding restriction past r; its unit formula replaces the σ-unit by
restriction along the fibre-product projection. Finally the inverse sheaf map at the
terminal-object isomorphism induced by σ transports evaluation from A → B to B → B.
The composite restriction map is strictHenselizationSectionMap f s j: compare both
projections using pullback.lift_fst, pullback.lift_snd, the pullbackComp projection
identities, and pullbackSymmetry_hom_comp_snd. Functoriality gives the displayed equation.
No step uses qcqs, nonempty schemes, or nonzero coefficients. -/
theorem strictLocalModuleSections_set_transport
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let H := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj F
    ∀ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s))
        (z : F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)))),
        strictLocalModuleSectionsSetEquiv Λ f s F (ConcreteCategory.hom (
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictHenselizationStructuralMap s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) z) =
          ((Scheme.etaleSetPullback
            (pullback.snd (Scheme.strictHenselizationStructuralMap s) f)).obj H).obj.map
              (Scheme.strictHenselizationSectionMap f s j).op
                (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                  (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
                    (pullback.snd (Scheme.strictHenselizationStructuralMap s) f))
                  (Type (u + 1)) (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
                ((pullback (Scheme.strictHenselizationStructuralMap s) f).smallGrothendieckTopology
                    @AlgebraicGeometry.Etale)).unit.app H).hom.app
                      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
                        ((equivSmallModel.{u}
                          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) z)
    := by sorry

end AlgebraicGeometry.Etale
