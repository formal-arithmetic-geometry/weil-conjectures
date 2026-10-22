module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction
public import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.Paper.StrictHenselizationPointedMap
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.IntegralStrictHenselianGeometricFibreSections

/-! # Integral strict-local fibre comparison

Source: Stacks Project, Tag 0EYP, using Tags 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Sections on the integral strict-local pullback and on the geometric fibre agree,
compatibly with the restrictions from each affine pointed neighbourhood. This compares
only two schemes; it does not assert that strict-local sections have neighbourhood
representatives, which is the separate qcqs continuity theorem.

Source: Stacks Project, Tag 0EYP, using Tags 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-strict-local-fibre-comparison).

Proof: the maps of the geometric point to its affine pointed neighbourhoods are
compatible. The limit property of strictHenselizationCone constructs their unique
map t to Spec A, the strict henselization. Its composite with the structural map is s.
The pullback universal property constructs q from X' to Z = X times_Y Spec A, with
projections g' and f' followed by t. Integrality makes Z affine, say Spec B, and B is
integral over A. The local-structure theorem makes A strictly henselian. The ring
map A to Omega factors through its separably closed residue field k: in each pointed
etale neighbourhood it induces the selected residue embedding, so its kernel is the
maximal ideal m. By Tag 09XK, (B,mB) is henselian. Apply the henselian degree-zero
comparison to the proper identity of Spec B and the ideal mB. Restriction from Spec B
to Spec(B/mB) is invertible. Tag 0A3I makes restriction from this k-scheme to its
base change to Omega invertible on underlying sets; the canonical module/set
inverse-image comparison transports this assertion to modules. Pullback pasting
identifies the latter scheme with X'. Compose these restrictions, the inverse-image
composition isomorphism, and evaluation at the identity etale object to obtain e.
For each j, the limit-leg equation for t identifies its restriction with the selected
point of that neighbourhood. The two projections of the resulting iterated pullback
lift are therefore precisely those of geometricFibreSectionLift. Naturality of the
inverse-image units and their composition identity give the displayed equation.
If Z is empty, both section modules are zero and the same formulas hold. The zero
coefficient ring also gives zero modules. No algebraicity of Omega over k is used. -/
theorem exists_integralStrictLocalFibreComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Sheaf.Γ (pullback f (strictHenselizationStructuralMap s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≅
      ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        unitSectionRestriction Λ
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) F
          (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
          ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
            Scheme.smallStrictHenselizationBaseChangeMap f s j)
          (by
            change _ ≫ pullback.snd _ f =
              pullback.fst f (Scheme.strictHenselizationStructuralMap s)
            simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
              pullbackSymmetry_hom_comp_snd]) ≫ e.hom =
          geometricFibreSectionRestriction Λ sq.toCommSq F
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1)
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).2 := by
  classical
  obtain ⟨hl, hs⟩ := strictHenselizationLocalStructure s
  let := hl
  let := hs
  let : Algebra (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨ψ, hsurj, hker, hpoint⟩ := strictHenselizationPointedMap s (by rfl)
  let t : Spec (.of Ω) ⟶ strictHenselizationScheme s := Spec.map (CommRingCat.ofHom
    ((IntermediateField.val
      (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp ψ))
  have ht : t ≫ strictHenselizationStructuralMap s = s := by
    let := (strictHenselization_properties s).2.1
    let j := Classical.choice (IsCofiltered.nonempty (C :=
      SmallModel.{u} (strictHenselizationNeighbourhoods s)))
    have hp := hpoint j
    rw [isoSpec_Spec_inv] at hp
    have hstr := ((exists_strictHenselizationStructuralMap s).choose_spec j)
    change _ = strictHenselizationStructuralMap s at hstr
    rw [← hstr, ← Category.assoc, ← Category.assoc]
    exact (congrArg (fun a ↦ a ≫ ((AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1).hom)
      hp).trans ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods s)).inverse.obj j).2.w
  set_option backward.isDefEq.respectTransparency false in
  have hclosed : t (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselizationRing s) := by
    apply strictHenselizationStructuralMap_fiber_eq_closedPoint_compat
      (A := strictHenselizationRing s) s (Iso.refl _)
      (t (IsLocalRing.closedPoint Ω))
    change (t ≫ strictHenselizationStructuralMap s) (IsLocalRing.closedPoint Ω) = _
    rw [ht]
  let i : X' ⟶ pullback f (strictHenselizationStructuralMap s) :=
    pullback.lift g' (f' ≫ t) (by rw [Category.assoc, ht]; exact sq.w)
  have hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g' :=
    pullback.lift_fst _ _ _
  have hi' : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hsq : IsPullback i f' (pullback.snd f (strictHenselizationStructuralMap s)) t := by
    apply IsPullback.of_right _ hi'
      (IsPullback.of_hasPullback f (strictHenselizationStructuralMap s))
    simpa only [hi, ht] using sq
  have hc : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (strictHenselizationStructuralMap s))).obj F)) :=
    isIso_integralStrictHenselianGeometricFibreRestriction Λ (strictHenselizationRing s)
      (pullback.snd f (strictHenselizationStructuralMap s)) t hclosed hsq _
  let := hc
  let r :=
    globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (strictHenselizationStructuralMap s))).obj F) ≫
      (Sheaf.Γ X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) i
          (pullback.fst f (strictHenselizationStructuralMap s)) g' hi.symm).inv.app F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
          (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).hom.app _
  have : IsIso r := by
    dsimp only [r]
    infer_instance
  refine ⟨asIso r, ?_⟩
  intro j
  let V := (Scheme.AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1
  let v := ((equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let l := (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
    Scheme.smallStrictHenselizationBaseChangeMap f s j
  have hl : l ≫ (f.Etale.obj V).hom = p := by
    change l ≫ pullback.snd _ f = p
    simp only [l, p, Category.assoc,
      Scheme.smallStrictHenselizationBaseChangeMap_snd, pullbackSymmetry_hom_comp_snd]
  have hr := unitSectionRestriction_comp Λ i p g' hi.symm F (f.Etale.obj V) l hl
  have hg : etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
      (by rw [Category.assoc, hl, ← hi]) = geometricFibreSectionLift sq.toCommSq V v := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [etaleSectionGraph, geometricFibreSectionLift,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, pullback.lift_fst]
      apply pullback.hom_ext
      · simp only [l, Category.assoc, pullback.lift_fst]
        rw [Scheme.smallStrictHenselizationBaseChangeMap_fst]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
        rw [hi']
        simp only [Category.assoc]
        rw [← Scheme.isoSpec_Spec_inv, hpoint j]
      · simp only [pullback.lift_snd]
        change (i ≫ l) ≫ (f.Etale.obj V).hom = g'
        rw [Category.assoc, hl, hi]
    · exact (etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
        (by rw [Category.assoc, hl, ← hi])).w.trans
        (geometricFibreSectionLift sq.toCommSq V v).w.symm
  have heq : unitSectionRestriction Λ g' F (f.Etale.obj V) (i ≫ l)
      (by rw [Category.assoc, hl, ← hi]) =
      geometricFibreSectionRestriction Λ sq.toCommSq F V v ≫
        (Sheaf.ΓNatIsoSheafSections _ _
          (IsTerminal.isTerminalOfObj
            (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
            (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by
    unfold unitSectionRestriction
    rw [hg]
    rfl
  have h := hr.trans heq
  change _ ≫ r = _
  dsimp only [r]
  simp only [← Category.assoc] at h ⊢
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
