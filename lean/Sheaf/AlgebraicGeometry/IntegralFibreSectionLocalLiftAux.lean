module

public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.Paper.StrictHenselizationLocalStructure
import Sheaf.Paper.StrictHenselizationPointedMap
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber
import Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility
import Sheaf.AlgebraicGeometry.IntegralStrictHenselianGeometricFibreSections
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap

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
        qcqsStrictLocalSectionRestriction Λ f s F j ≫ e.hom =
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
    have hstr := Classical.choose_spec (exists_strictHenselizationStructuralMap s) j
    change _ = strictHenselizationStructuralMap s at hstr
    rw [← hstr, ← Category.assoc, ← Category.assoc]
    exact (congrArg (fun a ↦ a ≫ ((AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j).1).hom)
      hp).trans ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods s)).inverse.obj j).2.w
  set_option backward.isDefEq.respectTransparency false in
  have hclosed : t (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselizationRing s) := by
    apply (strictHenselizationStructuralMap_fiber_eq_closedPoint
      (A := strictHenselizationRing s) s (Iso.refl _)
      (t (IsLocalRing.closedPoint Ω))).mp
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
  have : IsIso (strictLocalFibreRestriction Λ i hi F) := by
    unfold strictLocalFibreRestriction
    infer_instance
  refine ⟨asIso (strictLocalFibreRestriction Λ i hi F), ?_⟩
  intro j
  exact strictLocalFibreRestriction_compatibility Λ sq.toCommSq t hpoint i hi hi' F j

end AlgebraicGeometry.Etale
