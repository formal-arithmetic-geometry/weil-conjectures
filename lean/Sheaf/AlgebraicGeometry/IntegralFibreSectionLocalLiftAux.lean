module

public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.RingTheory.IntegralOverHenselianPair
import Sheaf.Paper.StrictHenselizationLocalStructure
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

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
  sorry

end AlgebraicGeometry.Etale
