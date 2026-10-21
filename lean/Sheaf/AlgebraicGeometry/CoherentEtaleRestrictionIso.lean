module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Canonical restriction of coherent tensor-section sheaves

Source: Stacks Project, Tags 03DR and 03DU; Tag 03Q8 coefficient restriction.
(blueprint: def-weil-pbc-coherent-etale-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The section formula uniquely determines the restriction isomorphism.
Source: Stacks Project, Tags 03DR, 03DU and 03Q8
(blueprint: def-weil-pbc-coherent-etale-restriction).

Proof: inverse image along an etale map is restriction along postcomposition.
At an etale object W the tensor-pullback composition isomorphism gives the
inverse of the displayed component. Its naturality follows from associativity
of the unit-normalized composition comparisons and naturality of section units.
These components therefore define inverse natural transformations. They are
isomorphisms of sheaves since both underlying presheaves are sheaves. Lift every
component and restriction by the same additive ULift functor. Every section is
ULift.up of a section, so the displayed formula also proves uniqueness. -/
theorem existsUnique_coherentEtaleRestrictionIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent]
    [(tensorPullback j).obj F |>.IsQuasicoherent] :
    ∃! e : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj
        (liftedCoherentEtaleSheaf F) ≅
        liftedCoherentEtaleSheaf ((tensorPullback j).obj F),
      ∀ (W : Y.Etale)
        (s : Γ((tensorPullback (W.hom ≫ j)).obj F, ⊤)),
        e.hom.hom.app (op W)
          (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
            inferInstance).inv.app (liftedCoherentEtaleSheaf F)).hom.app (op W)
              (ULift.up s)) =
          ULift.up (((tensorSectionsComp W.hom j).inv.app F).app ⊤ s) := by
  sorry

/-- Restriction with its actual tensor-composition section normalization.
Only a uniquely specified isomorphism is selected.
Source: Stacks Project, Tags 03DR, 03DU and 03Q8
(blueprint: def-weil-pbc-coherent-etale-restriction). -/
def coherentEtaleRestrictionIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent]
    [(tensorPullback j).obj F |>.IsQuasicoherent] :
    (Etale.upperStar AddCommGrpCat.{u + 1} j).obj (liftedCoherentEtaleSheaf F) ≅
      liftedCoherentEtaleSheaf ((tensorPullback j).obj F) :=
  Classical.choose (existsUnique_coherentEtaleRestrictionIso j F)

end
end AlgebraicGeometry.Scheme.Modules
