module
public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalMap
@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
/-- Tuplewise structural pullback coordinates force the beta square for a total map.
Source: Stacks Project, Tags 01FD and 03P2, augmented double-complex diagram.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-beta)
Proof: Unfold beta and apply ht in bidegree (n,0). It suffices to compare
the products before their total inclusion. Project to a tuple y, so the left
side is the resolution augmentation at the source tuple open, followed by
evaluation of alpha and restriction along additiveCechTuplePullback. Evaluate
hα at that source open and use naturality of J.ι along the tuple pullback map.
The result is J.ι at the target tuple open applied to the structural pullback
of its function section. By naturality of restrictFunctorΓ.inv, its transport
from functions on the open subscheme to sections on the open agrees with
restriction along hinter and unitToPushforwardObjUnit. The coordinate equality
in the hypothesis identifies this function with the tuple coordinate of x'.
Lift through ULift and apply J.ι. Product projection extensionality gives the
required equality, hence so does the total inclusion. Empty families give
zero products; degree zero and empty opens satisfy the same functorial
identities. The hypothesis ht is essential: an arbitrary total map need not
preserve the augmentation. -/
theorem additiveCech_pullback_total_beta
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = Scheme.etaleAdditiveSheafToLowerStar g ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (n : ℕ) (t : additiveCechTotal U I ⟶ additiveCechTotal V J)
    (ht : IsAdditiveCechPullbackTotalMap g U V hinter I J α t) :
    ∀ (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)
      (x' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).X n),
      (∀ y : Fin (n + 1) → ι,
        cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y x' =
          (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
            (homOfLE (hinter n y)).op
            ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
              (op (⨅ l, U (y l)))
              (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y x))) →
      t.f n (additiveCechBeta U I n x) = additiveCechBeta V J n x' := by sorry
end AlgebraicGeometry.Scheme.Modules
