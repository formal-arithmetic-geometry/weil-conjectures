module

public import Sheaf.Paper.ModuleCohomologyCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.Paper.CechCupPullbackCompat

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

theorem moduleCup_pairing_exists {X : Scheme.{v}} (F G : X.Modules) :
    Nonempty (CupResolutionPairing F G) := by
  exact exists_moduleCupResolutionPairing F G

/-! Resolution-level part of pullback compatibility. -/

/--
Resolution-level part of pullback compatibility.
Source: Stacks Project, Tag 0FKV, resolution-level cycle comparison.
(blueprint: lem-sc-module-cup-pullback-cycle-step)
Proof: transport the three complexes of a cup-paired acyclic resolution through
the pullback adjunction unit. The sectionwise tensor comparison identifies the
transported target pairing with the pairing of the transported inputs. Apply
the two `IsModuleCupProduct` characterizations to the resulting cycles.
-/
theorem moduleCup_pullback_cycle_step (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup' : (RingedSpace.moduleCohomology X'.toRingedSpace p).obj
        ((tensorPullback f).obj F) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace q).obj
        ((tensorPullback f).obj G) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).obj
        (@id X'.Modules ((tensorPullback f).obj F ⊗ (tensorPullback f).obj G)))
    (hc' : IsModuleCupProduct ((tensorPullback f).obj F) ((tensorPullback f).obj G)
      p q cup')
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).map
        ((Classical.choose (module_pullback_tensor f)) F G).hom
        (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) (p + q)
          (cup (D.left.class p a) (D.right.class q b))) =
      cup' (moduleCohomologyPullback f F p (D.left.class p a))
        (moduleCohomologyPullback f G q (D.right.class q b)) := by
  exact moduleCup_pullback_naturality X X' f F G p q cup hc cup' hc'
    (D.left.class p a) (D.right.class q b)


end
end AlgebraicGeometry.Scheme.Modules
