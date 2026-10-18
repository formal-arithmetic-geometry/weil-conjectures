module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntAbSheafPowLocal
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicIntExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory

namespace AlgebraicGeometry.ProEtale
open Scheme
#check @Adjunction.unit_app_tensor_comp_map_δ
#check @Adjunction.unit_app_unit_comp_map_η
#check @Functor.monObjObj
#check @MonObj.ofIso
#check @Sheaf.isLocallySurjective_iff_epi
#check @Sheaf.isLocallySurjective_iff_epi'
#check @ProEt.mk
#check @Presheaf.isLocallySurjective_of_isLocallySurjective
#check @NatTrans.isMonHom_app
#check @Functor.isMonHom_map
example (X W : Scheme.{u}) (g : W ⟶ X) : (g)^*[Ab.{u+1}].Monoidal := inferInstance
example (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] : MonoidalPreadditive (Sheaf (ProEt.topology X) Ab.{u+1}) := inferInstance
example (X : Scheme.{u}) (M : Sheaf (ProEt.topology X) Ab.{u+1}) : PreservesColimitsOfSize.{0,0} (tensorRight M) := inferInstance
example (X W : Scheme.{u}) (l : ℕ) [Fact l.Prime] (g : W ⟶ X) (h : WeaklyEtale g) :
  (localizationRestriction Ab.{u+1} g h).obj (padicIntAbSheaf X l) = padicIntAbSheaf W l := rfl
end AlgebraicGeometry.ProEtale
