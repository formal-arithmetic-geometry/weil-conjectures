module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange
/-- A degreewise canonical open tensor-stalk square induces the homology square.

Proof: the hypothesis is an equality in every degree of the two additive chain
maps obtained by composing tau with tensorStalkIso, or tensorStalkIso with
openPinnedTensorRestrictionIso inverse and the same-germ stalk comparison gamma.
The naturality of these comparisons for differentials makes the two composites
chain maps; HomologicalComplex.Hom.ext makes them equal. Apply homologyMap in
degree i and its composition formula. Naturality of ShortComplex.mapHomologyIso
moves the additive forgetful homology factors across both tensorStalkIso maps.
Expand singleComplexOpenTensorRestrictionMap: it is localization of the inverse
homotopy restriction comparison followed by the inverse exact restriction factor.
Use quotientCompQhIso naturality and mapDerivedCategoryFactorsh to express this
as localization of the termwise inverse comparison followed by the inverse
complex restriction factor. comparisonStalkHomologyIso_naturality identifies
its stalk cohomology map with the homology map of that stalk chain map.
Expand openDerivedAdditiveStalkIso. The equations mapDerivedCategoryCompIso_fac
and mapDerivedCategoryNatIso_fac cancel the intermediate exact functor factors;
mapDerivedCategoryHomologyFunctorIso_hom_app_Q identifies the remaining homology
factor with the additive homology map of gamma. Thus the homology of the given
chain square is exactly the displayed equation after composing with the inverse
comparisonStalkHomologyIso at each endpoint. All cancellation uses specified
natural isomorphisms; no scalar coordinates or arbitrary witness are chosen.
Zero homology groups need no cancellation of elements. Empty opens have no z,
and top opens specialize to ordinary naturality of these same factors.
Source: Stacks Project, Tags 08HY and 08DW (exact localization); the exact functor
factorization equations and Mathlib homology naturality.
(blueprint: lem-pc-open-ordinary-tensor-germ-equation). -/
theorem openOrdinaryTensor_germ_transport_equation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let C₀ := C z
    let C₁ := C z.val
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    let k₀ := HomologicalComplex.homologyMap
      (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
      (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
        (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
    let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
      (comparisonStalkHomologyIso X' z.val
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    ∀ (τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
        (F.mapHomologicalComplex (.up ℤ)).obj T),
      (∀ n : ℤ,
        τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
          F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
            F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
              (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
            γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) →
      F₀.map k₀ ≫ F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
        ((T₀.sc i).mapHomologyIso F₀).inv ≫
          HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
            F.map k := by sorry

end AlgebraicGeometry
