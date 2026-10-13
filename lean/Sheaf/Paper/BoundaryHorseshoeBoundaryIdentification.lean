module
public import Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ConcreteCategory
import Sheaf.CategoryTheory.Abelian.RightDerivedTriangleConnecting
@[expose] public section
universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
/-- The snake boundary of the global horseshoe equals the derived-triangle boundary.
Source: Stacks Project, Tags 0117, 013T and 015B.
(blueprint: stage3-boundary-identification).

Proof: Split the resolution rows using injectivity of IA in each degree and apply
additive global sections, obtaining a short exact sequence of global complexes.
The augmentation of q is a degree-zero cocycle. The two displayed equalities
are exactly the lifting equalities in the concrete snake formula; that formula
sends its homology class to the class of a. The degree-zero resolution comparison
sends toRightDerivedZero(q) to the class of its augmentation. Apply the horseshoe
comparison of rightDerived_triangle_connecting to these compatible resolutions:
its first equality identifies the snake map transported by isoRightDerivedObj,
and its second identifies the same map with the boundary of the derived image
of the canonical short-exact-sequence triangle. The latter, transported by the
single-object comparison isomorphisms, is moduleCohomologyBoundary by definition.
Compose the comparison equalities and cancel the degree-one isomorphism to obtain
the stated equality. It holds for every permitted lift: changing b changes a
by a boundary, so its homology class is unchanged. For q = 0 that class is zero,
and zero objects introduce no exception. -/
theorem boundary_horseshoe_boundary_identification (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [EnoughInjectives X.Modules]
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    (S : ShortComplex X.Modules) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    (hS : S.ShortExact) (q : S.X₃.val.obj (op ⊤))
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b) :
    (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).hom
      (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q)) =
      (RingedSpace.globalSectionsComplex IA).homologyπ 1 a := by
  sorry
end AlgebraicGeometry.Scheme.Modules
