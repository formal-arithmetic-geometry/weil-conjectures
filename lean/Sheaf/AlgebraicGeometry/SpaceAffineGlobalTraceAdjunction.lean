module

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalHomCohomology
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization

/-! # Derived global trace adjunction over an affine scheme

Source: Stacks, Spaces Duality, Tags 0E58 and 0GG4; Spaces Perfect, Tag 071Q
(blueprint: lem-sfb-space-affine-global-trace-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace
section
variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
  [HasDerivedCategory.{w} X.SmallModules]
  [HasDerivedCategory.{w} (schemeSpace Y).SmallModules]
  (F : QCohDirectImagePresentation f)
  (a : (schemeSpace Y).DerivedQCoh ⥤ X.DerivedQCoh) (adj : F.functor ⊣ a)

/-- The counit trace, using the normalized global-sections compositor and affine unit.
Source: Stacks 0E58 (blueprint: lem-sfb-space-affine-global-trace-adjunction). -/
def affineGlobalTrace :
    (affineDerivedSections A Y e X f).obj
        (a.obj (schemeSpace Y).derivedQCohStructure).obj ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
  (affineDerivedSectionsComposition A Y e X f).hom.app _ ≫
    (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
      ((F.comparison.inv.app (a.obj (schemeSpace Y).derivedQCohStructure)) ≫
        (adj.counit.app (schemeSpace Y).derivedQCohStructure).hom) ≫
    (affineStructureDerivedIso A Y e).hom

/-- Contravariant global internal Hom into W; it lives in the full ambient D(A).
Source: Stacks 0E58 (blueprint: lem-sfb-space-affine-global-trace-adjunction). -/
def affineGlobalTraceSource : X.DerivedQCohᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  X.derivedQCohProperty.ι.op ⋙
    Prod.sectL X.DerivedModulesᵒᵖ (a.obj (schemeSpace Y).derivedQCohStructure).obj ⋙
    X.derivedHom ⋙ affineDerivedSections A Y e X f

/-- Ordinary-module internal Hom of global sections into A[0].
Source: Stacks 0E58 (blueprint: lem-sfb-space-affine-global-trace-adjunction). -/
def affineGlobalTraceTarget : X.DerivedQCohᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (X.derivedQCohProperty.ι ⋙ affineDerivedSections A Y e X f).op ⋙
    Prod.sectL (DerivedCategory (ModuleCat.{u} A))ᵒᵖ
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ⋙
    ordinaryModuleDerivedInternalHom A

/-- The exact cup/evaluation/counit pairing which specifies the isomorphism's adjunct.
Source: Stacks 0E58 (blueprint: lem-sfb-space-affine-global-trace-adjunction). -/
def affineGlobalTracePairing (L : X.DerivedQCoh) :=
  affineDerivedCup A Y e X f
      (X.derivedHom.obj (op L.obj, (a.obj (schemeSpace Y).derivedQCohStructure).obj)) L.obj ≫
    (affineDerivedSections A Y e X f).map
      (X.derivedDualityModel.closed.evaluation L.obj
        (a.obj (schemeSpace Y).derivedQCohStructure).obj) ≫
    affineGlobalTrace A Y e X f F a adj

/-- Derived global trace duality, natural in every quasi-coherent source, with its pairing
and all-integer-degree adjunction normalization. The Hom object on X is unrestricted.
Source: Stacks 0E58, 0GG4 and 071Q
(blueprint: lem-sfb-space-affine-global-trace-adjunction).

Proof: let t be the displayed counit trace. Transpose the canonical cup product
followed by global evaluation and t in the ordinary module tensor-Hom adjunction.
Naturality of cup, evaluation and the fixed trace makes these maps natural in L.
On K-flat and K-injective representatives, the product-projection Hom normalization
identifies degree-n cohomology with derived maps L to W[n]. The transpose sends u
to G(u), followed by t[n] and the canonical shift comparison. Naturality of the
normalized sections/direct-image compositor rewrites this as affine global sections
of Rf_*(u), followed by the shifted supplied counit. This is exactly the supplied
adjunction at O_Y[n], using the canonical adjoint shift identification. The full
quasi-coherent subcategories have the ambient Hom sets. The affine derived-module
equivalence is fully faithful, so that map is bijective in every integer degree.
Consequently the transpose is a cohomology isomorphism in every degree and hence
an isomorphism in D(A). This argument never requires quasi-coherence of RHom_X. -/
theorem affineGlobalTraceAdjunction
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom)) :
    ∃ τ : affineGlobalTraceSource A Y e X f a ≅ affineGlobalTraceTarget A Y e X f,
      (∀ L : X.DerivedQCoh,
        MonoidalCategory.tensorHom (τ.hom.app (op L)) (𝟙 _) ≫
          ((DerivedMonoidal.braidedCategory' DerivedCategory.Qh
            (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))).braiding _ _).hom ≫
          (ihom.ev ((affineDerivedSections A Y e X f).obj L.obj)).app _ =
        affineGlobalTracePairing A Y e X f F a adj L) ∧
      (∀ (L : X.DerivedQCoh) (n : ℤ) (x : _),
        moduleDerivedHomClass A ((affineDerivedSections A Y e X f).obj L.obj) _ n
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            (τ.hom.app (op L)) x) =
        (affineDerivedSectionsComposition A Y e X f).hom.app L.obj ≫
          (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
            ((derivedDirectImage f).map
              (affineGlobalHomCohomology A Y e X f L.obj
                (a.obj (schemeSpace Y).derivedQCohStructure).obj n x) ≫
              ((smallModuleDirectImage f).rightDerivedFunctor.commShiftIso n).hom.app _ ≫
              ((F.comparison.inv.app (a.obj (schemeSpace Y).derivedQCohStructure)) ≫
                (adj.counit.app (schemeSpace Y).derivedQCohStructure).hom)⟦n⟧') ≫
          ((affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).commShiftIso n).hom.app _ ≫
          (affineStructureDerivedIso A Y e).hom⟦n⟧') := by
  sorry

end
end AlgebraicGeometry.AlgebraicSpace
