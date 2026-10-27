module

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalHomCohomology
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.Algebra.Homology.RingedSiteGlobalHomDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Global derived Hom and the right adjoint of algebraic-space pushforward

Source: Stacks Project, Spaces Duality, Tag 0E59 (lemma-iso-global-hom),
equation-sheafy-trace, with affine target
(blueprint: lem-sfb-space-global-hom-right-adjunction).

The comparison is the tensor-of-counits/evaluation map, followed by Leray and
postcomposition with the supplied right adjunction's counit. All global Hom
complexes take values in the ambient unbounded D(A).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
  [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]

/-- Relative cup is the adjoint of the tensor of the geometric derived counits.
Source: Stacks 0B6C, equation-sheafy-trace preceding 0E59
(blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def globalHomDirectImageCup {X Z : AlgebraicSpace S} (f : X ⟶ Z)
    (K L : X.DerivedModules) :
    Z.derivedDualityModel.closed.tensor.obj
        ((derivedDirectImage f).obj K, (derivedDirectImage f).obj L) ⟶
      (derivedDirectImage f).obj (X.derivedDualityModel.closed.tensor.obj (K, L)) :=
  (spaceDerivedAdjunction f).homEquiv _ _
    ((SingleComplex.derivedTensorComparison f).hom.app _ ≫
      X.derivedDualityModel.closed.tensor.map
        ((spaceDerivedAdjunction f).counit.app K, (spaceDerivedAdjunction f).counit.app L))

/-- Direct image on internal derived Hom, the transpose of cup followed by evaluation.
Source: Stacks 0B6D, equation-sheafy-trace preceding 0E59
(blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def globalHomDirectImageInternal {X Z : AlgebraicSpace S} (f : X ⟶ Z)
    (P Q : X.DerivedModules) :
    (derivedDirectImage f).obj (X.derivedHom.obj (op P, Q)) ⟶
      Z.derivedHom.obj (op ((derivedDirectImage f).obj P), (derivedDirectImage f).obj Q) :=
  Z.derivedDualityModel.closed.transpose _ _ _
    (globalHomDirectImageCup f (X.derivedHom.obj (op P, Q)) P ≫
      (derivedDirectImage f).map (X.derivedDualityModel.closed.evaluation P Q))

section Affine
variable (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- The canonical A-linear global derived Hom direct-image map: inverse Leray, then theta.
The compositor is oriented from source sections to target sections of direct image.
Source: Stacks 0B6D, 0D6E, equation-sheafy-trace preceding 0E59
(blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def affineGlobalHomDirectImageMap (P Q : X.DerivedModules) :
    (affineDerivedSections A Y e X f).obj (X.derivedHom.obj (op P, Q)) ⟶
      (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).obj
        ((schemeSpace Y).derivedHom.obj
          (op ((derivedDirectImage f).obj P), (derivedDirectImage f).obj Q)) :=
  (affineDerivedSectionsComposition A Y e X f).hom.app _ ≫
    (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
      (globalHomDirectImageInternal f P Q)

variable (T : QCohDirectImagePresentation f)
  (a : (schemeSpace Y).DerivedQCoh ⥤ X.DerivedQCoh) (adj : T.functor ⊣ a)

/-- The source bifunctor RHom_X(P,aF), with its specified A-action.
Source: Stacks 0E59 (blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def globalHomRightAdjunctionSource :
    X.DerivedQCohᵒᵖ × (schemeSpace Y).DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (X.derivedQCohProperty.ι.op.prod (a ⋙ X.derivedQCohProperty.ι)) ⋙
    X.derivedHom ⋙ affineDerivedSections A Y e X f

/-- The target bifunctor RHom_Y(Rf_*P,F), in the ambient D(A).
Source: Stacks 0E59 (blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def globalHomRightAdjunctionTarget :
    X.DerivedQCohᵒᵖ × (schemeSpace Y).DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} A) :=
  ((T.functor ⋙ (schemeSpace Y).derivedQCohProperty.ι).op.prod
      (schemeSpace Y).derivedQCohProperty.ι) ⋙
    (schemeSpace Y).derivedHom ⋙ affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)

/-- The actual counit-induced comparison. The two presentation isomorphisms identify
restricted pushforward with the ambient canonical K-injective derived pushforward.
Source: Stacks 0E59, equation-sheafy-trace
(blueprint: lem-sfb-space-global-hom-right-adjunction). -/
def globalHomRightAdjunctionMap (P : X.DerivedQCoh) (F : (schemeSpace Y).DerivedQCoh) :
    (globalHomRightAdjunctionSource A Y e X f a).obj (op P, F) ⟶
      (globalHomRightAdjunctionTarget A Y e X f T).obj (op P, F) :=
  affineGlobalHomDirectImageMap A Y e X f P.obj (a.obj F).obj ≫
    (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
      ((schemeSpace Y).derivedHom.map
        ((T.comparison.hom.app P).op,
          T.comparison.inv.app (a.obj F) ≫ (adj.counit.app F).hom))

/-- Global derived Hom adjunction, natural in both variables, for an arbitrary chosen
right adjoint on D_QCoh. Its underlying arrow and its action in every integer degree
are specified; no properness, flatness, boundedness or Noetherian hypothesis occurs.
Source: Stacks Project, Spaces Duality, Tag 0E59 and equation-sheafy-trace
(blueprint: lem-sfb-space-global-hom-right-adjunction).

Proof: apply lem-sfb-ringed-site-global-hom-direct-image to the canonical ringed-topos
morphism supplied by lem-trf-space-enlarged-etale-ringed-site-model. On the equivalent
small model its comparison is precisely inverse Leray followed by the transpose of
relative cup and direct image of evaluation, as defined above. Postcompose with the
supplied counit; its degree-j map is Rf_* of the represented shifted map followed by
the shifted counit. The shift comparison comes from
lem-pc-right-derived-functor-triangulated. Shift the source by -j, apply the supplied
adjunction, and shift back. The triangular identities prove that this is a bijection
on every shifted Hom group, including negative degrees. Quasi-coherent cohomology is
stable under shifts, so these are the Hom groups of the stated full subcategories.
By lem-weil-pbc-unbounded-derived-iso-cohomology the comparison is invertible in D(A).
Naturality of cup, evaluation, Leray and the counit proves naturality in P and F;
component inverses give the displayed natural isomorphism. -/
theorem globalHomRightAdjunction
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated) :
    ∃ d : globalHomRightAdjunctionSource A Y e X f a ≅
        globalHomRightAdjunctionTarget A Y e X f T,
      (∀ (P : X.DerivedQCoh) (F : (schemeSpace Y).DerivedQCoh),
        d.hom.app (op P, F) = globalHomRightAdjunctionMap A Y e X f T a adj P F) ∧
      (∀ (P : X.DerivedQCoh) (F : (schemeSpace Y).DerivedQCoh) (j : ℤ) (x : _),
        affineGlobalHomCohomology A Y e (schemeSpace Y) (𝟙 _)
            (T.functor.obj P).obj F.obj j
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
              (d.hom.app (op P, F)) x) =
          T.comparison.hom.app P ≫
            (derivedDirectImage f).map
              (affineGlobalHomCohomology A Y e X f P.obj (a.obj F).obj j x) ≫
            ((smallModuleDirectImage f).rightDerivedFunctor.commShiftIso j).hom.app _ ≫
            (T.comparison.inv.app (a.obj F) ≫ (adj.counit.app F).hom)⟦j⟧') := by
  sorry

end Affine
end AlgebraicGeometry.AlgebraicSpace
