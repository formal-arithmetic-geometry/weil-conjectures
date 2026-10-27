module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

import Sheaf.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.AlgebraicGeometry.PerfectAffineModulePreimage
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Relative perfection and endomorphisms of the affine adjoint unit

Source: Stacks Project, Spaces Duality, Tag 0E5V, clauses (1)-(3);
More on Morphisms of Spaces, Tag 0DKN
(blueprint: lem-sfb-affine-adjoint-unit-properties).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The right adjoint of proper flat finitely presented direct image, evaluated at
O_Y, is Y-perfect, has nonpositive direct image, and has only scalar derived endomorphisms.
The supplied presentation identifies its functor naturally with the CANONICAL Rf_*;
its right adjunction is the right adjunction in the statement, not the ordinary f^* adjunction.
Source: Stacks, Tag 0E5V(1)-(3), relative perfectness Tag 0DKN
(blueprint: lem-sfb-affine-adjoint-unit-properties).

Proof:
1. Put Y=Spec A and G=RΓ(X,-). Perfect duality and the affine global trace
   adjunction give G(E tensor W)=RHom_A(G(E-dual),A) for every perfect E.
   Perfect direct-image sections and duality on D(A) make this perfect.
2. The perfect-test criterion gives relative perfection of W and local lower bounds.
   Pseudo-coherent internal Hom with a locally bounded-below quasi-coherent target
   is quasi-coherent, so B_X=RHom_X(W,W) lies in D_QCoh.
3. For B=G(O_X), the affine projection formula and flatness show that B tensor M
   has no negative cohomology for every A-module M. Perfect sections give an upper
   bound N. Pseudo-coherence follows from proper-flat direct image and the affine
   Zariski/étale comparison. The projective-window lemma supplies a finite-projective
   representative P supported in [0,N].
4. The trace adjunction identifies G(W) with RHom_A(B,A), computed by Hom(P,A[0])
   in [-N,0]. The pushforward compositor and affine étale module realization turn
   this into H^i(Rf_*W)=0 for i>0.
5. Closed tensor-Hom adjunction, the supplied right adjunction, the trace comparison,
   perfect biduality and global-Hom cohomology identify Hom(E,B_X) with Hom(E,O_X)
   naturally for every perfect E.
6. Under this identification scalar multiplication sends u:E→O_X to its transpose
   u tensor id_W. Evaluation and the trace counit give the same functional; the
   bidual triangle identity proves this is the specified scalar map. Thus Hom(E,α)
   is bijective, also after every shift of E.
7. In the triangle of α its cone C is quasi-coherent by step 2. All Hom(E,C[n]) vanish.
   The objects T for which all Hom(T,C[n]) vanish form a localizing class containing
   the perfect objects. Perfect localizing generation makes it all of D_QCoh.
   Take T=C: id_C=0, so C=0 and the actual scalar morphism α is invertible. -/
theorem affineAdjointUnit_properties
    {S : Scheme.{u}} (Y : Over S) [IsAffine Y.left]
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace Y).SmallModules]
    (F : QCohDirectImagePresentation f)
    (a : (schemeSpace Y).DerivedQCoh ⥤ X.DerivedQCoh) (adj : F.functor ⊣ a) :
    IsPerfectRelativeToScheme Y f (a.obj (schemeSpace Y).derivedQCohStructure).obj ∧
      (∀ i : ℤ, 0 < i → IsZero
        ((DerivedCategory.homologyFunctor (schemeSpace Y).SmallModules i).obj
          ((derivedDirectImage f).obj (a.obj (schemeSpace Y).derivedQCohStructure).obj))) ∧
      IsIso (derivedScalarEndomorphism X (a.obj (schemeSpace Y).derivedQCohStructure).obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
