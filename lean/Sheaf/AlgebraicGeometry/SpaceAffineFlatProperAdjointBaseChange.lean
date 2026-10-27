module

public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
import Sheaf.AlgebraicGeometry.SpaceAffinePullbackPerfectDetection
import Sheaf.AlgebraicGeometry.SpaceAffinePerfectHomBaseChange
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Affine base change of the proper flat coherent right adjoint

Source: Stacks Project, spaces-duality.tex, Tags 0E5I(1) and 0E5L
(blueprint: lem-sfb-affine-flat-proper-adjoint-base-change).

The inverse appearing in the adjunct is an inverse to the actual canonical exchange.
The direct-image presentations retain their identifications with K-injective direct image.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Restrict the already constructed tensor pullback to quasi-coherent cohomology.
The lift changes neither its objects nor its morphisms in the ambient derived category.
Source: Stacks, Derived Categories of Spaces, Tag 08F4; Spaces Duality, Tag 0E5I
(blueprint: lem-sfb-affine-flat-proper-adjoint-base-change). -/
def spaceQCohPullback {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (g : X ⟶ Y) :
    Y.DerivedQCoh ⥤ X.DerivedQCoh :=
  X.derivedQCohProperty.lift (Y.derivedQCohProperty.ι ⋙ spaceDerivedPullback g)
    (fun K ↦ (spaceDerivedPullback_tensor_preserve_QCoh.{u, w, w, w} g).1 K.obj K.property)

/-- The right-adjoint base-change component, formed using exactly the supplied counits.
Its adjunct is beta inverse followed by the pullback of the original counit.
The comparison beta is required to be the canonical exchange in the theorem below.
Source: Stacks, Spaces Duality, Tags 0E5I and 0E5L
(blueprint: lem-sfb-affine-flat-proper-adjoint-base-change). -/
def affineProperAdjointComparison
    {Y Y' : Over S} {X X' : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} X'.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace Y).SmallModules]
    [HasDerivedCategory.{w} (schemeSpace Y').SmallModules]
    {f : X ⟶ schemeSpace Y} {f' : X' ⟶ schemeSpace Y'}
    (g : Y' ⟶ Y) (h : X' ⟶ X)
    (D : QCohDirectImagePresentation f) (D' : QCohDirectImagePresentation f')
    (a : (schemeSpace Y).DerivedQCoh ⥤ X.DerivedQCoh)
    (a' : (schemeSpace Y').DerivedQCoh ⥤ X'.DerivedQCoh)
    (adj : D.functor ⊣ a) (adj' : D'.functor ⊣ a')
    (F : (schemeSpace Y).DerivedQCoh)
    (β : (spaceDerivedPullback (traceSchemeMap g)).obj
        ((derivedDirectImage f).obj (a.obj F).obj) ≅
      (derivedDirectImage f').obj ((spaceDerivedPullback h).obj (a.obj F).obj)) :
    (spaceQCohPullback h).obj (a.obj F) ⟶
      a'.obj ((spaceQCohPullback (traceSchemeMap g)).obj F) :=
  adj'.homEquiv _ _ (ObjectProperty.homMk
    (D'.comparison.hom.app ((spaceQCohPullback h).obj (a.obj F)) ≫ β.inv ≫
      (spaceDerivedPullback (traceSchemeMap g)).map
        (D.comparison.inv.app (a.obj F) ≫ (adj.counit.app F).hom)))

/-- Arbitrary affine base change of the proper flat finitely presented right adjoint.
The existential iso beta is pinned to the canonical derived exchange; hence its inverse
is uniquely determined. Alpha is the actual adjunct defined above, not an arbitrary iso.
Source: Stacks Project, Spaces Duality, Tag 0E5I(1) and Tag 0E5L
(blueprint: lem-sfb-affine-flat-proper-adjoint-base-change).

Proof:
1. Write Y = Spec A and Y' = Spec B. Properness makes X qcqs. Flat derived
pushforward base change makes beta invertible and preserves quasi-coherence, including
for the base-changed proper flat finitely presented morphism. The map h is affine,
since its pullback to an affine chart is a fibre product of affine schemes. By
lem-sfb-space-affine-pullback-perfect-detection, test alpha on Lh*P for every perfect P.
2. Set H = RHom_X(P,aF) and J = RHom_Y(Rf_*P,F). The counit-induced global Hom
adjunction identifies H with J. The theorem lem-sfb-space-affine-perfect-hom-base-change
identifies H tensor_A^L B with RHom_X'(Lh*P,Lh*aF), without boundedness assumptions.
3. Global Hom adjunction for f' and beta_P identify the other Hom complex with
RHom_Y'(Lg*Rf_*P,Lg*F). Proper-flat perfect sections makes RΓ(X,P) perfect over A.
Derived pushforward composition identifies this with RΓ(Y,Rf_*P). Affine étale derived
module realization therefore makes Rf_*P perfect. Apply perfect-Hom base change to
id_Y, Rf_*P and F; it identifies that second Hom complex with J tensor_A^L B.
This uses flatness of id_Y, and imposes no flatness condition on g.
4. The adjunct formula gives epsilon_f' after Rf'_*alpha equal to Lg*epsilon_f
following beta inverse. Compose with beta to obtain the stated trace equation.
5. Under steps 2 and 3, the Hom map induced by alpha is exactly the tensor extension
of the counit adjunction map H to J. Indeed, naturality moves beta past the pulled Hom,
and step 4 replaces the remaining counit composite by Lg*epsilon_f. The scalar-extension
adjunction identifies these maps as maps of complexes, not only degree-zero Homs.
All outside comparisons are invertible, so the Hom map is invertible in every degree.
Step 1 then proves alpha invertible. Step 4 supplies the second assertion. -/
theorem affineFlatProperAdjointBaseChange
    {Y Y' : Over S} [IsAffine Y.left] [IsAffine Y'.left]
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} X'.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace Y).SmallModules]
    [HasDerivedCategory.{w} (schemeSpace Y').SmallModules]
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : IsPullback h f' f (traceSchemeMap g))
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f)
    (D : QCohDirectImagePresentation f) (D' : QCohDirectImagePresentation f')
    (a : (schemeSpace Y).DerivedQCoh ⥤ X.DerivedQCoh)
    (a' : (schemeSpace Y').DerivedQCoh ⥤ X'.DerivedQCoh)
    (adj : D.functor ⊣ a) (adj' : D'.functor ⊣ a')
    (F : (schemeSpace Y).DerivedQCoh) :
    ∃ β : (spaceDerivedPullback (traceSchemeMap g)).obj
        ((derivedDirectImage f).obj (a.obj F).obj) ≅
      (derivedDirectImage f').obj ((spaceDerivedPullback h).obj (a.obj F).obj),
      β.hom = moduleDerivedExchange f f' (traceSchemeMap g) h sq.w (a.obj F).obj ∧
      IsIso (affineProperAdjointComparison g h D D' a a' adj adj' F β) ∧
      β.hom ≫ (derivedDirectImage f').map
          (affineProperAdjointComparison g h D D' a a' adj adj' F β).hom ≫
        D'.comparison.inv.app (a'.obj ((spaceQCohPullback (traceSchemeMap g)).obj F)) ≫
        (adj'.counit.app ((spaceQCohPullback (traceSchemeMap g)).obj F)).hom =
      (spaceDerivedPullback (traceSchemeMap g)).map
        (D.comparison.inv.app (a.obj F) ≫ (adj.counit.app F).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
