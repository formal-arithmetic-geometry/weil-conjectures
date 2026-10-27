/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.ResolvingDerivedAdjunction

/-! # A face total model from componentwise injective resolutions

Source: Stacks Project, spaces-simplicial.tex, Tag 0D7F, with the injective-order-map
adaptation and canonical augmentation normalization in the DAG proof
(blueprint: lem-sfb-face-component-injective-total-model).

The output records an actual functor to bicomplexes, its column identifications,
finite diagonal coproducts, and a natural comparison with the universal unbounded
right-derived pair. No object is chosen from this existence statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open scoped BigOperators Simplicial

namespace CategoryTheory.SemisimplicialRingedTotal

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
  {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
  {R : RingDiagram D} {h : Presheaf.IsSheaf D.totalTopology R.presheaf}
  {P : Presentation R h} {S : Site.{u}}
  {A : Augmentation R S P.face P.faceId P.faceComp}

/-- The column functor a_{p,*} e_p. Source: Stacks 0D7F
(blueprint: lem-sfb-face-component-injective-total-model). -/
abbrev faceColumn (_V : AugmentationPresentation P S A) (p : ℕ) :
    (R.total h).modules ⥤ S.modules :=
  (P.evaluation (op ⦋p⦌ₛ)).ordinary ⋙ (A.map (op ⦋p⦌ₛ)).modules

/-- The transpose of a face transition, using precisely the augmentation compositor
and component counit. Source: Stacks 0D7D, face-only adaptation
(blueprint: lem-sfb-face-component-injective-total-model). -/
def faceCoface (V : AugmentationPresentation P S A) (M : (R.total h).modules)
    (p : ℕ) (i : Fin (p + 2)) : (faceColumn V p).obj M ⟶
      (faceColumn V (p + 1)).obj M :=
  (V.components (op ⦋p + 1⦌ₛ)).adjunction.homEquiv _ _
    ((V.faceComposition (SemiSimplexCategory.homOfMono (SimplexCategory.δ i)).op).ordinary.hom.app
        ((faceColumn V p).obj M) ≫
      (P.pullback (SemiSimplexCategory.homOfMono (SimplexCategory.δ i)).op).ordinary.map
        ((V.components (op ⦋p⦌ₛ)).adjunction.counit.app
          ((P.evaluation (op ⦋p⦌ₛ)).ordinary.obj M)) ≫
      (P.transition (SemiSimplexCategory.homOfMono (SimplexCategory.δ i)).op).app M)

/-- An actual nonnegative, integer-indexed resolution. Vanishing is categorical zero,
not a restriction on the objects or on their coefficients. Source: Stacks 013K, 0D7F
(blueprint: lem-sfb-face-component-injective-total-model). -/
structure FaceNonnegativeResolution (X : Site.{u}) (M : X.modules) where
  complex : CochainComplex X.modules ℤ
  augmentation : (CochainComplex.singleFunctor X.modules 0).obj M ⟶ complex
  quasiIso : QuasiIso augmentation
  nonnegative : ∀ q : ℤ, q < 0 → IsZero (complex.X q)

/-- A resolution in the total category with injective component terms; injectivity
in the total category is not required. Source: Stacks 0D7F, componentwise adaptation
(blueprint: lem-sfb-face-component-injective-total-model). -/
structure FaceComponentResolution (P : Presentation R h) (M : (R.total h).modules)
    extends FaceNonnegativeResolution (R.total h) M where
  component_injective : ∀ (p : ℕ) (q : ℤ),
    Injective ((P.evaluation (op ⦋p⦌ₛ)).ordinary.obj (complex.X q))

/-- The degree-zero complex map associated to a module map out of a^*G.
Source: Stacks 0D7D, ordinary module adjunction
(blueprint: lem-sfb-face-component-injective-total-model). -/
def faceSingleMap (V : AugmentationPresentation P S A)
    {G : S.modules} {M : (R.total h).modules} (φ : V.pullback.ordinary.obj G ⟶ M) :
    (V.pullback.ordinary.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor S.modules 0).obj G) ⟶
      (CochainComplex.singleFunctor (R.total h).modules 0).obj M :=
  (HomologicalComplex.singleMapHomologicalComplex V.pullback.ordinary (.up ℤ) 0).hom.app G ≫
    (CochainComplex.singleFunctor (R.total h).modules 0).map φ

/-- The total-model certificate, retaining the alternating faces, column differentials,
finite diagonals, naturality on all augmented resolution maps and the component-zero
normalization for every extending lift. `RF, η` are the ambient universal unbounded
right-derived pair on complexes, rather than degreewise right derived functors.

The normalization is written without suppressing localization comparisons: its right
side is the localized ordinary adjunction unit, then the right-derived comparison,
then RF applied to φ[0]. Exactness of a^* identifies this with the canonical derived
adjunction unit followed by Ra_*(φ[0]).

Source: Stacks 0D7F and 0D7D, with the face-only adaptation
(blueprint: lem-sfb-face-component-injective-total-model). -/
structure FaceComponentTotalModel (V : AugmentationPresentation P S A)
    (RF : (R.total h).D ⥤ S.D)
    (η : V.map.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF) where
  bicomplex : CochainComplex (R.total h).modules ℤ ⥤
    HomologicalComplex₂ S.modules (.up ℤ) (.up ℤ)
  column : ∀ (J : CochainComplex (R.total h).modules ℤ) (p : ℕ),
    ((bicomplex.obj J).X (p : ℤ)) ≅
      ((faceColumn V p).mapHomologicalComplex (.up ℤ)).obj J
  negative_face : ∀ (J : CochainComplex (R.total h).modules ℤ) (p q : ℤ),
    p < 0 → IsZero (((bicomplex.obj J).X p).X q)
  horizontal : ∀ (J : CochainComplex (R.total h).modules ℤ) (p : ℕ) (q : ℤ),
    ((bicomplex.obj J).d (p : ℤ) ((p + 1 : ℕ) : ℤ)).f q ≫
        (column J (p + 1)).hom.f q =
      (column J p).hom.f q ≫ ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
        faceCoface V (J.X q) p i
  column_naturality : ∀ {J J' : CochainComplex (R.total h).modules ℤ}
      (w : J ⟶ J') (p : ℕ),
    (bicomplex.map w).f (p : ℤ) ≫ (column J' p).hom =
      (column J p).hom ≫ ((faceColumn V p).mapHomologicalComplex (.up ℤ)).map w
  [hasTotal : ∀ J : CochainComplex (R.total h).modules ℤ,
    (bicomplex.obj J).HasTotal (.up ℤ)]
  finite_diagonal : ∀ (M : (R.total h).modules) (J : FaceComponentResolution P M) (n : ℕ),
    IsColimit (Cofan.mk (((bicomplex.obj J.complex).total (.up ℤ)).X (n : ℤ))
      (fun p : Fin (n + 1) ↦ (column J.complex p.val).inv.f ((n - p.val : ℕ) : ℤ) ≫
        (bicomplex.obj J.complex).ιTotalOrZero (.up ℤ) (p.val : ℤ)
          ((n - p.val : ℕ) : ℤ) (n : ℤ)))
  total_negative : ∀ (M : (R.total h).modules) (J : FaceComponentResolution P M)
      (n : ℤ), n < 0 → IsZero (((bicomplex.obj J.complex).total (.up ℤ)).X n)
  comparison : ∀ (M : (R.total h).modules) (J : FaceComponentResolution P M),
    DerivedCategory.Q.obj ((bicomplex.obj J.complex).total (.up ℤ)) ≅
      RF.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M))
  naturality : ∀ {M M' : (R.total h).modules}
      (J : FaceComponentResolution P M) (J' : FaceComponentResolution P M')
      (f : M ⟶ M') (w : J.complex ⟶ J'.complex),
    J.augmentation ≫ w = (CochainComplex.singleFunctor _ 0).map f ≫ J'.augmentation →
      DerivedCategory.Q.map (HomologicalComplex₂.total.map (bicomplex.map w) (.up ℤ)) ≫
          (comparison M' J').hom =
        (comparison M J).hom ≫ RF.map
          (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map f))
  augmentation : ∀ (M : (R.total h).modules) (J : FaceComponentResolution P M)
      (G : S.modules) (K : FaceNonnegativeResolution S G),
    (∀ q : ℤ, Injective (K.complex.X q)) →
    ∀ (φ : V.pullback.ordinary.obj G ⟶ M)
      (t : (V.pullback.ordinary.mapHomologicalComplex (.up ℤ)).obj K.complex ⟶ J.complex),
      (V.pullback.ordinary.mapHomologicalComplex (.up ℤ)).map K.augmentation ≫ t =
        faceSingleMap V φ ≫ J.augmentation →
      ∃ b : K.complex ⟶ (bicomplex.obj J.complex).total (.up ℤ),
        (∀ q : ℤ, b.f q = (V.components (op ⦋0⦌ₛ)).adjunction.homEquiv _ _
          ((V.component (op ⦋0⦌ₛ)).inv.app (K.complex.X q) ≫
            (P.evaluation (op ⦋0⦌ₛ)).ordinary.map (t.f q)) ≫
          (column J.complex 0).inv.f q ≫
          (bicomplex.obj J.complex).ιTotalOrZero (.up ℤ) 0 q q) ∧
        DerivedCategory.Q.map K.augmentation ≫ DerivedCategory.Q.map b ≫
            (comparison M J).hom =
          DerivedCategory.Q.map ((V.pullback.adjunction.mapHomologicalComplex (.up ℤ)).unit.app
              ((CochainComplex.singleFunctor S.modules 0).obj G)) ≫
            η.app ((V.pullback.ordinary.mapHomologicalComplex (.up ℤ)).obj
              ((CochainComplex.singleFunctor S.modules 0).obj G)) ≫
            RF.map (DerivedCategory.Q.map (faceSingleMap V φ))

/-- Derived face augmentation from every componentwise injective resolution.
Source: Stacks Project, Tag 0D7F, double-complex proof, and Tag 0D7D, augmented
Čech complex; injective-order-map and componentwise-resolution adaptation
(blueprint: lem-sfb-face-component-injective-total-model).

Proof: (1) Exact, jointly conservative evaluations and e_p a^* = a_p^* show that
 a^* is exact. Transpose the face transitions by the module adjunctions; paired
 deletions give d_h² = 0 and naturality gives d_h d_v = d_v d_h. Thus the existing
 total has differential d_h + (-1)^p d_v and finite diagonals on nonnegative inputs.
(2) Use the exact free evaluation adjoints (semisimplicial-evaluation-free-adjoint)
 to resolve a^*H by the sums labelled by increasing vertex tuples. In component m,
 prepend vertex 0 when absent and give zero when present. Deleting vertices shows
 ∂s + s∂ = 1, including the augmented degree. Exact conservative evaluations detect
 exactness. (3) Hom into a total injective I is exact, since a cocycle factors through
 an image and extends across its inclusion. The adjunctions identify this with the
 augmented face complex of Hom_R(H,a_{p,*}e_pI). Testing with each kernel gives exact
 augmented rows in modules (module-pullback-pushforward-adjunction).
(4) The ringed total module category is Grothendieck, hence has nonnegative injective
 resolutions and ambient unbounded K-injective resolutions. Exact free evaluation
 adjoints make evaluations of total injectives injective; bounded-below injective
 complexes are K-injective. The right-derived comparison on such a resolution I
 is rho_I = (RF(Qr_I))^{-1} eta_I.
(5) The row augmentation alpha_I : a_*I -> Tot(A_I) is a quasi-isomorphism by
 first-quadrant total comparison. Interchanging indices uses (-1)^(pq), equal to 1
 on the augmentation edge. Put c_I = rho_I (Q alpha_I)^{-1}.
(6) The K-injective Hom bijection represents Qr_I (Qr_J)^{-1} by u : J -> I.
 Its composite with r_J equals r_I because homotopies from degree-zero objects into
 nonnegative complexes vanish. Each evaluated u is a homotopy equivalence between
 bounded-below injective complexes, preserved by a_{p,*}. Column comparison makes
 T(u) a quasi-isomorphism; put c_J = c_I QT(u).
(7) Two choices of u are homotopic. Their total homotopy is (-1)^p a_{p,*}e_ph,
 whose horizontal terms cancel. Comparison between total injective resolutions,
 naturality of alpha and the derived unit show independence of I as well.
(8) For any augmented map w over f, represent the induced map between total injective
 resolutions by v. The maps u' w and v u are homotopic, and their total maps agree
 after localization. Naturality of alpha and eta gives c_J' QT(w) = RF(Qf[0]) c_J.
(9) For each extending t, adjointness gives b_t in face degree zero: its two degree-one
 cofaces agree. For the total injective comparison u, termwise adjunction gives s
 with T(u)b_t = alpha_I s, so c_J Qb_t = rho_I Qs.
(10) Exact-functor derivation and resolving-derived-adjunction-normalization identify
 eta_I Qs with the derived transpose of Q(ut). The extension equation and naturality
 then give exactly the displayed normalization after composition with Qr_K.
No covering, cartesian-transition or quasi-coherence condition is used. -/
theorem face_component_injective_total_model
    (V : AugmentationPresentation P S A)
    (faceExact : ∀ (i j : SemiSimplexCategoryᵒᵖ) (a : i ⟶ j),
      PreservesFiniteLimits (P.pullback a).ordinary ∧
        PreservesFiniteColimits (P.pullback a).ordinary)
    (augmentationExact : ∀ i : SemiSimplexCategoryᵒᵖ,
      PreservesFiniteLimits (V.components i).ordinary ∧
        PreservesFiniteColimits (V.components i).ordinary)
    (RF : (R.total h).D ⥤ S.D)
    (η : V.map.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (R.total h).modules (.up ℤ))) :
    Nonempty (FaceComponentTotalModel V RF η) := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal
