module

public import Sheaf.Algebra.Homology.SingleDegreeCoefficientConeCancellation
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward

/-! # Global single-degree coefficient cancellation

Source: agent-formulated prerequisite for the Kiehl paragraph after Stacks Tag 0CSD,
perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation).

The main theorem is `sheafSingleDegreeCoefficientCancellation`. The preceding definitions
construct its scalar action, affine restriction comparison, and polynomial cone condition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable section
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The ordinary scalar-action map on the affine coefficient base, obtained from the
identity on A by the tilde/Gamma and tensor-pullback adjunctions.
Source: Stacks Tags 01I9 and 079W, coefficient normalization in the Kiehl prerequisite.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationOrdinaryAction {E A : Type u} [CommRing E] [CommRing A]
    (φ : E →+* A) :
    (Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))).obj
        (tilde ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))) ⟶
      SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace) :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (Spec.map (CommRingCat.ofHom φ)))).homEquiv _ _).symm
    ((tilde.adjunction.homEquiv _ _).symm
      ((ModuleCat.restrictScalars φ).map (tilde.isoTop (R := .of A) (ModuleCat.of A A)).hom ≫
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom φ)).inv.app
          (tilde (ModuleCat.of A A))))

/-- Localize the recorded left-derived counit on a complex concentrated in degree zero,
then apply the specified ordinary pullback morphism. This fixes the scalar action even
for nonflat maps. Source: Stacks 06YJ and 079W.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationSingleMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (a : (Scheme.Modules.tensorPullback g).obj M ⟶ N) :
    (derivedPullback.{u, w} g).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N := by
  letI := SingleComplexBaseChange.tensorPullbackAdditive g
  exact (schemeHomPullbackCounitData g).counit.app
      ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.tensorPullback g).mapHomotopyCategoryFactors (.up ℤ)).hom.app
        ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback g) (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctor _ 0).map a

/-- The derived unit compared with the structure sheaf in degree zero. The recorded
derived monoidal construction takes this object as its unit, so the comparison is identity.
Source: Stacks 06YH.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationUnitIso (X : Scheme.{u}) :
    𝟙_ (schemeDerivedCategory.{u, w} X) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (moduleRings X.toRingedSpace)) :=
  Iso.refl _


/-- Pull back the coefficient action to X_A, retaining the canonical composition
comparisons and the original left-derived counits. Source: Stacks 06YJ, 079U, 079W
and 0D5S; the adjunction normalization in the Kiehl prerequisite.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationScalar {E A : Type u} [CommRing E] [CommRing A]
    (φ : E →+* A) {Z Y : Scheme.{u}} (π : Z ⟶ Y)
    (q : Y ⟶ Spec (.of E)) (qA : Z ⟶ Spec (.of A))
    (h : π ≫ q = qA ≫ Spec.map (CommRingCat.ofHom φ)) :
    (derivedPullback.{u, w} π).obj ((derivedPullback.{u, w} q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (tilde ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))))) ⟶
      𝟙_ (schemeDerivedCategory.{u, w} Z) :=
  (recordedDerivedPullbackComposition π q).hom.app _ ≫
    (eqToIso (congrArg (fun f ↦ derivedPullback.{u, w} f) h)).hom.app _ ≫
    (recordedDerivedPullbackComposition qA (Spec.map (CommRingCat.ofHom φ))).inv.app _ ≫
    (derivedPullback.{u, w} qA).map
      (coefficientCancellationSingleMap (Spec.map (CommRingCat.ofHom φ)) _ _
        (coefficientCancellationOrdinaryAction φ)) ≫
    coefficientCancellationSingleMap qA _ _ (Scheme.Modules.tensorPullbackObjUnitToUnit qA) ≫
    (coefficientCancellationUnitIso Z).inv

/-- The actual adjunction-normalized coefficient action on a supplied coherent witness.
It splits pullback of tensor by the original-counit tensor comparison, applies the
coefficient scalar map and the transpose of gamma, and uses the left unitor.
Source: the displayed definition of theta in the Kiehl prerequisite after Stacks 0CSD.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationTheta {E A : Type u} [CommRing E] [CommRing A]
    (φ : E →+* A) {Z Y : Scheme.{u}} (π : Z ⟶ Y)
    (q : Y ⟶ Spec (.of E)) (qA : Z ⟶ Spec (.of A))
    (h : π ≫ q = qA ≫ Spec.map (CommRingCat.ofHom φ))
    (F : schemeDerivedCategory.{u, w} Y) (K : schemeDerivedCategory.{u, w} Z)
    (γ : F ⟶ (schemeDerivedDirectImage π).obj K) :
    (derivedPullback.{u, w} q).obj ((DerivedCategory.singleFunctor _ 0).obj
        (tilde ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)))) ⊗ F ⟶
      (schemeDerivedDirectImage π).obj K :=
  (schemeHomOriginalPullbackAdjunction π).homEquiv _ _
    ((schemeHomOriginalTensorPullbackIso π).hom.app (_, F) ≫
      (coefficientCancellationScalar φ π q qA h ⊗ₘ
        ((schemeHomOriginalPullbackAdjunction π).homEquiv F K).symm γ) ≫ (λ_ K).hom)


/-- The associated-sheaf complex, with the exact tilde functor applied termwise.
Source: Stacks 06Z0 (blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
abbrev coefficientCancellationTildeComplex {S : Type u} [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) :=
  (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} S ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of S)).toRingedSpace))
      (tilde.functor (.of S))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P

/-- The module-derived arrow represented by a map to termwise restriction of scalars.
Source: Stacks 05G3 and 06Z0.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationModuleMap {S B : Type u} [CommRing S] [CommRing B]
    (φ : S →+* B) {P : CochainComplex (ModuleCat.{u} S) ℤ}
    {N : CochainComplex (ModuleCat.{u} B) ℤ}
    (γ : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj N) :
    DerivedCategory.Q.obj P ⟶ (ModuleCat.derivedRestrictScalars φ).obj
      (DerivedCategory.Q.obj N) :=
  DerivedCategory.Q.map γ ≫ (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app N

/-- The affine tilde/pullback isomorphism, constructed by uniqueness of left adjoints
from the identity-on-sections right-adjoint comparison. Source: Stacks 01I9.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationTildePullback {S B : Type u} [CommRing S] [CommRing B]
    (φ : S →+* B) :
    tilde.functor (.of S) ⋙ Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ)) ≅
      ModuleCat.extendScalars φ ⋙ tilde.functor (.of B) :=
  ((tilde.adjunction.comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (Spec.map (CommRingCat.ofHom φ))))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom φ))).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ).comp tilde.adjunction)

/-- The affine transpose on complexes, using extension/restriction adjunction and the
canonical tilde/pullback comparison on each term. Source: Stacks 01I9 and 079W.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationComplexTranspose {S B : Type u} [CommRing S] [CommRing B]
    (φ : S →+* B) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (N : CochainComplex (ModuleCat.{u} B) ℤ)
    (γ : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj N) :
    ((Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex
      (.up ℤ)).obj (coefficientCancellationTildeComplex P) ⟶
        coefficientCancellationTildeComplex N := by
  letI := SingleComplexBaseChange.tensorPullbackAdditive (Spec.map (CommRingCat.ofHom φ))
  letI : (tilde.functor (.of S) : ModuleCat.{u} S ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of S)).toRingedSpace)).Additive :=
    ⟨by intros; exact tilde.map_add _ _⟩
  letI : (tilde.functor (.of B) : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)).Additive :=
    ⟨by intros; exact tilde.map_add _ _⟩
  letI := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  exact (Functor.mapHomologicalComplexCompIso (F := tilde.functor (.of S))
    (G := Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ)))
    (Iso.refl _) (.up ℤ)).hom.app P ≫
    (NatIso.mapHomologicalComplex (coefficientCancellationTildePullback φ) (.up ℤ)).hom.app P ≫
    (Functor.mapHomologicalComplexCompIso (F := ModuleCat.extendScalars φ)
      (G := tilde.functor (.of B)) (Iso.refl _) (.up ℤ)).inv.app P ≫
    ((tilde.functor (.of B)).mapHomologicalComplex (.up ℤ)).map
      ((((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).homEquiv
        P N).symm γ)

/-- The sheaf-derived transpose of the affine module map, via the original left-derived
counit. For a K-flat P this is the actual affine derived pullback map, with no flatness
assumption on S to B. Source: Stacks 08DW, 06Z0 and 079W.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationAffineTranspose {S B : Type u} [CommRing S] [CommRing B]
    (φ : S →+* B) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (N : CochainComplex (ModuleCat.{u} B) ℤ)
    (γ : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj N) :
    (derivedPullback.{u, w} (Spec.map (CommRingCat.ofHom φ))).obj
      (DerivedCategory.Q.{w, u, u + 1}.obj (coefficientCancellationTildeComplex P)) ⟶
        DerivedCategory.Q.{w, u, u + 1}.obj (coefficientCancellationTildeComplex N) := by
  letI := SingleComplexBaseChange.tensorPullbackAdditive (Spec.map (CommRingCat.ofHom φ))
  exact (schemeHomPullbackCounitData (Spec.map (CommRingCat.ofHom φ))).counit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (coefficientCancellationTildeComplex P)) ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.tensorPullback (Spec.map (CommRingCat.ofHom φ))).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app (coefficientCancellationTildeComplex P)) ≫
    DerivedCategory.Q.map (coefficientCancellationComplexTranspose φ P N γ)

/-- The canonical commutative-square comparison of derived pullbacks, with its direction
from the bottom then left pullback to the right then top pullback. Source: Stacks 0D5S.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationSquare {X Y Z W : Scheme.{u}}
    (π : Z ⟶ X) (v : Y ⟶ X) (p : W ⟶ Y) (vA : W ⟶ Z)
    (h : p ≫ v = vA ≫ π) :
    derivedPullback.{u, w} v ⋙ derivedPullback.{u, w} p ≅
      derivedPullback.{u, w} π ⋙ derivedPullback.{u, w} vA :=
  recordedDerivedPullbackComposition p v ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback.{u, w} f) h) ≪≫
    (recordedDerivedPullbackComposition vA π).symm


/-- The polynomial-chart cone condition, written using universal derived extension and
its uniquely normalized transpose. The tensor presentation Q_D tensor_D A is canonically
A[x_1,...,x_s] (MvPolynomial.algebraTensorAlgEquiv and symmetry). This predicate only
packages the displayed cone and its two cohomology conditions in the node.
Source: the agent-formulated prerequisite after Stacks 0CSD; affine normalization as
in lem-sfb-single-degree-coefficient-cone-cancellation.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation). -/
def coefficientCancellationPolynomialCondition
    (D A S : Type u) [CommRing D] [CommRing A] [CommRing S]
    [Algebra D A] [Algebra D S] (s : ℕ) (q : MvPolynomial (Fin s) D →ₐ[D] S)
    (L : DerivedCategory (ModuleCat.{u} S))
    (K : DerivedCategory (ModuleCat.{u} (S ⊗[D] A)))
    (γ : L ⟶ (ModuleCat.derivedRestrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[D] A)).obj K) (n : ℤ) : Prop :=
  ∃ (T : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)))
    (η : (ModuleCat.derivedRestrictScalars q.toRingHom).obj L ⟶
      (ModuleCat.derivedRestrictScalars (Algebra.TensorProduct.includeLeftRingHom :
        MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)).obj T),
    ModuleCat.IsDerivedBaseChange η ∧
    ∃ θ : T ⟶ (ModuleCat.derivedRestrictScalars
        (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom).obj K,
      (η ≫ (ModuleCat.derivedRestrictScalars (Algebra.TensorProduct.includeLeftRingHom :
          MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)).map θ ≫
        (ModuleCat.coefficientConeRestrictionSquareIso q.toRingHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[D] A)
          (Algebra.TensorProduct.includeLeftRingHom :
            MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)
          (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom
          (Algebra.TensorProduct.map_comp_includeLeftRingHom q (AlgHom.id D A)).symm).inv.app K =
        (ModuleCat.derivedRestrictScalars q.toRingHom).map γ) ∧
      ∃ (C : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)))
        (ι : (ModuleCat.derivedRestrictScalars
          (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom).obj K ⟶ C)
        (δ : C ⟶ T⟦(1 : ℤ)⟧),
        Triangle.mk θ ι δ ∈ distTriang _ ∧
        (∀ i : ℤ, n < i → IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)) i).obj C)) ∧
        Module.Finite (MvPolynomial (Fin s) D ⊗[D] A)
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)) n).obj C)

/-- A finite polynomial-chart top obstruction can be cancelled globally in one degree.
The affine data P,N,gamma are representatives of the stipulated L_j,K_j,gamma_j;
the equation hgamma identifies their actual adjunction transposes. No replacement
of gamma by unrelated local arrows is permitted.

Source: agent-formulated global prerequisite for the Kiehl paragraph after Stacks
Tag 0CSD, perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general.
The paragraph does not state this lemma; the primary Kiehl descente proof is WANTED.
(blueprint: lem-sfb-sheaf-single-degree-coefficient-cancellation).

Proof plan (the node's five steps):
1. Every S_j is Noetherian by finite-type permanence. Coherent cohomology of F on
an affine chart corresponds to finitely generated module cohomology in the same
finite interval (pqf-lem-coherent-ft-locnoeth and the affine section criterion).
Apply lem-sfb-single-degree-coefficient-cone-cancellation to the polynomial cone.
It gives a finite coefficient stage and a bounded finite-cohomology approximation
on each chart whose action cone vanishes in degrees at least n.
2. Use lem-pc-affine-qcoh-derived-equivalence and finite-type Noetherian permanence
to sheafify these approximations. The affine pushforward resolution comparison
and lem-pc-affine-derived-pullback-tensor-tilde identify their action maps with
the adjunction-normalized sheaf maps: resolve A, apply gamma, and multiply by A.
Thus each chart satisfies the cutoff-n approximation assertion.
3. Retain the supplied global F,gamma. Normalize their action at the original
coefficient stage D. Its restriction agrees with each polynomial cone after
forgetting scalars, since Q_j is D-free on monomials: a K-flat Q_j resolution
is K-flat over D, and Q_{j,A} tensor_{Q_j} P = A tensor_D P.
Both composites apply gamma_j and the same scalar multiplication. Consequently
the global cone is quasi-coherent and vanishes above n: F,gamma is the global
cutoff-(n+1) witness.
4. Induct over finite unions of the affine opens. At each binary step retain
the restriction of this same original global witness. The two cutoff-n witnesses
and the global cutoff-(n+1) witness satisfy
lem-sfb-global-witness-one-degree-binary-patching. Quasi-compactness follows
from the finite affine cover, separatedness and finite type restrict to these
opens, and the affine formulas and lem-pc-module-pushforward-open-restriction
preserve the action normalization. At the last union obtain D',F',gamma' below.
5. For the empty cover X is empty. Take D'=D and the zero witness; all module
sheaves, action sources, targets and cones are zero. Zero rings, zero or redundant
charts, zero variables and arbitrary integer n are allowed throughout. Negative
Tor remains; neither a flatness hypothesis nor a claim below n is used. -/
theorem sheafSingleDegreeCoefficientCancellation
    (D A : Type u) [CommRing D] [CommRing A] [IsNoetherianRing D] [Algebra D A]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of D))
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (r : ℕ) (S : Fin r → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra D (S j)]
    (s : Fin r → ℕ) (Q : ∀ j, MvPolynomial (Fin (s j)) D →ₐ[D] S j)
    (hQ : ∀ j, Function.Surjective (Q j))
    (v : ∀ j, Spec (.of (S j)) ⟶ X) [∀ j, IsOpenImmersion (v j)]
    (hv : ∀ j, v j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap D (S j))))
    (hcover : ∀ x : X, ∃ j : Fin r, ∃ z : Spec (.of (S j)), v j z = x)
    (K : schemeDerivedQCohCategory.{u, w}
      (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D A)))))
    (F : schemeDerivedCategory.{u, w} X)
    (hFbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj F))
    (hFcoherent : ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj F))
    (γ : F ⟶ (schemeDerivedDirectImage
      (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D A))))).obj K.obj)
    (vA : ∀ j, Spec (.of (S j ⊗[D] A)) ⟶
      pullback q (Spec.map (CommRingCat.ofHom (algebraMap D A))))
    (hvA : ∀ j,
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A)) ≫ v j =
      vA j ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D A))))
    (hvAcoeff : ∀ j, vA j ≫
      pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap D A))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[D] S j ⊗[D] A).toRingHom))
    (P : ∀ j, CochainComplex (ModuleCat.{u} (S j)) ℤ)
    (hP : ∀ j, (HomologicalComplex.quasiIso (ModuleCat.{u} (S j)) (.up ℤ)).kFlat (P j))
    (N : ∀ j, CochainComplex (ModuleCat.{u} (S j ⊗[D] A)) ℤ)
    (γj : ∀ j, P j ⟶ ((ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A)).mapHomologicalComplex
        (.up ℤ)).obj (N j))
    (eF : ∀ j, (DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings (Spec (.of (S j))).toRingedSpace))).obj
        (coefficientCancellationTildeComplex (P j)) ≅
      (derivedPullback.{u, w} (v j)).obj F)
    (eK : ∀ j, (DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings (Spec (.of (S j ⊗[D] A))).toRingedSpace))).obj
        (coefficientCancellationTildeComplex (N j)) ≅
      (derivedPullback.{u, w} (vA j)).obj K.obj)
    (hgamma : ∀ j,
      coefficientCancellationAffineTranspose
          (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A)
          (P j) (N j) (γj j) ≫ (eK j).hom =
        (derivedPullback.{u, w} (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A)))).map (eF j).hom ≫
        (coefficientCancellationSquare
          (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D A)))) (v j)
          (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A)))
          (vA j) (hvA j)).hom.app F ≫
        (derivedPullback.{u, w} (vA j)).map
          (((schemeHomOriginalPullbackAdjunction
            (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D A))))).homEquiv
              F K.obj).symm γ))
    (n : ℤ)
    (hcones : ∀ j, coefficientCancellationPolynomialCondition D A (S j) (s j) (Q j)
      (DerivedCategory.Q.obj (P j)) (DerivedCategory.Q.obj (N j))
      (coefficientCancellationModuleMap
        (Algebra.TensorProduct.includeLeftRingHom : S j →+* S j ⊗[D] A) (γj j)) n) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra D E) (_ : Algebra E A)
      (_ : IsScalarTower D E A), Algebra.FiniteType D E ∧
      ∃ (π' : pullback q (Spec.map (CommRingCat.ofHom (algebraMap D A))) ⟶
          pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E))))
        (hπ' : π' ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap D E))) =
          pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap D A))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap E A))),
        (π' ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D E))) =
          pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap D A)))) ∧
        ∃ (F' : schemeDerivedCategory.{u, w}
            (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))))
          (γ' : F' ⟶ (schemeDerivedDirectImage π').obj K.obj),
          (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings
              (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))).toRingedSpace))
                i).obj F')) ∧
          (∀ i : ℤ, RingedSpace.IsCoherent
            (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))).toRingedSpace
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings
              (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))).toRingedSpace))
                i).obj F')) ∧
          ∃ (C' : schemeDerivedQCohCategory.{u, w}
              (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))))
            (ι' : (schemeDerivedDirectImage π').obj K.obj ⟶ C'.obj)
            (δ' : C'.obj ⟶
              ((derivedPullback.{u, w} (pullback.snd q
                (Spec.map (CommRingCat.ofHom (algebraMap D E))))).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  (tilde ((ModuleCat.restrictScalars (algebraMap E A)).obj
                    (ModuleCat.of A A)))) ⊗ F')⟦(1 : ℤ)⟧),
            Triangle.mk
              (coefficientCancellationTheta (algebraMap E A) π'
                (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap D E))))
                (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap D A))))
                hπ' F' K.obj γ') ι' δ' ∈ distTriang _ ∧
            ∀ i : ℤ, n ≤ i → IsZero ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings
                (pullback q (Spec.map (CommRingCat.ofHom (algebraMap D E)))).toRingedSpace))
                  i).obj C'.obj) := by
  sorry

end
end AlgebraicGeometry
