module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.Paper.ModuleCohomologyCupProduct
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.ZariskiLocalDualityAdjunction
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.AlgebraicGeometry.PolynomialDualityPresentationData

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel
import Sheaf.AlgebraicGeometry.SmoothPairRegularEquations
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Sheaf.AlgebraicGeometry.LciCotangentPresentation
import Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison
import Sheaf.AlgebraicGeometry.LciDeterminantDescentSmooth
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Sheaf.CategoryTheory.DerivedHomologyInjective
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated

/-! # Smooth proper coherent trace pairings

Source: Stacks Project, duality.tex, Tags 0FVV, 0FVW, 0FVY, 0FW0, 0B6J and 0AAB.
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing).

All cohomology below is the right-derived global-sections functor on Zariski module
sheaves. Scalar restriction changes only the coefficient action. The auxiliary
records spell out the maps and the compatibilities of this single assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.SmoothProperCoherentTrace

/-- Cohomology with its action through the displayed affine structure map.
Source: Stacks 01DZ, 0FVV
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev cohomology {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (F : Z.Modules) (j : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ a.appTop).hom)).obj
    ((RingedSpace.moduleCohomology Z.toRingedSpace j).obj F)

/-- The top exterior power of the actual relative differential sheaf, also in degree zero.
Source: Stacks 0BRT, 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev omega {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (d : ℕ) : Z.Modules :=
  Scheme.Modules.exteriorSheaf a.relativeDifferentials d

/-- The specified Serre-dual coefficient, using the existing sheaf Hom and tensor.
Source: Stacks 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev dualCoefficient {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (d : ℕ) (E : Z.Modules) : Z.Modules :=
  Scheme.Modules.dual E ⊗ omega a d

/-- Evaluation in exactly the order e tensor (lambda tensor w).
Source: Stacks 0FVY, 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def evaluation {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (d : ℕ) (E : Z.Modules) :
    E ⊗ dualCoefficient a d E ⟶ omega a d :=
  (α_ E (Scheme.Modules.dual E) (omega a d)).inv ≫
    (Scheme.Modules.dualEvaluation E ▷ omega a d) ≫ (λ_ (omega a d)).hom

/-- Coefficient functoriality on the same derived-functor cohomology.
Source: Stacks 01DZ
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def coefficientMap {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) {F G : Z.Modules} (v : F ⟶ G) (j : ℕ) :
    cohomology a F j →ₗ[A] cohomology a G j :=
  ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ a.appTop).hom)).map
    ((RingedSpace.moduleCohomology Z.toRingedSpace j).map v)).hom

/-- The pullback followed by its specified coefficient map, as an additive function.
Its construction is the recorded cohomology h-map of the tensor-adjunction unit.
Source: Stacks 01F7
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def pull {A B : Type u} [CommRing A] [CommRing B] {Z W : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (b : W ⟶ Spec (.of B)) (g : W ⟶ Z)
    (F : Z.Modules) (G : W.Modules)
    (v : (Scheme.Modules.tensorPullback g).obj F ⟶ G) (j : ℕ)
    (x : cohomology a F j) : cohomology b G j :=
  (Scheme.Modules.moduleCohomologyFMap g
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app F ≫
      (Scheme.Modules.pushforward g).map v) j) x

/-- Cup product followed by evaluation and trace, with the index equality explicit.
The unique cup is selected by its resolution characterization, which fixes the map.
Source: Stacks 0FVY, 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def pairing {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (d : ℕ) (E : Z.Modules)
    (t : cohomology a (omega a d) d →ₗ[A] A)
    (i j : ℕ) (h : i + j = d)
    (x : cohomology a E i) (y : cohomology a (dualCoefficient a d E) j) : A :=
  t (coefficientMap a (evaluation a d E) d
    ((eqToHom (congrArg (fun n ↦ RingedSpace.moduleCohomology Z.toRingedSpace n) h)).app
      (E ⊗ dualCoefficient a d E)
        ((Classical.choose (Scheme.Modules.exists_unique_moduleCupProduct
          E (dualCoefficient a d E) i j)) x y)))


/-- The differential comparison, fixed on universal differentials, and its top wedge.
Source: Stacks 01V0, 0BRT
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure DifferentialIso {Z W S T : Scheme.{u}} (a : Z ⟶ S) (b : W ⟶ T)
    (g : W ⟶ Z) (d : ℕ) where
  differential : (Scheme.Modules.tensorPullback g).obj a.relativeDifferentials ≅
    b.relativeDifferentials
  differential_normal : ∀ (U : Z.Opens) (r : Γ(Z, U)),
    differential.hom.app (g ⁻¹ᵁ U)
      (Scheme.Modules.tensorPullbackSection g a.relativeDifferentials U
        (a.relativeDifferentialsDerivation.d (X := op U) r)) =
      b.relativeDifferentialsDerivation.d (X := op (g ⁻¹ᵁ U)) (g.app U r)
  top : (Scheme.Modules.tensorPullback g).obj
      (Scheme.Modules.exteriorSheaf a.relativeDifferentials d) ≅
    Scheme.Modules.exteriorSheaf b.relativeDifferentials d
  top_normal : ∀ (U : Z.Opens) (s : Fin d → Γ(a.relativeDifferentials, U)),
    top.hom.app (g ⁻¹ᵁ U)
      (Scheme.Modules.tensorPullbackSection g
        (Scheme.Modules.exteriorSheaf a.relativeDifferentials d) U
        (Scheme.Modules.exteriorSheafSection a.relativeDifferentials d U s)) =
      Scheme.Modules.exteriorSheafSection b.relativeDifferentials d (g ⁻¹ᵁ U)
        (fun i ↦ differential.hom.app (g ⁻¹ᵁ U)
          (Scheme.Modules.tensorPullbackSection g a.relativeDifferentials U (s i)))

/-- The tensorator fixed by the recorded pure-tensor formula.
Source: Stacks 01CA
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def tensorComparison {Z W : Scheme.{u}} (g : W ⟶ Z) (F G : Z.Modules) :
    (Scheme.Modules.tensorPullback g).obj (F ⊗ G) ≅
      (Scheme.Modules.tensorPullback g).obj F ⊗ (Scheme.Modules.tensorPullback g).obj G :=
  Classical.choose (Scheme.Modules.module_pullback_tensor g) F G

/-- Transport on the dual coefficient. Evaluation characterizes the dual of eta inverse,
so this record cannot substitute the dual of eta or a rescaled comparison.
Source: Stacks 0FW0, tensor-Hom evaluation
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure DualIso {A B : Type u} [CommRing A] [CommRing B] {Z W : Scheme.{u}}
    (a : Z ⟶ Spec (.of A)) (b : W ⟶ Spec (.of B)) (g : W ⟶ Z) (d : ℕ)
    (E : Z.Modules) (F : W.Modules) (eta : (Scheme.Modules.tensorPullback g).obj E ≅ F)
    (delta : DifferentialIso a b g d) where
  coefficient : (Scheme.Modules.tensorPullback g).obj (dualCoefficient a d E) ≅
    dualCoefficient b d F
  evaluation_square :
    (Scheme.Modules.tensorPullback g).map (evaluation a d E) ≫ delta.top.hom =
      (tensorComparison g E (dualCoefficient a d E)).hom ≫
        (eta.hom ⊗ₘ coefficient.hom) ≫ evaluation b d F

/-- A bilinear cup-evaluation pairing and its two linear-dual transposes.
Source: Stacks 0FVY, 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def IsPerfect {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (d : ℕ)
    (t : cohomology f (omega f d) d →ₗ[k] k) (E : Y.Modules)
    (i j : ℕ) (h : i + j = d) : Prop :=
  FiniteDimensional k (cohomology f E i) ∧
  FiniteDimensional k (cohomology f (dualCoefficient f d E) j) ∧
  ∃ P : cohomology f E i →ₗ[k] cohomology f (dualCoefficient f d E) j →ₗ[k] k,
    (∀ x y, P x y = pairing f d E t i j h x y) ∧
    Function.Bijective P ∧ Function.Bijective P.flip


/-- Sheafified graph Koszul complex in degrees -d through zero.
Source: Stacks 0622, 0E2E
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev graphComplex {T : Type u} [CommRing T] (d : ℕ) (r : Fin d → T) :=
  ((tilde.functor (.of T)).mapHomologicalComplex (.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex T d r).extend ComplexShape.embeddingDownNat)

/-- The ordered top or empty wedge in the actual extended Koszul complex.
Source: Stacks 0622
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def graphWedge {T : Type u} [CommRing T] (d : ℕ) (r : Fin d → T) (n : ℕ)
    (v : Fin n → Fin d →₀ T) :
    ((ExteriorAlgebra.koszulComplex T d r).extend ComplexShape.embeddingDownNat).X
      (-(n : ℤ)) :=
  ((ExteriorAlgebra.koszulComplex T d r).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl).inv (exteriorPower.ιMulti T n v)

section Derived



/-- A module placed in degree zero, in the existing scheme derived category.
Source: Stacks 05RR
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev single {Z : Scheme.{u}} (F : (SheafOfModules.{u} (moduleRings Z.toRingedSpace))) :
    schemeDerivedCategory.{u, u} Z :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj F

/-- The differential line shifted by the relative dimension.
Source: Stacks 0BRT
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev shiftedOmega {Z S : Scheme.{u}} (a : Z ⟶ S) (d : ℕ) :
    schemeDerivedCategory.{u, u} Z :=
  (single (Scheme.Modules.exteriorSheaf a.relativeDifferentials d))⟦(d : ℤ)⟧

/-- The structure module pushed along the diagonal.
Source: Stacks 0E2E
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev diagonalModule {Z S : Scheme.{u}} (a : Z ⟶ S) : (pullback a a).Modules :=
  (Scheme.Modules.pushforward (pullback.diagonal a)).obj
    (SheafOfModules.unit Z.ringCatSheaf)

/-- Restrict a degree-d class using exact open restriction and its standard shifts.
Source: Stacks 08BT
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def restrictClass {P V : Scheme.{u}} (j : V ⟶ P) [IsOpenImmersion j]
    {F G : (SheafOfModules.{u} (moduleRings P.toRingedSpace))} (d : ℕ) (c : single F ⟶ (single
        G)⟦(d : ℤ)⟧) :
    single ((Scheme.Modules.restrictFunctor j).obj F) ⟶
      (single ((Scheme.Modules.restrictFunctor j).obj G))⟦(d : ℤ)⟧ :=
  ((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).inv.app F ≫
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory.map c ≫
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.commShiftIso
      (d : ℤ)).hom.app (single G) ≫
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).hom.app G)
      ⟦(d : ℤ)⟧'

/-- Normalize the diagonal class on an affine neighbourhood of every diagonal point.
The augmentation is one on one; the ordered top Koszul cocycle is the wedge of the
relative derivatives of those same equations. This is the evaluation-normalized graph
class, including degree zero; no orientation or scalar remains free.
Source: Stacks 0E2E, 0BZI, 0BZJ
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def IsNormalizedDiagonal {Z S : Scheme.{u}} (a : Z ⟶ S) (d : ℕ)
    (c : single (diagonalModule a) ⟶ shiftedOmega (pullback.snd a a) d) : Prop :=
  ∀ x : Z, ∃ (T : Type u) (_ : CommRing T)
    (j : Spec (.of T) ⟶ pullback a a) (_ : IsOpenImmersion j),
    (pullback.diagonal a) x ∈ j ''ᵁ (⊤ : (Spec (.of T)).Opens) ∧
    ∃ (r : Fin d → T)
      (e : graphComplex d r ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((Scheme.Modules.restrictFunctor j).obj (diagonalModule a)))
      (z : graphComplex d r ⟶ (CochainComplex.singleFunctor _ (-(d : ℤ))).obj
        ((Scheme.Modules.restrictFunctor j).obj
          (Scheme.Modules.exteriorSheaf (pullback.snd a a).relativeDifferentials d))),
      QuasiIso e ∧
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        ((Scheme.Modules.restrictFunctor j).obj (diagonalModule a))).hom.app ⊤
        ((e.f 0).app ⊤ (tilde.toOpen (R := .of T) _ ⊤
          (graphWedge d r 0 Fin.elim0))) =
        ((diagonalModule a).restrictAppIso j ⊤).inv
          (1 : Γ(Z, (pullback.diagonal a) ⁻¹ᵁ (j ''ᵁ ⊤))) ∧
      ((Scheme.Modules.restrictAppIso j
        (Scheme.Modules.exteriorSheaf (pullback.snd a a).relativeDifferentials d) ⊤).hom
        ((HomologicalComplex.singleObjXSelf (.up ℤ) (-(d : ℤ))
          ((Scheme.Modules.restrictFunctor j).obj
            (Scheme.Modules.exteriorSheaf (pullback.snd a a).relativeDifferentials d))).hom.app ⊤
                ((z.f (-(d : ℤ))).app ⊤ (tilde.toOpen (R := .of T) _ ⊤
            (graphWedge d r d (fun i ↦ Finsupp.single i 1)))))) =
        Scheme.Modules.exteriorSheafSection (pullback.snd a a).relativeDifferentials d
          (j ''ᵁ ⊤) (fun i ↦ (pullback.snd a a).relativeDifferentialsDerivation.d
            (X := op (j ''ᵁ ⊤)) ((j.appIso ⊤).inv
              ((Scheme.ΓSpecIso (.of T)).inv (r i)))) ∧
      DerivedCategory.Q.map e ≫
        (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings (Spec (.of
            T)).toRingedSpace)) 0).inv.app _ ≫
        restrictClass j d c =
      DerivedCategory.Q.map z ≫
        (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings (Spec (.of
            T)).toRingedSpace)) (-(d : ℤ))).inv.app _ ≫
        ((DerivedCategory.singleFunctors.{u} (SheafOfModules.{u} (moduleRings (Spec (.of
            T)).toRingedSpace))).shiftIso
          (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)).inv.app _


/-- The ordinary-to-derived direct-image map on a single module, from the recorded unit.
Source: Stacks 079V
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def directImageUnit {Z S : Scheme.{u}} (a : Z ⟶ S) (F : (SheafOfModules.{u} (moduleRings
    Z.toRingedSpace))) :
    single ((Scheme.Modules.pushforward a).obj F) ⟶
      (schemeDerivedDirectImage a).obj (single F) :=
  (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings S.toRingedSpace))
      0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward a)
        (.up ℤ) 0).inv.app F) ≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))).inv.app
        _ ≫
    (RingedSpace.moduleDirectImage a.toLRSHom.toShHom).rightDerivedFunctorUnit.app _ ≫
    (schemeDerivedDirectImage a).map
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings
          Z.toRingedSpace))).hom.app _ ≫
        (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
            0).inv.app F)

/-- The pinned left-derived tensor counit on an ordinary module in any degree.
Source: Stacks 06YJ, 0D5S
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def derivedCoefficientMap {Z W : Scheme.{u}} (g : W ⟶ Z)
    (F : (SheafOfModules.{u} (moduleRings Z.toRingedSpace))) (G : (SheafOfModules.{u} (moduleRings
        W.toRingedSpace)))
    (v : (Scheme.Modules.tensorPullback g).obj F ⟶ G) (n : ℤ) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings
        Z.toRingedSpace)) n).obj F) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings W.toRingedSpace)) n).obj G :=
  (derivedPullback g).map
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
        n).hom.app F ≫
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings
          Z.toRingedSpace))).inv.app _) ≫
    (SingleComplexBaseChange.counit g).app _ ≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings W.toRingedSpace))).hom.app
        _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.tensorPullback g)
        (.up ℤ) n).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (moduleRings W.toRingedSpace))
        n).inv.app _ ≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings W.toRingedSpace)) n).map v

/-- The same comparison with the standard cohomological shift convention.
Source: Stacks 0BRT, 06YJ
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def derivedOmegaMap {Z W S T : Scheme.{u}} (a : Z ⟶ S) (b : W ⟶ T)
    (g : W ⟶ Z) (d : ℕ) (delta : DifferentialIso a b g d) :
    (derivedPullback g).obj (shiftedOmega a d) ⟶ shiftedOmega b d :=
  (derivedPullback g).map
    (((DerivedCategory.singleFunctors (SheafOfModules.{u} (moduleRings Z.toRingedSpace))).shiftIso
      (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)).hom.app _) ≫
    derivedCoefficientMap g _ _ delta.top.hom (-(d : ℤ)) ≫
    ((DerivedCategory.singleFunctors (SheafOfModules.{u} (moduleRings W.toRingedSpace))).shiftIso
      (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)).inv.app _

/-- The canonical identification p2_* Delta_* O with O.
Source: Stacks 01KJ, identity of the second projection on the diagonal
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def diagonalProjection {Z S : Scheme.{u}} (a : Z ⟶ S) :
    (Scheme.Modules.pushforward (pullback.snd a a)).obj (diagonalModule a) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.pushforwardComp (pullback.diagonal a) (pullback.snd a a)).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (pullback.diagonal_snd a)).app _ ≪≫
    (Scheme.Modules.pushforwardId Z).app _

/-- The actual counit on a(O), in the common ambient derived category.
Source: Stacks 0A9E
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def counit {Z S : Scheme.{u}} {a : Z ⟶ S}
    (D : NodalRelativeDualizingAdjunction.{u, u} a) :
    (schemeDerivedDirectImage a).obj D.complex ⟶
      single (SheafOfModules.unit S.ringCatSheaf) :=
  (D.adjunction.counit.app ⟨single (SheafOfModules.unit S.ringCatSheaf),
    D.unit_quasicoherent⟩).hom

/-- The smooth dualizing identification normalized by the diagonal graph class.
The exchange equation uses the canonical derived base-change map and the actual
counits. Thus the normalization applies simultaneously to adjunction and differential
coordinates, fixing their relative scalar.
Source: Stacks 0BRT, 0E2E, 0B6J
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure TraceNormalization {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (d : ℕ) where
  duality : NodalRelativeDualizingAdjunction.{u, u} f
  smooth : duality.complex ≅ shiftedOmega f d
  projectionDuality : NodalRelativeDualizingAdjunction.{u, u} (pullback.snd f f)
  projectionSmooth : projectionDuality.complex ≅ shiftedOmega (pullback.snd f f) d
  differential : DifferentialIso f (pullback.snd f f) (pullback.fst f f) d
  exchange :
    schemeDerivedBaseChangeMap f (pullback.snd f f) f (pullback.fst f f)
        pullback.condition duality.complex ≫
      (schemeDerivedDirectImage (pullback.snd f f)).map
        ((derivedPullback (pullback.fst f f)).map smooth.hom ≫
          derivedOmegaMap f (pullback.snd f f) (pullback.fst f f) d differential ≫
          projectionSmooth.inv) ≫ counit projectionDuality =
    (derivedPullback f).map (counit duality) ≫ (zariskiTracePullbackUnitIso f).hom
  diagonal_quasicoherent : schemeDerivedQCohProperty (pullback f f)
    (single (diagonalModule f))
  projectionIso : (schemeDerivedDirectImage (pullback.snd f f)).obj
    (single (diagonalModule f)) ≅ single (SheafOfModules.unit Y.ringCatSheaf)
  projection_normal : directImageUnit (pullback.snd f f) (diagonalModule f) ≫
    projectionIso.hom = (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings
        Y.toRingedSpace)) 0).map
      (diagonalProjection f).hom
  diagonal_normal : IsNormalizedDiagonal f d
    (((projectionDuality.adjunction.homEquiv
      ⟨single (diagonalModule f), diagonal_quasicoherent⟩
      ⟨single (SheafOfModules.unit Y.ringCatSheaf),
        projectionDuality.unit_quasicoherent⟩)
      (ObjectProperty.homMk projectionIso.hom)).hom ≫ projectionSmooth.hom)

/-- A scalar acting on the affine structure module, and hence on its degree-zero complex.
Source: Stacks 01I1, 0FVV
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def scalarEnd {k : Type u} [Field k] (r : k) :
    single (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) ⟶
      single (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace))
      0).map
    (Scheme.Modules.homOfGlobalSection _ ((Scheme.ΓSpecIso (.of k)).inv r))

/-- The degree-zero counit equation, using the canonical module-cohomology/Ext comparison.
Testing on every class is precisely equality of maps on H^0 RΓ(omega[d]).
Source: Stacks 0FVV, 0FVW
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def IsCounitTrace {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (d : ℕ) (N : TraceNormalization f d)
    (t : cohomology f (omega f d) d →ₗ[k] k) : Prop :=
  ∀ x : cohomology f (omega f d) d,
    ((canonicalPullbackAdjunction f).homEquiv _ _
      (zariskiTracePullbackUnitIso f).hom) ≫
      (schemeDerivedDirectImage f).map
        ((Scheme.Modules.moduleExtEquiv (omega f d) d x).hom ≫ N.smooth.inv) ≫
      counit N.duality = scalarEnd (t x)

end Derived


/-- A presentation of the specified fibre product. Allowing every cartesian presentation
includes the original family, the chosen fibre product, and iterated scalar extensions.
Source: Stacks 01JO
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure ScalarChange {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (A : Type u) [CommRing A] [Algebra k A] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of A)
  projection : scheme ⟶ Y
  cartesian : IsPullback projection structureMap f
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The pullback bundle, without a new carrier or a chosen trivialization.
Source: Stacks 01CA
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
abbrev ScalarChange.bundle {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)} (B : ScalarChange f A) (E : Y.Modules) :=
  (Scheme.Modules.tensorPullback B.projection).obj E

/-- The canonical scalar-extension comparison, fixed on every pure tensor.
Existence of a bijective map with this formula states the isomorphism, not just
an abstract equivalence of the two groups.
Source: Stacks 0AAB, 02KH
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def HasBaseChange {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (B : ScalarChange f A)
    (F : Y.Modules) : Prop :=
  ∀ j : ℕ, ∃ beta : A ⊗[k] cohomology f F j →ₗ[A]
      cohomology B.structureMap (B.bundle F) j,
    Function.Bijective beta ∧ ∀ (a : A) (x : cohomology f F j),
      beta (a ⊗ₜ[k] x) = a •
        pull f B.structureMap B.projection F (B.bundle F) (𝟙 _) j x

/-- The coefficient comparison on a composite scalar extension.
Source: Stacks 01CA, normalized tensor-adjunction composition
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def compositeCoefficient {k A B : Type u} [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)}
    (C : ScalarChange f A) (D : ScalarChange f B) (g : D.scheme ⟶ C.scheme)
    (hg : g ≫ C.projection = D.projection) (F : Y.Modules) :
    (Scheme.Modules.tensorPullback g).obj (C.bundle F) ⟶ D.bundle F :=
  (Scheme.Modules.tensorPullbackSectionComp g C.projection).inv.app F ≫
    eqToHom (congrArg (fun q ↦ (Scheme.Modules.tensorPullback q).obj F) hg)

/-- Composite of coefficient isomorphisms in the contravariant pullback order.
Source: Stacks 01CA, 0D5S
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
def composeIso {Z W V : Scheme.{u}} (g : W ⟶ Z) (h : V ⟶ W)
    {F : Z.Modules} {G : W.Modules} {H : V.Modules}
    (eta : (Scheme.Modules.tensorPullback g).obj F ≅ G)
    (theta : (Scheme.Modules.tensorPullback h).obj G ≅ H) :
    (Scheme.Modules.tensorPullback (h ≫ g)).obj F ≅ H :=
  (Scheme.Modules.tensorPullbackSectionComp h g).app F ≪≫
    (Scheme.Modules.tensorPullback h).mapIso eta ≪≫ theta

/-- All scalar and geometric naturality data for the one normalized trace.
The maps are pinned by universal differentials, evaluation and pure tensors.
Source: Stacks 0B6J, 0AAB, 0FW0
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure TraceSystem {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (d : ℕ)
    (t : cohomology f (omega f d) d →ₗ[k] k) where
  differential : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A),
    DifferentialIso f B.structureMap B.projection d
  trace : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A),
    cohomology B.structureMap (omega B.structureMap d) d →ₗ[A] A
  trace_scalar : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
      (a : A) (x : cohomology f (omega f d) d),
    trace A B (a • pull f B.structureMap B.projection (omega f d)
      (omega B.structureMap d) (differential A B).top.hom d x) = a * algebraMap k A (t x)
  automorphism : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
    (h : B.scheme ≅ B.scheme), h.hom ≫ B.structureMap = B.structureMap →
      DifferentialIso B.structureMap B.structureMap h.hom d
  trace_invariant : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
      (h : B.scheme ≅ B.scheme) (hh : h.hom ≫ B.structureMap = B.structureMap)
      (z : cohomology B.structureMap (omega B.structureMap d) d),
    trace A B (pull B.structureMap B.structureMap h.hom (omega B.structureMap d)
      (omega B.structureMap d) (automorphism A B h hh).top.hom d z) = trace A B z

  scalar_differential : ∀ (A B : Type u) [CommRing A] [Algebra k A]
      [CommRing B] [Algebra k B] (phi : A →ₐ[k] B)
      (C : ScalarChange f A) (D : ScalarChange f B) (g : D.scheme ⟶ C.scheme)
      (_hg : g ≫ C.projection = D.projection)
      (_ha : g ≫ C.structureMap = D.structureMap ≫
        Spec.map (CommRingCat.ofHom phi.toRingHom)),
    DifferentialIso C.structureMap D.structureMap g d
  scalar_trace : ∀ (A B : Type u) [CommRing A] [Algebra k A]
      [CommRing B] [Algebra k B] (phi : A →ₐ[k] B)
      (C : ScalarChange f A) (D : ScalarChange f B) (g : D.scheme ⟶ C.scheme)
      (hg : g ≫ C.projection = D.projection)
      (ha : g ≫ C.structureMap = D.structureMap ≫
        Spec.map (CommRingCat.ofHom phi.toRingHom))
      (z : cohomology C.structureMap (omega C.structureMap d) d),
    trace B D (pull C.structureMap D.structureMap g (omega C.structureMap d)
      (omega D.structureMap d) (scalar_differential A B phi C D g hg ha).top.hom d z) =
      phi (trace A C z)
  automorphism_composition : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (B : ScalarChange f A) (h g : B.scheme ≅ B.scheme)
      (hh : h.hom ≫ B.structureMap = B.structureMap)
      (hg : g.hom ≫ B.structureMap = B.structureMap)
      (hc : (h.trans g).hom ≫ B.structureMap = B.structureMap),
    (automorphism A B (h.trans g) hc).top = composeIso g.hom h.hom
      (automorphism A B g hg).top (automorphism A B h hh).top

/-- Bundle pairing compatibility, retaining both dual transposes and the dual of eta inverse.
Source: Stacks 0FVY, 0FW0, 0B6J
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing). -/
structure BundleCompatibility {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (d : ℕ)
    (t : cohomology f (omega f d) d →ₗ[k] k) (S : TraceSystem f d t) (E : Y.Modules) where
  perfect : ∀ (i j : ℕ) (h : i + j = d), IsPerfect f d t E i j h
  base_change : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A),
    HasBaseChange f B E ∧ HasBaseChange f B (dualCoefficient f d E) ∧
      HasBaseChange f B (omega f d)
  dual : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A),
    DualIso f B.structureMap B.projection d E (B.bundle E) (Iso.refl _)
      (S.differential A B)
  pairing_scalar : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
      (i j : ℕ) (h : i + j = d) (a b : A)
      (x : cohomology f E i) (y : cohomology f (dualCoefficient f d E) j),
    pairing B.structureMap d (B.bundle E) (S.trace A B) i j h
      (a • pull f B.structureMap B.projection E (B.bundle E) (𝟙 _) i x)
      (b • pull f B.structureMap B.projection (dualCoefficient f d E)
        (dualCoefficient B.structureMap d (B.bundle E)) (dual A B).coefficient.hom j y) =
      (a * b) * algebraMap k A (pairing f d E t i j h x y)
  automorphism_dual : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
      (h : B.scheme ≅ B.scheme) (hh : h.hom ≫ B.structureMap = B.structureMap)
      (eta : (Scheme.Modules.tensorPullback h.hom).obj (B.bundle E) ≅ B.bundle E),
    DualIso B.structureMap B.structureMap h.hom d (B.bundle E) (B.bundle E) eta
      (S.automorphism A B h hh)
  pairing_invariant : ∀ (A : Type u) [CommRing A] [Algebra k A] (B : ScalarChange f A)
      (h : B.scheme ≅ B.scheme) (hh : h.hom ≫ B.structureMap = B.structureMap)
      (eta : (Scheme.Modules.tensorPullback h.hom).obj (B.bundle E) ≅ B.bundle E)
      (i j : ℕ) (hij : i + j = d) (x : cohomology B.structureMap (B.bundle E) i)
      (y : cohomology B.structureMap (dualCoefficient B.structureMap d (B.bundle E)) j),
    pairing B.structureMap d (B.bundle E) (S.trace A B) i j hij
      (pull B.structureMap B.structureMap h.hom (B.bundle E) (B.bundle E) eta.hom i x)
      (pull B.structureMap B.structureMap h.hom
        (dualCoefficient B.structureMap d (B.bundle E))
        (dualCoefficient B.structureMap d (B.bundle E))
        (automorphism_dual A B h hh eta).coefficient.hom j y) =
      pairing B.structureMap d (B.bundle E) (S.trace A B) i j hij x y
  scalar_composition : ∀ (A B : Type u) [CommRing A] [Algebra k A]
      [CommRing B] [Algebra k B] (phi : A →ₐ[k] B)
      (C : ScalarChange f A) (D : ScalarChange f B) (g : D.scheme ⟶ C.scheme)
      (hg : g ≫ C.projection = D.projection)
      (_ha : g ≫ C.structureMap = D.structureMap ≫ Spec.map (CommRingCat.ofHom phi.toRingHom))
      (F : Y.Modules) (_hF : F = E ∨ F = dualCoefficient f d E ∨ F = omega f d)
      (j : ℕ) (a : A) (x : cohomology f F j),
    pull C.structureMap D.structureMap g (C.bundle F) (D.bundle F)
        (compositeCoefficient C D g hg F) j
        (a • pull f C.structureMap C.projection F (C.bundle F) (𝟙 _) j x) =
      phi a • pull f D.structureMap D.projection F (D.bundle F) (𝟙 _) j x

  dual_composition : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (B : ScalarChange f A) (h g : B.scheme ≅ B.scheme)
      (hh : h.hom ≫ B.structureMap = B.structureMap)
      (hg : g.hom ≫ B.structureMap = B.structureMap)
      (hc : (h.trans g).hom ≫ B.structureMap = B.structureMap)
      (eta : (Scheme.Modules.tensorPullback g.hom).obj (B.bundle E) ≅ B.bundle E)
      (theta : (Scheme.Modules.tensorPullback h.hom).obj (B.bundle E) ≅ B.bundle E),
    (automorphism_dual A B (h.trans g) hc (composeIso g.hom h.hom eta theta)).coefficient =
      composeIso g.hom h.hom (automorphism_dual A B g hg eta).coefficient
        (automorphism_dual A B h hh theta).coefficient
  cohomology_composition : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (B : ScalarChange f A) (h g : B.scheme ≅ B.scheme)
      (_hh : h.hom ≫ B.structureMap = B.structureMap)
      (_hg : g.hom ≫ B.structureMap = B.structureMap) (F : B.scheme.Modules)
      (_hF : F = B.bundle E ∨ F = dualCoefficient B.structureMap d (B.bundle E) ∨
        F = omega B.structureMap d)
      (eta : (Scheme.Modules.tensorPullback g.hom).obj F ≅ F)
      (theta : (Scheme.Modules.tensorPullback h.hom).obj F ≅ F)
      (j : ℕ) (z : cohomology B.structureMap F j),
    pull B.structureMap B.structureMap (h.trans g).hom F F
      (composeIso g.hom h.hom eta theta).hom j z =
      pull B.structureMap B.structureMap h.hom F F theta.hom j
        (pull B.structureMap B.structureMap g.hom F F eta.hom j z)

/-- Smooth proper coherent trace pairings, with their actual counit normalization,
all commutative algebra scalar extensions, and geometric naturality.
Source: Stacks duality.tex, Tags 0FVV, 0FVW, 0FVY, 0FW0, 0B6J and 0AAB
(blueprint: lem-sfb-smooth-proper-coherent-trace-pairing).

Proof, following all twelve steps of the DAG:
1. Put $K_f=f^!k$ and write $\tau_f:R\Gamma K_f\to k[0]$ for the counit. Also use $K_p=p^!\mathcal
O_S$ and $\tau_p$ for $p=f_A:Y_A\to\operatorname{Spec}A$, for any commutative $k$-algebra $A$, as
well as for $p=f$. Smoothness supplies local finite presentation; properness supplies quasi-
compactness and separatedness, so $p$ is of finite presentation. Apply [lem-sfb-proper-flat-
dualizing-polynomial-model] to obtain $K_p$ with its normalized polynomial-chart models and
adjunction trace. Flatness for $f$ follows from [lem-pc-flat-field]; after base change it follows
by tensoring the same flat algebra charts. The trace-pair characterization, uniqueness and
arbitrary-base-change compatibility are those of [lem-sfb-proper-flat-space-derived-duality],
including its explicit agreement with Zariski proper duality when the spaces are schemes and the
base affine. Thus no Noetherian hypothesis on an eventual $A$ is introduced. Uses: def-sbc-smooth-
morphisms, def-weil-proper-morphism, lem-pc-flat-field, lem-sfb-proper-flat-dualizing-polynomial-
model, lem-sfb-proper-flat-space-derived-duality.

2. Normalize $K_p$ by the differential line. Take the standard-smooth affine charts of [lem-sc-
standard-smooth-local-relative-dimension], of dimension $n-c=d$. Their closed immersions into
polynomial affine space are immersions between smooth $S$-schemes. Apply [lem-pur-smooth-pair-
regular-immersion] locally, and [lem-weil-pbc-regular-sequence-koszul-regular] to their regular
equations. The conormal description of [lem-trf-lci-cotangent-presentation] then gives $[C\to
V]\simeq L_{Z/S}$, with $V$ of rank $n$. Since $p$ is smooth this complex is $\Omega^1_{Z/S}[0]$;
its differential cokernel is locally free of rank $d$ by [lem-sc-smooth-omega-finite-locally-
free], so locally this conormal sequence splits. It follows that $C$ has rank $n-d=c$. On these
charts [lem-trf-lci-koszul-duality-determinant-comparison] identifies the normalized polynomial
model of step 1 with $(\det C)^\vee\otimes\det V[d]$. The equality of ranks concerns these local
charts, not a chosen global presentation. Uses: lem-sc-standard-smooth-local-relative-dimension,
lem-pur-smooth-pair-regular-immersion, lem-weil-pbc-regular-sequence-koszul-regular, lem-trf-lci-
cotangent-presentation, lem-trf-lci-koszul-duality-determinant-comparison, lem-sc-smooth-omega-
finite-locally-free.

3. By [lem-trf-lci-determinant-descent-smooth], the relation-first determinant map $(\det
C)^\vee\otimes\det V\to\bigwedge^d\Omega^1_{Z/S}$ agrees with the intrinsic determinant and with
its overlap maps. The polynomial comparisons in [lem-trf-lci-koszul-duality-determinant-
comparison] use precisely these maps, including contraction of an extra relation $t-a$ with
$d(t-a)$ to $1$. These local calculations imply that $K_p$ has cohomology only in degree $-d$. By
[lem-sf-derived-concentrated-single] it is that cohomology sheaf shifted by $d$; the determinant
maps identify this sheaf globally. Thus they give a specified $\kappa_p:K_p\simeq\omega_{Z/S}[d]$.
Its isomorphism naturality can be checked using transported presentations: a family isomorphism
takes the conormal map $[C\to V]$ to the transported map, hence on its cokernel it takes $db$ to
$d(h^\sharp b)$. The induced map of determinant lines is exactly $\bigwedge^d dh$. Changing the
chosen presentations changes neither map, by the cited refinement comparison. This identifies the
action on the actual differential sheaf, rather than an arbitrary identification with a line.
Uses: lem-trf-lci-determinant-descent-smooth, lem-trf-lci-koszul-duality-determinant-comparison,
lem-sf-derived-concentrated-single.

4. Set $t_Y=H^0(\tau_f\circ R\Gamma(\kappa_f^{-1}))$, using
$H^0R\Gamma(\omega_Y[d])=H^d(Y,\omega_Y)$. The rank-$d$ statement [lem-sc-smooth-omega-finite-
locally-free] makes $\omega_Y$ a line (in a local basis its generator is the wedge of the $d$
basis vectors). In a local frame $\mathcal E\simeq\mathcal O^r$, the dual has the dual frame, and
$\mathcal E^\vee\otimes\omega_Y$ is finite free of rank $r$. These sheaves are quasi-coherent and
finitely presented by their local free presentations; $\mathcal E[0]$ is perfect by [def-pc-
perfect-complex]. Apply [lem-fin-proper-coherent-finite-dimensional] to each of $\mathcal E$,
$\mathcal E^\vee\otimes\omega_Y$, and $\omega_Y$. This proves the required finiteness without
connectedness or an algebraic-closure hypothesis. Uses: lem-sc-smooth-omega-finite-locally-free,
pqf-def-coherent, def-pc-perfect-complex, lem-fin-proper-coherent-finite-dimensional.

5. For any complex $C$ of $k$-vector spaces,
$\operatorname{Hom}_{D(k)}(C[i],k[0])\cong\operatorname{Hom}_k(H^iC,k)$. Indeed $k$ is injective:
extend a functional from a subspace by choosing a basis complement and setting it to zero there.
Apply [new-stage3-derived-homology-injective-bijective] to $C[i]$; it says that this particular
comparison is the map induced by cohomology, hence sends a derived morphism to its action on
$H^0$. Apply it with $C=R\Gamma\mathcal E$. The adjunction characterization in [lem-sfb-proper-
flat-space-derived-duality], with the object $\mathcal E[i]$, identifies
$\operatorname{Hom}_Y(\mathcal E[i],K_f)$ with this vector-space dual. The map sends $a:\mathcal
E[i]\to K_f$ to $\tau_f\circ R\Gamma a$, not to an unspecified linear equivalence. Uses: new-
stage3-derived-homology-injective-bijective, lem-sfb-proper-flat-space-derived-duality.

6. Use [lem-pc-perfect-rhom-tensor-comparison] for $\mathcal E[0]$ and $K_f=\omega_Y[d]$, and
[lem-sfb-ringed-global-hom-cup-comparison] to identify the left side of step 5 with
$H^{d-i}(Y,\mathcal E^\vee\otimes\omega_Y)$. The latter node also identifies the action of
$R\Gamma a$ with cup followed by evaluation; [def-sc-module-cohomology-cup-product] identifies
this with the stated module cup. Its order is the dual class followed by the $\mathcal E$ class.
Interchanging the two total-complex cocycles multiplies by $(-1)^{i(d-i)}$, since the tensor
symmetry on degrees $i,d-i$ is exactly that sign. Thus the transpose of the ordered pairing
$P(u,v)$ differs, if required by this order convention, from the bijection of step 5 by
multiplication by this unit sign. It is consequently bijective. Both spaces are finite dimensional
by step 4, so the other transpose is also bijective: in bases its matrix is the transpose of an
invertible square matrix. This proves perfectness for the pairing with the order and evaluation in
the statement. Uses: lem-pc-perfect-rhom-tensor-comparison, lem-sfb-ringed-global-hom-cup-
comparison, def-sc-module-cohomology-cup-product.

7. Let $A$ be any commutative $k$-algebra. It is a flat $k$-module (choose a $k$-basis), so [lem-
sc-flat-base-change-coherent] applies, for every $j\geq0$, to the three quasi-coherent sheaves in
step 4. Since $Y$ is separated and quasi-compact over $k$, its isomorphism is the specified
canonical comparison of [lem-pc-flat-cohomology-separated], $\beta^j:A\otimes_kH^j(Y,\mathcal
F)\to H^j(Y_A,\mathcal F_A)$, $b\otimes x\mapsto b\,p^*x$, and this map is bijective. By [lem-trf-
relative-differential-sheaf-base-change], the differential map is $b\otimes da\mapsto
b\,d(1\otimes a)$; its top wedge identifies $(\omega_Y)_A$ with $\omega_{Y_A/A}$. Duals and tensor
products of $\mathcal E$ commute with this pullback: in a frame the dual basis is carried to the
dual basis and evaluation remains $\sum e_j\lambda_j$. Hence the three sheaves used in base change
are precisely the sheaves occurring over $A$. Uses: lem-sc-flat-base-change-coherent, lem-pc-flat-
cohomology-separated, lem-trf-relative-differential-sheaf-base-change.

8. The arbitrary-base-change trace-pair identification $\beta:Lp^*K_f\simeq K_{f_A}$ of [lem-sfb-
proper-flat-space-derived-duality] identifies $K_{f_A}$ and its counit with the pullback pair of
$K_f$. To compare $\beta$ with the differential normalization, use the pulled-back charts of step
2: $B_A=B\otimes_kA$ with $P_A=P\otimes_kA$. Their relative dimensions remain $n-c=d$ by [lem-
weil-pbc-standard-smooth-base-change]. By [lem-sfb-proper-flat-polynomial-model-base-change],
under the polynomial-chart comparisons on both sides, $\beta|_{U_A}$ is the coinduction base-
change map $R\operatorname{Hom}_P(B,\Omega^n_{P/k})[n]\otimes_BB_A\to
R\operatorname{Hom}_{P_A}(B_A,\Omega^n_{P_A/A})[n]$. That node imposes no Noetherian hypothesis on
$A$. The cotangent comparisons of [lem-trf-lci-cotangent-presentation] commute with this flat,
hence Tor-independent, base change. The dual Koszul comparison of [lem-trf-lci-koszul-duality-
determinant-comparison] for the pulled-back equations is obtained by the same contractions after
tensoring. The base change is flat, so the free Koszul resolutions remain resolutions, and a
contraction of the ordered top relation with its dual is $1$ before and after tensoring. Hence on
$H^{-d}$ the map $\kappa_{f_A}\circ\beta\circ p^*\kappa_f^{-1}$ is the determinant of the conormal
and differential base-change maps, that is, the top wedge of the differential base-change map of
step 7. Taking $H^0R\Gamma$ of the trace-pair equality, with the comparison $\beta^d$ of step 7,
proves $t_{Y_A}=1_A\otimes t_Y$. This uses flatness over $k$, not Noetherianity of $A$. Uses: lem-
sfb-proper-flat-space-derived-duality, lem-weil-pbc-standard-smooth-base-change, lem-sfb-proper-
flat-polynomial-model-base-change, lem-trf-lci-cotangent-presentation, lem-trf-lci-koszul-duality-
determinant-comparison.

9. Apply [lem-sfb-ringed-space-derived-cup-base-change] to the square $Y_A\to Y$ over
$\operatorname{Spec}A\to\operatorname{Spec}k$, with the two vector-bundle complexes and their
evaluation coefficient map. Together with [def-sc-module-cohomology-cup-product] and step 7, its
equality says on pure tensors that the cup-evaluation class of $a\otimes u,b\otimes v$ is
$ab\otimes\operatorname{ev}_*(u\cup v)$. After step 8 its trace is
$ab\,t_Y(\operatorname{ev}_*(u\cup v))$. Pure tensors generate both scalar extensions, so the
pairing over $A$ is exactly $A\otimes_kP$. Uses: lem-sfb-ringed-space-derived-cup-base-change,
def-sc-module-cohomology-cup-product.

10. Let $h:Y_A\to Y_A$ be an $A$-isomorphism. Pull the dualizing trace pair back by $h$. For each
derived quasi-coherent $M$, its represented Hom functor is unchanged: $\operatorname{Hom}(M,h^*K)\
cong\operatorname{Hom}((h^{-1})^*M,K)\cong\operatorname{Hom}_A(R\Gamma((h^{-
1})^*M),A)\cong\operatorname{Hom}_A(R\Gamma M,A)$. The last isomorphism is the canonical
identification of global sections under an isomorphism, with inverse the one induced by $h^{-1}$.
Thus uniqueness of the trace pair in [lem-sfb-proper-flat-space-derived-duality] supplies its
trace-preserving comparison. This is the intrinsic comparison on the polynomial models of [lem-
sfb-proper-flat-dualizing-polynomial-model]. Step 3 computes it, using transported charts, as
$\bigwedge^d dh$ on $\omega$. Consequently its degree-zero counit equation is
$t_{Y_A}(h^*z)=t_{Y_A}(z)$. This argument is over $A$ itself and allows $h$ which does not descend
to $k$. Uses: lem-sfb-proper-flat-space-derived-duality, lem-sfb-proper-flat-dualizing-polynomial-
model, lem-trf-lci-koszul-duality-determinant-comparison, lem-trf-lci-determinant-descent-smooth.

11. Apply [lem-sfb-ringed-space-derived-cup-base-change] with
$g=\mathrm{id}_{\operatorname{Spec}A}$, $g'=h$, $f=f_A=f'$, and the coefficient maps induced by
$\eta$ and its specified dual. This is a commutative square, which need not be presented as a
Cartesian square. On local sections $e,\lambda,w$ the coefficient identity is
$$((\eta^{-1})^*\lambda)(\eta e)\,dh(w)=\lambda(e)\,dh(w).$$ Hence cup-evaluation of the
transformed classes is $h^*$ of the original evaluated class. Step 10 removes this pullback after
applying the trace. This proves the displayed invariance of $P$ with the dual of $\eta^{-1}$,
including its inverse in exactly the required position. Uses: lem-sfb-ringed-space-derived-cup-
base-change.

12. Composition requires no new choices: trace-pair comparisons compose because both composites
induce the same functional on every test object, so uniqueness in [lem-sfb-proper-flat-space-
derived-duality] identifies them. The intrinsic cotangent comparisons in [lem-trf-lci-cotangent-
presentation] respect compositions, and their determinant maps do too by the cocycle of [lem-trf-
lci-determinant-descent-smooth]. At the cochain level the base-change map sends $a\otimes s$ to
$a\,s_A$; for $A\to B$ its composite sends $b\otimes(a\otimes s)$ to $ba\,s_B$, the direct map.
Thus steps 7--11 respect composition of scalar extensions and isomorphisms. If $d=0$ the exterior
power is the empty wedge $\mathcal O$, with the same normalized contractions and all signs equal
to $1$. Empty schemes or rank-zero bundles give zero cohomology spaces and the unique maps; their
zero pairings induce the unique isomorphisms $0\simeq0$. The proof applies componentwise with no
connectedness assumption. Uses: lem-sfb-proper-flat-space-derived-duality, lem-trf-lci-cotangent-
presentation, lem-trf-lci-determinant-descent-smooth.
-/
theorem exists_smoothProperCoherentTracePairing {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsProper f] :
    ∃ (N : TraceNormalization f d) (t : cohomology f (omega f d) d →ₗ[k] k)
      (S : TraceSystem f d t),
      IsCounitTrace f d N t ∧ FiniteDimensional k (cohomology f (omega f d) d) ∧
      ∀ E : Y.Modules, E.IsFiniteLocallyFree → Nonempty (BundleCompatibility f d t S E) := by
  sorry

end AlgebraicGeometry.SmoothProperCoherentTrace
