/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.Paper.ProjectionFormulaArrows
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Exact projection mates for ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56;
Derived Categories, Tag 0A8D (blueprint: lem-weil-pbc-ringed-projection-mate-exact).
-/

@[expose] public section

universe u w

set_option autoImplicit false
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- The module category of a recorded corner; this is a transparent interface abbreviation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateModules (A : RingedTensorCorner.{u, w}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

/-- The existing derived category, with the size chosen in the corner.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateDerived (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory A.mateModules

/-- The degree-zero ring complex, the tensor unit before localization.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnitComplex (A : RingedTensorCorner.{u, w}) :=
  (CochainComplex.singleFunctor A.mateModules 0).obj
    (SheafOfModules.unit ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))

/-- The degree-zero ring in the derived category, rather than an arbitrary unit object.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnit (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory.Q.obj A.mateUnitComplex

/-- The ordinary tensor bifunctor already used by the representative presentation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateTensor (A : RingedTensorCorner.{u, w}) :=
  @MonoidalCategory.curriedTensor A.mateModules _ (monoidalCategory A.ring)

/-- Flat-term K-flat representatives, with the same predicate as `RingedTensorModel`.
Source: Stacks Tags 06YS, 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateFlat (A : RingedTensorCorner.{u, w}) :
    ObjectProperty (CochainComplex A.mateModules ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

/-- On representatives the first shift is unsigned and the second has the Koszul sign.
The equations transport these existing chain isomorphisms through the representative
identification and the canonical shift comparison of the localization functor.
Source: Stacks Tag 06YU, signed total convention
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def RingedTensorModel.MateCanonicalShifts {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) [(Functor.curryObj A.tensor).CommShift₂Int] : Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  (∀ (P : CochainComplex A.mateModules ℤ) (n : ℤ), A.mateFlat P → A.mateFlat (P⟦n⟧)) ∧
  (∀ (P Q : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P) (hQ : A.mateFlat Q)
      (n : ℤ) (hPn : A.mateFlat (P⟦n⟧)),
    a.representative.hom.app (⟨P⟦n⟧, hPn⟩, ⟨Q, hQ⟩) ≫
        A.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P)
          (𝟙 (DerivedCategory.Q.obj Q))) ≫
        (((Functor.curryObj A.tensor).flip.obj (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso P Q A.mateTensor n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q A.mateTensor) ≫
        (shiftFunctor A.mateDerived n).map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))) ∧
  (∀ (P Q : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P) (hQ : A.mateFlat Q)
      (n : ℤ) (hQn : A.mateFlat (Q⟦n⟧)),
    a.representative.hom.app (⟨P, hP⟩, ⟨Q⟦n⟧, hQn⟩) ≫
        A.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
          ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curryObj A.tensor).obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso P Q A.mateTensor n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q A.mateTensor) ≫
        (shiftFunctor A.mateDerived n).map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)))

/-- Canonical right unitors are induced by multiplication on every total-complex summand.
The chain map is specified by its composites with all summand inclusions, so its data
cannot be replaced by an arbitrary isomorphism. This also asserts that the unit is K-flat.
Source: Stacks Tags 06YU, 07A4 (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def RingedTensorModel.MateCanonicalUnit {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) (r : ∀ U : A.mateDerived, A.tensor.obj (U, A.mateUnit) ≅ U) :
    Prop :=
  ∃ hunit : A.mateFlat A.mateUnitComplex,
    ∀ (P : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P),
      ∃ j : CochainComplex.mapBifunctor P A.mateUnitComplex A.mateTensor ≅ P,
        (∀ n : ℤ,
          CochainComplex.ιMapBifunctor P A.mateUnitComplex A.mateTensor n 0 n (add_zero n) ≫
              j.hom.f n =
            (A.mateTensor.obj (P.X n)).map
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  (SheafOfModules.unit ((sheafCompose A.topology
                    (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))).hom ≫
              ((monoidalCategory A.ring).rightUnitor (P.X n)).hom) ∧
        a.representative.hom.app (⟨P, hP⟩, ⟨A.mateUnitComplex, hunit⟩) ≫
          (r (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map j.hom

/-- Exactness, normalized tensor shifts, and the counit projection mate for a ringed topos.
Source: Stacks Tags 06YU, 07A4, 07A6, 0B56 and Derived Categories Tag 0A8D
(blueprint: lem-weil-pbc-ringed-projection-mate-exact).

Proof:
1. Descend total tensor from flat-term K-flat complexes using
`lem-weil-pbc-site-derived-tensor-descent` and `lem-pc-kflat-resolution`. Construct L by
`lem-weil-pbc-ringed-topoi-derived-pullback`; K-injective resolutions and
`lem-pc-right-derived-functor-triangulated` construct R. The module adjunction
`lem-weil-pbc-ringed-topoi-module-adjunction` and `lem-pc-derived-adjoint-functors`
give the derived adjunction.
2. The canonical comparison is `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
On representatives it sends a tensor (x tensor y) to (a tensor x) tensor (1 tensor y),
with inverse multiplying scalars. The first-factor shift has no sign; the second on
first-factor degree p has sign (-1)^(np). These chain maps are coherent for all integers,
natural, and compatible with pullback and multiplication by the unit. Descend them.
3. Tensor with a K-flat complex preserves cone triangles: the cone comparison is identity
on the unshifted summand and (-1)^p on the shifted summand. This commutes with the signed
connecting map. Symmetry proves exactness in the other variable. Compose the exact tensor,
L and R to obtain exactness of F and G.
4. Put beta = mu followed by counit tensor identity. Its adjunct is alpha, the existing
`derivedProjectionFormulaMate`. Shifted K-injective complexes stay K-injective by
`lem-weil-pbc-kinjective-shift`. The derived adjunction shift compatibility is the unique
one of `lem-weil-pbc-adjunction-shift-compatibility-unique`. Write alpha_(P[1]) for evaluation
at the shifted object and (alpha_P)[1] for the shifted morphism. Naturality of the unit and
the shift equation for beta give sG alpha_(P[1]) = (alpha_P)[1] sF, for every integer shift.
Naturality in E follows from naturality of the counit and mu. On distinguished triangles,
the first two squares are naturality and the third is this shift equation followed by
naturality at the connecting map. At the unit beta is the counit; the adjunction triangle
identity gives alpha = identity under the unitors. -/
theorem ringedProjectionMateExact
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) :
    ∃ (_ : (Functor.curryObj Y.tensor).CommShift₂Int)
      (_ : (Functor.curryObj X.tensor).CommShift₂Int)
      (_ : e.left.CommShift ℤ) (_ : e.right.CommShift ℤ),
      a.MateCanonicalShifts ∧ b.MateCanonicalShifts ∧
      NatTrans.CommShift e.epsilon ℤ ∧
      e.left.IsTriangulated ∧ e.right.IsTriangulated ∧ e.derivedAdjunction.CommShift ℤ ∧
      (∀ U : Y.mateDerived, ((Functor.curryObj Y.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj Y.tensor).flip.obj U).IsTriangulated) ∧
      (∀ U : X.mateDerived, ((Functor.curryObj X.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj X.tensor).flip.obj U).IsTriangulated) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U, V⟦n⟧) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U))
              ((e.left.commShiftIso n).hom.app V)) ≫
            (((Functor.curryObj X.tensor).obj (e.left.obj U)).commShiftIso n).hom.app
              (e.left.obj V) =
          e.left.map ((((Functor.curryObj Y.tensor).obj U).commShiftIso n).hom.app V) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U⟦n⟧, V) ≫
            X.tensor.map (Prod.mkHom ((e.left.commShiftIso n).hom.app U)
              (𝟙 (e.left.obj V))) ≫
            (((Functor.curryObj X.tensor).flip.obj (e.left.obj V)).commShiftIso n).hom.app
              (e.left.obj U) =
          e.left.map ((((Functor.curryObj Y.tensor).flip.obj V).commShiftIso n).hom.app U) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      ∃ (unitL : e.left.obj Y.mateUnit ≅ X.mateUnit)
        (unitY : ∀ U : Y.mateDerived, Y.tensor.obj (U, Y.mateUnit) ≅ U)
        (unitX : ∀ U : X.mateDerived, X.tensor.obj (U, X.mateUnit) ≅ U),
        a.MateCanonicalUnit unitY ∧ b.MateCanonicalUnit unitX ∧
        (∀ U : Y.mateDerived,
          (e.tensorComparison a b).hom.app (U, Y.mateUnit) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom) ≫
            (unitX (e.left.obj U)).hom = e.left.map (unitY U).hom) ∧
        ∃ alpha : ∀ E : X.mateDerived,
          (Functor.curryObj Y.tensor).obj (e.right.obj E) ⟶
            e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right,
          (∀ (E : X.mateDerived) (P : Y.mateDerived), (alpha E).app P =
            derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
              (e.tensorComparison a b) E P) ∧
          (∀ E : X.mateDerived,
            (e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right).IsTriangulated ∧
              NatTrans.CommShift (alpha E) ℤ) ∧
          (∀ (E : X.mateDerived) (T : Triangle Y.mateDerived), T ∈ distTriang Y.mateDerived →
            ∃ m : (Functor.mapTriangle
                ((Functor.curryObj Y.tensor).obj (e.right.obj E))).obj T ⟶
                (Functor.mapTriangle
                  (e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right)).obj T,
              m.hom₁ = (alpha E).app T.obj₁ ∧ m.hom₂ = (alpha E).app T.obj₂ ∧
                m.hom₃ = (alpha E).app T.obj₃) ∧
          (∀ (E E' : X.mateDerived) (q : E ⟶ E') (P : Y.mateDerived),
            ((Functor.curryObj Y.tensor).map (e.right.map q)).app P ≫ (alpha E').app P =
              (alpha E).app P ≫
                (Functor.whiskerRight (Functor.whiskerLeft e.left
                  ((Functor.curryObj X.tensor).map q)) e.right).app P) ∧
          (∀ E : X.mateDerived,
            (alpha E).app Y.mateUnit ≫
              e.right.map (X.tensor.map (Prod.mkHom (𝟙 E) unitL.hom) ≫ (unitX E).hom) =
                (unitY (e.right.obj E)).hom) := by
  sorry

end SheafOfModules
