/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates
import Sheaf.CategoryTheory.ExactDerivedComposition
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations

/-! # Unbounded open restriction of condensed-module direct image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, Proof (2)
(blueprint: lem-sfb-derived-open-square-restriction).

The helpers spell out the canonical inverse-image comparison, its open mate, exact
termwise derivation, and the five Hom bijections. All categories are the ordinary
unbounded derived categories of internal modules over the pulled-back condensed ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {W Y Ybar : Scheme.{u}} (r : W ⟶ Ybar) (i : Y ⟶ Ybar) [IsOpenImmersion i]

/-- The pullback-square comparison on internal modules, using the recorded coefficient
composition comparisons; the square is the chosen scheme fibre product.
Source: det-sf-comp-composition-interchange, Proof (2), coefficient coherence in steps 3--4
of the expanded DAG proof (blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquarePullbackComparison :
    upperStar Λ i ⋙ upperStar Λ (pullback.snd r i) ≅
      upperStar Λ r ⋙ upperStar Λ (pullback.fst r i) :=
  (upperStarComp Λ (pullback.snd r i) i).symm ≪≫
    eqToIso (congrArg (upperStar Λ) (pullback.condition (f := r) (g := i)).symm) ≪≫
    upperStarComp Λ (pullback.fst r i) r

/-- Apply an underived open base-change isomorphism termwise and localize, with the
canonical exact-composition identifications on both sides.
Source: det-sf-comp-composition-interchange, Proof (2), step 4 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquareDerivedExtensionIso
    (e : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i)) :
    (openImmersionLowerShriek Λ i).mapDerivedCategory ⋙ (upperStar Λ r).mapDerivedCategory ≅
      (upperStar Λ (pullback.snd r i)).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst r i)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek Λ i) (upperStar Λ r)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Λ (pullback.snd r i))
      (openImmersionLowerShriek Λ (pullback.fst r i))

/-- The five natural Hom bijections defining open restriction of derived direct image.
The middle bijection precomposes with the inverse of the termwise open comparison.
Source: det-sf-comp-composition-interchange, Proof (2), steps 5--6 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenSquareHomEquiv
    (e : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i))
    (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))) :
    (T ⟶ (upperStar Λ i).mapDerivedCategory.obj (((lowerStar Λ r).rightDerivedFunctor).obj B)) ≃
      (T ⟶ ((lowerStar Λ (pullback.snd r i)).rightDerivedFunctor).obj
        ((upperStar Λ (pullback.fst r i)).mapDerivedCategory.obj B)) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _).symm |>.trans
    (((upperStarLowerStarAdjunction Λ r).mapDerivedCategoryRightDerivedAdjunction.homEquiv
      _ _).symm) |>.trans
    (Iso.homCongr ((moduleOpenSquareDerivedExtensionIso Λ r i e).app T) (Iso.refl B)) |>.trans
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r i)).homEquiv
      _ _) |>.trans
    ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ (pullback.snd r i))).homEquiv _ _)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The derived open unit is the localization of the termwise sheaf unit, using the
canonical exact-functor factorizations. The derived adjunction itself is the recorded one.
Source: det-sf-comp-composition-interchange, Proof (2), step 2 of the expanded DAG proof
(blueprint: lem-sfb-derived-open-square-restriction). -/
def moduleOpenUnitIsTermwise
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} (h : U ⟶ X) [IsOpenImmersion h] : Prop :=
  ∀ K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) ℤ,
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ h).unit.app
        (DerivedCategory.Q.obj K) ≫
      (upperStar Λ h).mapDerivedCategory.map
        ((openImmersionLowerShriek Λ h).mapDerivedCategoryFactors.hom.app K) ≫
      (upperStar Λ h).mapDerivedCategoryFactors.hom.app
        (((openImmersionLowerShriek Λ h).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        (((openImmersionLowerShriekUpperStarAdjunction Λ h).mapHomologicalComplex
          (.up ℤ)).unit.app K)

/-- Open restriction commutes with total derived direct image on all unbounded
internal-module complexes, with the specified open units, Hom chain and canonical shifts.
Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, Proof (2)
(blueprint: lem-sfb-derived-open-square-restriction).

Proof plan (the eight steps of the DAG):
1. Cartesian coefficients identify each pulled-back ring with the coefficient ring at the
source. The module pullbacks and open extensions are exact. The module open unit is the
composite of the invertible scalar-change unit and the linearized abelian open unit;
full faithfulness of abelian extension by zero makes the latter invertible.
2. Apply the termwise adjunction on complexes and homotopy categories, then localize at
quasi-isomorphisms. Exact-functor factorization and adjunction localization give the
recorded adjunctions and their actual, termwise-normalized invertible units.
3. Specialize arbitrary-ring open base change to the coefficient ring on Ybar, translating
its operations using extension/restriction along the coefficient isomorphisms.
4. The two coefficient transports to the fibre product coincide: the composition law for
eta and the alpha/eta mate relation identify them for jr = pi. Thus open base change is
module-linear and natural. Its inverse is the open exchange mate. Derive this exact
natural isomorphism termwise, with the canonical exact-composition identifications.
5. Grothendieck abelian sheaves and internal modules provide K-injective resolutions.
Use the canonical adjunctions D(r*) -| Rr* and D(p*) -| Rp*. Compose their Hom bijections
with the two open adjunction bijections and precomposition with inverse open base change.
6. For the resulting natural bijection Phi, define rho_B = Phi(id). Its inverse is
Phi.symm(id). Naturality in the test object proves both inverse identities and the
characterization by postcomposition; naturality in B gives a natural isomorphism.
7. Exact functor shifts are induced termwise, so units, counits, open base change and
exact-composition comparisons commute with shifts.
8. The canonical right-derived adjunction shift theorem applies to r and p. Every factor
of the five-bijection chain therefore commutes with simultaneous shift. Apply this to
the identity defining rho to obtain its shift square. No step imposes properness,
boundedness or constructibility. -/
theorem derived_open_square_restriction
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {W Y Ybar : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom] [IsSeparated Ybar.hom]
    (r : W ⟶ Ybar) (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).unit ∧
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).unit ∧
    moduleOpenUnitIsTermwise Λ i.left ∧
    moduleOpenUnitIsTermwise Λ (pullback.fst r.left i.left) ∧
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left).CommShift ℤ ∧
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
      (pullback.fst r.left i.left)).CommShift ℤ ∧
    (upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ ∧
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ (pullback.snd r.left i.left))).CommShift ℤ ∧
    ∃ e : openImmersionLowerShriek Λ i.left ⋙ upperStar Λ r.left ≅
        upperStar Λ (pullback.snd r.left i.left) ⋙
          openImmersionLowerShriek Λ (pullback.fst r.left i.left),
      e.inv = Adjunction.exchangeLeft
        (openImmersionLowerShriekUpperStarAdjunction Λ i.left)
        (openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left))
        (moduleOpenSquarePullbackComparison Λ r.left i.left) ∧
      NatTrans.CommShift (moduleOpenSquareDerivedExtensionIso Λ r.left i.left e).hom ℤ ∧
      ∃ ρ : (lowerStar Λ r.left).rightDerivedFunctor ⋙ (upperStar Λ i.left).mapDerivedCategory ≅
          (upperStar Λ (pullback.fst r.left i.left)).mapDerivedCategory ⋙
            (lowerStar Λ (pullback.snd r.left i.left)).rightDerivedFunctor,
        (∀ (T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
            (condensedRingObj Λ Y.left)))
          (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
            (condensedRingObj Λ W.left)))
          (a : T ⟶ (upperStar Λ i.left).mapDerivedCategory.obj
            (((lowerStar Λ r.left).rightDerivedFunctor).obj B)),
          a ≫ ρ.hom.app B = moduleOpenSquareHomEquiv Λ r.left i.left e T B a) ∧
        NatTrans.CommShift ρ.hom ℤ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
