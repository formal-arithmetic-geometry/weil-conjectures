/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import Sheaf.Paper.PurityFiniteKummerLevel
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-! # Finite Kummer coefficients and scalar-forgetting normalization

Source: blueprint sec-six-functors-basics/sk-prop-a1-kummer,
prop-pur-gm-relative-kummer.proof.md, opening paragraph and Step 3; Stacks Tags
03PL, 03FD, 072W and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Cache the existing coefficient forgetful functor's finite-colimit structure at
its explicit carrier universe. Source: Stacks 03FD, exact coefficient forgetting
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
instance relativeScalarForgetFiniteColimits (P : PurityFiniteSetting.{u}) :
    PreservesFiniteColimits
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) where
  preservesFiniteColimits J _ _ :=
    ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0} (R := P.Coefficient) (J := J)

/-- The positive prime-power exponent is nonzero, as required by the existing canonical
root trivialization. Source: blueprint relative Kummer proof, opening paragraph
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
instance relativeExponentNeZero (P : PurityFiniteSetting.{u}) : NeZero P.exponent :=
  ⟨pow_ne_zero P.kummerLevel (Fact.out : P.coefficients.l.Prime).ne_zero⟩

/-- The existing root-normalized inverse-image comparison at the Kummer exponent.
Source: blueprint relative Kummer proof, opening paragraph; Stacks 03PK
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeTwistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (a : T ⟶ Spec (.of P.field.k)) :
    (upperStar (ModuleCat.{u + 1, u + 1} P.Coefficient) v).obj (P.twistEtale h T) ≅
      P.twistEtale h T' :=
  (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.kummerLevel)
    (P.exponent_coefficient_eq_zero h)).c v (P.exponent_isUnit T a)
      (P.exponent_isUnit T' (v ≫ a)) 1

/-- The sectionwise coefficient comparison, fixed by evaluation at the final object.
Source: Stacks 03FD (blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeGlobalSectionsForgetIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1, u + 1} P.Coefficient) ⋙
        forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient) AddCommGrpCat.{u + 1} ≅
      P.forgetEtale T ⋙ Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology
        (ModuleCat.{u + 1, u + 1} P.Coefficient) (terminalIsTerminal (C := T.Etale)))
      (forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (P.forgetEtale T)
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}
        (terminalIsTerminal (C := T.Etale))).symm

/-- The canonical resolution-induced global comparison, obtained by right-derived
unit descent of the preceding evaluation comparison. Source: Stacks 03FD and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeDerivedGlobalForget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (Sheaf.Γ T.smallEtaleTopology
      (ModuleCat.{u + 1, u + 1} P.Coefficient)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient)
          AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ⟶
      (P.forgetEtale T).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
    (G := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1, u + 1} P.Coefficient))
    (G' := Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (β := P.forgetEtale T)
    (γ := forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
    (P.relativeGlobalSectionsForgetIso T).hom

/-- The actual all-integer cohomology comparison, rather than a choice of an
unconstrained isomorphism. Source: Stacks 03FD
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeGlobalForgetMap (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1, u + 1} P.Coefficient))) :
    (forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1, u + 1} P.Coefficient) q).obj
        ((Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1, u + 1} P.Coefficient)).rightDerivedFunctorPlus.obj K)) ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
          ((P.forgetEtale T).mapDerivedCategoryPlus.obj K)) :=
  ((forget₂ (ModuleCat.{u + 1, u + 1} P.Coefficient)
    AddCommGrpCat.{u + 1}).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
      ((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1, u + 1} P.Coefficient)).rightDerivedFunctorPlus.obj K) ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).map
      ((P.relativeDerivedGlobalForget T).app K)

/-- The canonical all-integer higher-direct-image comparison, formed from the
unit-compatible direct-image comparison and exact-functor homology comparisons.
Source: Stacks 072W and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeHigherForgetIso (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}}
    (a : X ⟶ B) (q : ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1, u + 1} P.Coefficient)) :
    (P.forgetEtale B).obj (higherDirectImage P.Coefficient a q F) ≅
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} a).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((P.forgetEtale X).obj F))) :=
  ((P.forgetEtale B).mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((lowerStar (ModuleCat.{u + 1, u + 1} P.Coefficient) a).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) q).mapIso
      ((moduleAbelianDerivedLowerStarIso P.Coefficient a).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
        (lowerStar AddCommGrpCat.{u + 1} a).rightDerivedFunctorPlus.mapIso
          (((P.forgetEtale X).mapDerivedCategoryPlusSingleFunctor 0).app F))


/-- The canonical root inverse-image comparison, normalized by the kernel inclusion.
Source: blueprint relative Kummer proof, opening paragraph; Stacks 03PK
(blueprint: lem-pur-relative-kummer-coefficient-normalization). -/
def relativeRootPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (a : T ⟶ Spec (.of P.field.k)) :
    (upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf P.exponent) ≅
      T'.rootsOfUnitySheaf P.exponent :=
  (Scheme.finiteEtaleTwistPullbackData P.Coefficient P.exponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.kummerLevel)
    (P.exponent_coefficient_eq_zero h)).r v (P.exponent_isUnit T a)

/-- Finite Kummer coefficients, primitive-root trivializations, naturality of the
ordinary Kummer class, and the canonical scalar-forgetting normalization.

Source: blueprint prop-pur-gm-relative-kummer.proof.md, opening paragraph and Step 3;
Stacks 03PL, 00YR, 03DA, 03DB, 03FD, 072W and 0D6J
(blueprint: lem-pur-relative-kummer-coefficient-normalization).

Proof:
1. Use lem-pur-finite-kummer-level: e divides n, N=n/e is positive, ell^N kills A,
and the DVR quotient is a finite free Z/ell^N-algebra. Since ell differs from p,
ell^N is invertible on every k-scheme. Use lem-sc-primitive-root for the roots.
2. Use the unit-valued root description of lem-asd-etale-finite-twist-pullback.
On an etale test V, factor z^r-1 into the distinct factors z-zeta^b. The opens
where all but one factor are invertible cover V, and on each z=zeta^b. Distinct
labels agree only on empty overlaps. This includes nonreduced V. By
lem-pc-sites-sheafification-underlying-sets and def-weil-pbc-constant-sheaf,
the existing root map is the claimed isomorphism.
3. Tensor that isomorphism with A using def-pur-sheaf-tensor-product. The inverse
sends zeta^b tensor a to ba; balancing proves the inverse laws. The canonical
root and tensor pullbacks preserve these generators, so both trivializations
are natural. Take the structure morphism to Spec k for the pullback description.
The underlying coefficient group is A, whose order r^(ef) is an ell-power.
4. Apply lem-amb-kummer-any-base to the ordinary abelian Kummer sequence.
Pullback of units commutes with powers, giving a morphism of Kummer sequences.
Use lem-weil-pbc-pullback-cohomology-long-exact-ladder and naturality of the
horseshoe boundaries (lem-weil-pbc-horseshoe-delta-functor), identified with the
triangle boundaries by lem-sc-p1-right-derived-triangle-connecting. Degree zero
is pullback of units by lem-weil-pbc-cohomology-pullback-degree-zero.
5. The root insertion z to 1 tensor z commutes with the normalized pullbacks on
pure tensors. Apply lem-weil-pbc-cohomology-pullback-functorial to that insertion
and combine with step 4. This gives naturality of the displayed boundary-and-insertion
composite without putting a Z/r-module structure on G_m.
6. Forgetting is exact by lem-weil-pbc-module-sheaves-colimits-forgetful.
The constant and insertion comparisons extend the identity on constant sections
and z to 1 tensor z. Uniqueness of sheafification, via
lem-cbc-module-sheafification-underlying-sets and
lem-pc-sites-sheafification-underlying-sets, fixes their normalization.
7. The global comparison is derived descent of the evaluation comparison.
For a module injective resolution I and an abelian K-injective replacement UI to J,
it is represented by Gamma(I) to Gamma(J). Use
lem-weil-pbc-etale-module-injective-forget-acyclic and
lem-weil-pbc-etale-module-cohomology-forget. For direct images use the
unit-compatible comparison of
lem-weil-pbc-module-abelian-derived-direct-image-comparison; applying cohomology
gives lem-sbc-higher-direct-image-forget-comparison and relativeHigherForgetIso.
Naturality identifies coefficient and resolution maps. The inverse-image unit
comparison of lem-weil-pbc-module-abelian-inverse-image-comparison identifies
cohomology pullbacks. Exact functors commute with cohomology in every integer
degree, including the vanishing negative degrees of degree-zero sheaves.
8. Apply lem-weil-pbc-exchange-forget-coefficients to every cartesian square.
Its equality identifies the actual exchange maps under these same comparisons.
An inverse additive map to an A-linear isomorphism is A-linear, so forgetting
reflects invertibility. Its exactness and the cohomology criterion for derived
isomorphisms give the same reflection for derived maps.
-/
theorem relativeKummerCoefficientNormalization (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    (1 ≤ P.kummerLevel) ∧
    ((P.exponent : P.Coefficient) = 0) ∧
    (∃ α : ZMod P.exponent →+* P.Coefficient, ∃ d : ℕ,
      ∃ b : P.Coefficient ≃+ (Fin d → ZMod P.exponent),
        ∀ (z : ZMod P.exponent) (x : P.Coefficient), b (α z * x) = z • b x) ∧
    (∀ T : Over (Spec (.of P.field.k)), IsUnit (P.exponent : Γ(T.left, ⊤))) ∧
    (∃ d : ℕ, Nat.card P.Coefficient = P.coefficients.l ^ d) ∧
    (∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.exponent),
      ∃ τ : ∀ T : Over (Spec (.of P.field.k)),
        P.constantEtale T.left ≅ P.twistEtale h T.left,
        (∀ (T : Over (Spec (.of P.field.k))) (W : T.left.Etaleᵒᵖ) (b : ℕ),
          ((Additive.toMul
            ((kernel.ι (P.exponent • 𝟙 T.left.gmSheaf)).hom.app W
              ((T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom.hom.app W
                ((toSheafify T.left.smallEtaleTopology
                  ((Functor.const T.left.Etaleᵒᵖ).obj
                    (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent))))).app W
                      (ULift.up (b : ZMod P.exponent))))).down : Γ(W.unop.left, ⊤)ˣ) :
              Γ(W.unop.left, ⊤)) =
            W.unop.hom.appTop (((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ T.hom.appTop) ζ)
              ^ b) ∧
        (∀ (T : Over (Spec (.of P.field.k))) (W : T.left.Etaleᵒᵖ) (a : P.Coefficient),
          (τ T).hom.hom.app W
            ((toSheafify T.left.smallEtaleTopology
              ((Functor.const T.left.Etaleᵒᵖ).obj
                (ModuleCat.of P.Coefficient P.Coefficient))).app W a) =
            Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T.left
              (P.exponent_coefficient_eq_zero h) W a
                ((T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom.hom.app W
                  ((toSheafify T.left.smallEtaleTopology
                    ((Functor.const T.left.Etaleᵒᵖ).obj
                      (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent))))).app W
                        (ULift.up 1)))) ∧
        (∀ (T T' : Over (Spec (.of P.field.k))) (v : T' ⟶ T),
          (upperStar AddCommGrpCat.{u + 1} v.left).map
              (T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ).hom ≫
              (P.relativeRootPullback h v.left T.hom).hom =
            ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v.left).app
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.exponent)))).hom ≫
                (T'.left.constantZModIsoRootsOfUnitySheaf P.exponent T'.hom hζ).hom) ∧
        (∀ (T T' : Over (Spec (.of P.field.k))) (v : T' ⟶ T),
          (upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).map (τ T).hom ≫
              (P.relativeTwistPullback h v.left T.hom).hom =
            ((Scheme.upperStarConstantSheafIso
              (ModuleCat.{u + 1} P.Coefficient) v.left).app
                (ModuleCat.of P.Coefficient P.Coefficient)).hom ≫ (τ T').hom)) ∧
    (∀ (T T' : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k)) (v : T' ⟶ T)
        (w : Γ(T, ⊤)ˣ),
      Sheaf.H.map
        ((moduleAbelianUpperStarComparison P.Coefficient v).app (P.twistEtale h T) ≫
          (P.forgetEtale T').map (P.relativeTwistPullback h v a).hom) 1
        (cohomologyMap v ((P.forgetEtale T).obj (P.twistEtale h T)) 1
          (Sheaf.H.map
            (ordinaryFiniteRootMap P.Coefficient P.exponent
              (P.exponent_coefficient_eq_zero h) T) 1
            (T.kummerδ₀ P.exponent (P.exponent_isUnit T a) (Additive.ofMul w)))) =
        Sheaf.H.map
          (ordinaryFiniteRootMap P.Coefficient P.exponent
            (P.exponent_coefficient_eq_zero h) T') 1
          (T'.kummerδ₀ P.exponent (P.exponent_isUnit T' (v ≫ a))
            (Additive.ofMul (Units.map v.appTop.hom.toMonoidHom w)))) ∧
    (∀ (T : Scheme.{u}) (W : T.Etaleᵒᵖ)
        (z : (T.rootsOfUnitySheaf P.exponent).obj.obj W),
      (ordinaryFiniteRootMap P.Coefficient P.exponent
        (P.exponent_coefficient_eq_zero h) T).hom.app W z =
        Scheme.finiteEtaleTateOneGenerator P.Coefficient P.exponent T
          (P.exponent_coefficient_eq_zero h) W 1 z) ∧
    (∀ (T : Scheme.{u}) (W : T.Etaleᵒᵖ) (a : P.Coefficient),
      ((constantCommuteCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient)).hom.app W
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj
                (ModuleCat.of P.Coefficient P.Coefficient))).app W a) =
        (toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of P.Coefficient))).app W a) ∧
    (∀ T : Scheme.{u}, IsIso (P.relativeDerivedGlobalForget T)) ∧
    (∀ (T : Scheme.{u}) (q : ℤ)
        (K : DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
      IsIso (P.relativeGlobalForgetMap T q K)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
        (K : DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
      (forget₂ (ModuleCat.{u + 1} P.Coefficient)
        AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
          (moduleDerivedCohomologyPullback P.Coefficient v K) ≫
        (P.relativeDerivedGlobalForget T').app
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategoryPlus.obj K) ≫
        (Sheaf.Γ T'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((moduleAbelianDerivedUpperStarIso P.Coefficient v).symm.app K).hom =
      (P.relativeDerivedGlobalForget T).app K ≫
        abelianDerivedCohomologyPullback v ((P.forgetEtale T).mapDerivedCategoryPlus.obj K)) ∧
    (∀ (X B : Scheme.{u}) (a : X ⟶ B),
      IsIso (moduleAbelianDerivedLowerStarComparison P.Coefficient a)) ∧
    (∀ (X X' B B' : Scheme.{u}) (f : X ⟶ B) (f' : X' ⟶ B')
        (g' : X' ⟶ X) (g : B' ⟶ B) (sq : ChosenCartesianSquare g' f' f g)
        (K : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
      ((P.forgetEtale B').mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq).app K) ≫
        (moduleAbelianDerivedExchangeTargetIso P.Coefficient g' f' K).hom =
      (moduleAbelianDerivedExchangeSourceIso P.Coefficient f g K).hom ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((P.forgetEtale X).mapDerivedCategoryPlus.obj K)) ∧
      (IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} P.Coefficient)
          sq.toCommSq).app K) ↔
        IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((P.forgetEtale X).mapDerivedCategoryPlus.obj K)))) ∧
    (∀ (T : Scheme.{u}) (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
        (b : F ⟶ G), IsIso ((P.forgetEtale T).map b) ↔ IsIso b) ∧
    (∀ (T : Scheme.{u})
        (K L : DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (b : K ⟶ L), IsIso ((P.forgetEtale T).mapDerivedCategoryPlus.map b) ↔ IsIso b) := by
  sorry

end WeilConjectures.PurityFiniteSetting
