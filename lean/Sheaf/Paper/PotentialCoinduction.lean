/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Internal coinduction for a prime-power coefficient quotient

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition 6.2.1.1, second assertion, printed p. 294
(blueprint: lem-per-potential-coinduction).

Coextension is the published right derived functor of sectionwise coextension.
The comparison is the closed transpose of evaluation, followed by the actual
restriction/coextension counit. Its tensor balancing map is fixed on every
cochain representative by the ordinary sectionwise balancing map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

/-- The existing cochain tensor, specialized only after fixing the coefficient category.
Source: Stacks 06YY; ILO XVII, Proposition 6.2.1.1
(blueprint: lem-per-potential-coinduction). -/
def coinductionCochainTensor
    (D : Type a) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u}) (P Q : CochainComplex (Sheaf X.smallEtaleTopology D) ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology D) ℤ := P ⊗ Q

/-- The summand inclusion for the existing cochain tensor.
Source: Stacks 06YY; ILO XVII, Proposition 6.2.1.1
(blueprint: lem-per-potential-coinduction). -/
def coinductionTensorInclusion
    (D : Type a) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u}) (P Q : CochainComplex (Sheaf X.smallEtaleTopology D) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    P.X p ⊗ Q.X q ⟶ (coinductionCochainTensor D X P Q).X n :=
  HomologicalComplex.ιTensorObj P Q p q n h

/-- The published tensor localization map, expressed using derivedTensor before specializing
its coefficient category. This retains exactly the monoidal structure used by derivedHom.
Source: ILO XVII, Proposition 6.2.1.1; Stacks 06YY
(blueprint: lem-per-potential-coinduction). -/
def coinductionTensorRepresentative
    (D : Type a) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u}) (P Q : CochainComplex (Sheaf X.smallEtaleTopology D) ℤ) :
    ((derivedTensor D X).obj (_root_.DerivedCategory.Q.obj P)).obj
        (_root_.DerivedCategory.Q.obj Q) ⟶
        _root_.DerivedCategory.Q.obj (coinductionCochainTensor D X P Q) :=
  Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- The type of the derived balancing transformation for scalar restriction.
Its source is `UM tensor_A UN` and its target is `U(M tensor_B N)`.
Source: ILO XVII, Proposition 6.2.1.1, restriction--coinduction adjunction
(blueprint: lem-per-potential-coinduction). -/
abbrev CoinductionTensorMap (q : A →+* B) (X : Scheme.{u}) :=
  ((Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory.prod
      (Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory ⋙
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) X)) ⟶
  (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) X) ⋙
    (Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory)

/-- Fix the balancing transformation by its ordinary cochain formula. The map `t`
uses the sheaf tensorator `UM tensor_A UN → U(M tensor_B N)` on every summand.
The second equality states that deriving this map gives the specified transformation.
Taking K-flat representatives over B makes the right-hand comparison invertible,
so these equations determine the transformation, without any arbitrary-map choice.
Source: ILO XVII, Proposition 6.2.1.1; Stacks 03EK and 06YY
(blueprint: lem-per-potential-coinduction). -/
def CoinductionTensorNormalized (q : A →+* B) (X : Scheme.{u})
    (μ : CoinductionTensorMap q X) : Prop :=
  let V := Sheaf.restrictScalars X.smallEtaleTopology q
  let U := V.mapDerivedCategory
  let Vc := V.mapHomologicalComplex (.up ℤ)
  ∀ P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ,
    ∃ t : coinductionCochainTensor (ModuleCat.{u + 1} A) X (Vc.obj P) (Vc.obj Q) ⟶
        Vc.obj (coinductionCochainTensor (ModuleCat.{u + 1} B) X P Q),
      (∀ (p q n : ℤ) (h : p + q = n),
        coinductionTensorInclusion (ModuleCat.{u + 1} A) X (Vc.obj P) (Vc.obj Q) p q n h ≫ t.f n =
          Functor.LaxMonoidal.μ V (P.X p) (Q.X q) ≫
            V.map (coinductionTensorInclusion (ModuleCat.{u + 1} B) X P Q p q n h)) ∧
      μ.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) ≫
          U.map (coinductionTensorRepresentative (ModuleCat.{u + 1} B) X P Q) ≫
          V.mapDerivedCategoryFactors.hom.app
            (coinductionCochainTensor (ModuleCat.{u + 1} B) X P Q) =
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
            (V.mapDerivedCategoryFactors.hom.app P)).app
              (U.obj (_root_.DerivedCategory.Q.obj Q)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj
            (_root_.DerivedCategory.Q.obj (Vc.obj P))).map
              (V.mapDerivedCategoryFactors.hom.app Q) ≫
          coinductionTensorRepresentative (ModuleCat.{u + 1} A) X (Vc.obj P) (Vc.obj Q) ≫
          _root_.DerivedCategory.Q.map t

/-- The actual internal comparison from the S-linear Hom into coextension to the
R-linear Hom into K. It is the closed transpose of restricted evaluation followed
by the derived restriction/coextension counit, whose ordinary formula is h ↦ h(1).
Source: ILO XVII, Proposition 6.2.1.1, second assertion
(blueprint: lem-per-potential-coinduction). -/
def coinductionInternalHomMap (q : A →+* B) (X : Scheme.{u})
    (μ : CoinductionTensorMap q X)
    (M : DerivedCategoryModule B X) (K : DerivedCategoryModule A X) :
    (Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory.obj
        (((derivedHom (ModuleCat.{u + 1} B) X).obj (op M)).obj
          ((coextendScalars q X).rightDerivedFunctor.obj K)) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) X).obj
        (op ((Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory.obj M))).obj K :=
  let U := (Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory
  let C := (coextendScalars q X).rightDerivedFunctor
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) (U.obj M)).homEquiv _ _
    (μ.app (M, ((derivedHom (ModuleCat.{u + 1} B) X).obj (op M)).obj (C.obj K)) ≫
      U.map ((derivedTensorHomAdjunction (ModuleCat.{u + 1} B) M).counit.app (C.obj K)) ≫
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology q
        |>.mapDerivedCategoryRightDerivedAdjunction).counit.app K)

/-- The full comparison assertion, with coefficients kept abstract until specialization.
The first clause fixes the balancing map, the second places coextension in D+,
the third identifies its underlying R-object with RHom_R(S,K), and the last
clause gives the evaluation-normalized natural isomorphism in unbounded D(R).
Source: ILO XVII, Proposition 6.2.1.1
(blueprint: lem-per-potential-coinduction). -/
def InternalCoinductionComparison (q : A →+* B) (X : Scheme.{u}) : Prop :=
  let U := (Sheaf.restrictScalars X.smallEtaleTopology q).mapDerivedCategory
  let C := (coextendScalars q X).rightDerivedFunctor
  let PR := _root_.DerivedCategory.Plus.ι
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let PS := _root_.DerivedCategory.Plus.ι
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
  ∃ μ : CoinductionTensorMap q X,
    CoinductionTensorNormalized q X μ ∧
    (∀ K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ n : ℤ, (C.obj K.obj).IsGE n) ∧
    Nonempty (PR ⋙ C ⋙ U ≅ PR ⋙
      (derivedHom (ModuleCat.{u + 1} A) X).obj (op (U.obj (constantComplex B X)))) ∧
    ∃ e :
      (PS.op.prod (PR ⋙ C) ⋙
          Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} B) X) ⋙ U) ≅
        ((PS ⋙ U).op.prod PR ⋙
          Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) X)),
      ∀ (M : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (K : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
        e.hom.app (op M, K) = coinductionInternalHomMap q X μ M.obj K.obj

/-- Internal coinduction along the canonical prime-power quotient, with its
coefficient action, bounded-below coextension, and natural evaluation comparison.
The final isomorphism is a natural isomorphism on `D+(S)^op × D+(R)`, with values
in the unbounded category D(R). Its direction is evaluation; its inverse gives
the displayed isomorphism in the node. No finiteness or potentiality is assumed.

Source: ILO, Travaux de Gabber, XVII, Proposition 6.2.1.1, printed p. 294
(blueprint: lem-per-potential-coinduction).

Proof:
1. Restriction U is exact and does not change underlying abelian sheaves.
   The published coextension C₀ sends F to Hom_R(S,F), with S-action
   (a φ)(b)=φ(ab). The counit is evaluation at 1; its inverse adjunction
   formula sends f to (m ↦ (b ↦ f(bm))). These formulas hold on every localized
   site (def-pur-sheaf-hom, def-pc-sheaf-restrict-scalars).
2. The same formulas give Hom_R(UN,F)=U Hom_S(N,C₀F), naturally in N and F.
   The tensor balancing maps are ordinary balancing on pure tensors. Apply
   them on every summand of the tensor total complex and then localize.
   K-flat B-representatives make the displayed normalization unique.
3. Resolve bounded-below K by a bounded-below complex I of injectives
   (lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative). Termwise C₀I is K-injective
   over S, since U is exact (lem-weil-pbc-right-adjoint-preserves-kinjective),
   and vanishes below the same degree. It represents C(K). Forgetting its
   action gives precisely Hom_R(S[0],I), hence RHom_R(S,K).
4. For any cochain representative A of M, take the products of the sheaf
   isomorphisms in step 2 over all p in degree n (def-pur-hom-complex).
   Evaluation commutes with postcomposition by d_I, hence with the signed
   Hom differential. This gives an isomorphism of Hom complexes, including
   their sheaf structures, not just a bijection of global morphisms.
5. Localize. K-injectivity over R and over S computes the two internal Homs
   (def-pur-derived-internal-hom). Exact restriction preserves quasi-isomorphisms.
   Independence of representatives and resolutions follows from
   lem-pur-rhom-well-defined. The formulas commute with maps in both variables,
   giving the natural isomorphism. Its evaluation transpose is exactly
   coinductionInternalHomMap, with the normalized balancing map of step 2.
   Only C(K), not either internal Hom, is asserted bounded below.
-/
theorem potential_coinduction (l r s : ℕ) [Fact l.Prime]
    (_hs : 1 ≤ s) (hsr : s ≤ r) (X : Scheme.{u}) :
    InternalCoinductionComparison
      ((ZMod.castHom (pow_dvd_pow l hsr) (ZMod (l ^ s))).ulift :
        ULift.{u + 1} (ZMod (l ^ r)) →+* ULift.{u + 1} (ZMod (l ^ s))) X := by
  sorry

end AlgebraicGeometry.Etale
