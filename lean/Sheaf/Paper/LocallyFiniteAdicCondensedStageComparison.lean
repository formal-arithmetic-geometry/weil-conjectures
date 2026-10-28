/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.Paper.LocallyFiniteAdicNormalizedFunctorData
public import Sheaf.Paper.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
import Sheaf.Paper.NativeScalarForgetting
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite tensor comparison with condensed coefficients

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- The actual coefficient comparison: bounded finite-field functions are locally finite
functions. Source: Bhatt--Scholze, Lemma 6.8.2, via the two published ring comparisons
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def condensedNativeMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ProEtale.padicAlgClRingObj X l ⟶ abRing l X :=
  (ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
    ProEtale.padicAlgClSheafToAdicConstantSheaf X l

instance condensedNativeMap_isMonHom (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsMonHom (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

instance condensedNativeMap_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsIso (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

/-- Transport native modules to the condensed coefficient, retaining their abelian sheaves.
Source: Bhatt--Scholze, Lemma 6.8.2; restriction along the specified ring isomorphism
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ProEtale.AdicSheaf.forgetAb l X ⋙ Mod.comap (condensedNativeMap l X)

instance nativeCondensedModules_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).IsEquivalence := by
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  letI : (Mod.comap (condensedNativeMap l X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedNativeMap l X)).isEquivalence_functor
  unfold nativeCondensedModules
  infer_instance

instance nativeCondensedModules_additive (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact derived transport along the same coefficient isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedDerived (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  (nativeCondensedModules l X).mapDerivedCategory

instance nativeCondensedDerived_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedDerived l X).IsEquivalence := by
  unfold nativeCondensedDerived
  infer_instance

open AlgebraicallyClosedCoefficients (Index)

/-- Only finite-stage data: full faithful functors on raw rational stages, scalar comparisons,
and their action on a representative. No statement about a Hom colimit is included.
Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
structure CondensedStageComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (D : NormalizedFunctor l X) where
  finite : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      ProEtale.PadicSubfieldConstructible X l E
  full : ∀ E, (finite E).Full
  faithful : ∀ E, (finite E).Faithful
  scalar : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    finite E ⋙ ProEtale.constructibleExtendScalars X l h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        finite L
  objectIso : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    (nativeCondensedDerived l X).obj (D.J.obj A) ≅
      ((ProEtale.constructibleToPadicAlgCl X l A.stage).obj
        ((finite A.stage).obj A.obj)).obj
  representative : ∀ {A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X}
    (L : Index l (PadicAlgCl l)) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : A.toStage hA ⟶ B.toStage hB),
    (nativeCondensedDerived l X).map
        (D.J.map (StageSystem.PairCategory.mkHom L hA hB f)) =
      (objectIso A).hom ≫
        (((ProEtale.constructibleToPadicAlgClCompIso X l hA).inv.app
              ((finite A.stage).obj A.obj) ≫
            (ProEtale.constructibleToPadicAlgCl X l L).map
              ((scalar hA).hom.app A.obj ≫ (finite L).map f ≫
                (scalar hB).inv.app B.obj) ≫
            (ProEtale.constructibleToPadicAlgClCompIso X l hB).hom.app
              ((finite B.stage).obj B.obj)).hom) ≫
        (objectIso B).inv

/-- Finite coefficient realization agrees with the normalized native tensor formula.

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14(2),
and Remark 6.8.15; the finite-stage identification in the parent Hom-descent proof
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison).

Proof in words: first apply the integral identity equivalence between strict-tower and
completed integral presentations, and rationalize it. Compose with the continuous rational
realization at the finite field. The section-ring comparison for that finite condensed
coefficient identifies continuous modules with internal modules. Constructible rational
Hom comparison makes this finite realization full and faithful; preservation of local
finite freeness puts its image in the bounded constructible condensed category. Neither
essential surjectivity of this finite functor nor a closure Hom quotient is required.
For E ≤ L, inverse-completion
scalar coherence, the continuous realization scalar comparison, and balanced tensor
transitivity give the displayed scalar isomorphism. The finite coefficient inclusion
followed by condensedNativeMap is the specified rational inclusion of D: both maps evaluate
a function by the fixed embedding. Integral residue normalization identifies their integral
maps. Hence D.integral identifies the integral restrictions of both realizations. The
universal property of localization extends this identification to the raw rational stage,
giving objectIso. On an integral arrow its naturality is exactly that of D.integral;
inverse uniformizer powers are preserved by functoriality. The equation D.common_field
identifies the transition isomorphisms with the same completion and tensor comparisons.
Write a representative as isoToStage, then a stage arrow, then the inverse isoToStage.
Mapping this expression proves the representative equation. Identity extensions use the
unit comparison; repeated fields and zero objects use the same formulas. For the empty
scheme the categories and formulas are the zero ones. This lemma asserts finite tensor
normalization only, with no Hom-surjectivity, eventual equality, or essential-image claim
at the algebraic closure.
-/
theorem condensedStageComparison_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    Nonempty (CondensedStageComparison l X D) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
