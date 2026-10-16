/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel

/-! Scalar-counit normalization for the residue pull square.

The tensor presentation on X has already been normalized to its defining counit.
Only the scalar mate and the ordinary balanced tensor comparison occur below.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
set_option backward.isDefEq.respectTransparency false in
/-- The scalar pull square, followed by the tensor-presentation counit on X,
computes the ordinary pullback model map. No derived tensor comparison occurs.

Source: Bhatt--Scholze, Remark 6.8.15 and the tensor-pullback identity in the
proof of Lemma 6.5.9(5), p. 51. The counit normalization below is the explicit
formal comparison argument, rather than a separately stated lemma of the paper.
(blueprint: new-integral-residue-scalar-counit-model)

Proof. Write F for integral pullback, G for residue pullback, S for restriction,
and T for extension of scalars; append subscripts X and Y for the sites. Write
Fh, Gh, Sh, Th for their homotopy functors and LF, LG, LT for the derived ones.
Let gamma denote their left-derived counits. Restriction and both pullbacks
are exact. Let q : SY then F -> G then SX be the ordinary restriction/pullback
isomorphism, and let p : F then TX -> TY then G be its inverse scalar-adjunction
mate. Its homotopy version is ph and its derived version is pd. The latter is
exactly residueExchangePullComparisons.pull.hom by the definition of PullHom.

First apply the mate unit identity and the defining unit identity of the
derived extension/restriction adjunction. Naturality of gamma and the triangle
identities give, at P,
pd(Qh P) followed by LG(gamma_TY(P)) followed by gamma_G(ThY P)
= LTX(gamma_F(P)) followed by gamma_TX(Fh P) followed by Qh(ph(P)).
To see this without choosing resolutions, transpose both sides along the
extension/restriction adjunction on X. Both transposes are q at the image of
P, followed by the ordinary extension unit; the exact-functor comparisons
commute with these units by the derived adjunction's defining unit formula.
The adjunction hom-equivalence is injective, giving the displayed equality.
Use the inverse of pd to rewrite it in the direction needed here, apply SX,
and compose with the exact restriction/pullback comparison.

Next expand epsilon_X = tensorPresentationDerivedCounit: it is the extension
counit gamma_TX, followed by exact restriction's comparison, followed by the
ordinary extendComapTensorIso. The previous identity cancels the scalar mate
in the claimed composite. What remains is the ordinary comparison between
pullback of the balanced tensor presentation on Y and that presentation on X.
The coefficient isomorphism e is q on the residue regular module, followed by
restriction of the inverse monoidal unit of G; eH is its homotopy image.
Consequently this remaining comparison is the ordinary tensor comparison for
F, after F applied to the Y presentation and after eH inverse on the first
factor. Explicitly, after forgetting module actions and precomposing with the
balanced tensor coequalizer epimorphism, both morphisms pull back the residue
coefficient and the module argument and apply the same scalar action. The
relations agree by naturality of coefficientMap. The inverse unit in e cancels
the pulled-back regular residue module. The coequalizer universal property
and faithfulness of forgetting actions therefore give equality of module
morphisms. Naturality makes this equality compatible with the differentials,
so it passes to homotopy complexes and then to Qh.

Finally combine this ordinary equality with the preceding counit identity.
The resulting composite is LF applied to the Y tensor-presentation counit,
then gamma_F, then Qh applied to Fh of homotopyTensorSingleIso inverse and the
ordinary oplax tensor comparison. This is tensorModelMap by definition, hence
residueExchangeTensorModelMap. No tensor-model target, tensor comparison, or
extension counit has been inverted. In particular the argument applies to
arbitrary P and requires no flatness hypothesis. -/
theorem integralResidue_scalarCounit_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    let F := (f)^*⟦integralCoeff ℓ E⟧
    let B := residueExchangeOrdinaryCoefficient ℓ E Y
    let B' := residueExchangeOrdinaryCoefficient ℓ E X
    let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (integralReductionMap ℓ E) X)
    letI := residueOrdinaryUpperStarMonoidal A f
    let e : F.obj B ≅ B' :=
      (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app
        (Mod.regular (condensedRingObj A Y)) ≪≫
          SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
      Functor.tensorModelCoefficient B' := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    let φX := coefficientMap (integralReductionMap ℓ E) X
    let H := residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X
    let εX : DerivedCategory.Qh ⋙ H ⟶
        (tensorLeft B').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
      unfold H B' residueExchangeOrdinaryCoefficient
        residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit φX
    let M := DerivedCategory.Qh.obj P
    let a : (residueExchangeUpperStar (integralCoeff ℓ E) f).obj M ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P) := by
      unfold residueExchangeUpperStar
      exact F.leftDerivedFunctorCounit.app P
    (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj M) ≫
      (residueExchangeRestriction ℓ E X).map
        (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
      H.map a ≫
      εX.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        ((homotopyTensorSingleIso B').inv.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          eH.inv ▷ (F.mapHomotopyCategory (.up ℤ)).obj P) =
      residueExchangeTensorModelMap ℓ E f P := by sorry
end AlgebraicGeometry.ProEtale.CondensedRing
