module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.ProEtaleProperOpenInterchange
public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.SixFunctors.ScalarSixCtf
import Sheaf.SixFunctors.CtfStabilityDirectImages
import Sheaf.Paper.CondensedOpenSquareScalarComparison
import Sheaf.Paper.DerivedOpenSquareRestriction
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.SixFunctors.OpenScalarConjugateNormalization
import Sheaf.Paper.ScalarGeometricExchangeRectangle

/-!
# Coefficient compatibility of proper/open interchange

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-compact-support.proof.md, Composition paragraph.
(blueprint: lem-sfb-scalar-proper-open-interchange-square).

The interchange arrows are specified by the published identity-on-restriction
normalization. The two restriction equations below use forward open units, avoiding
an arbitrary choice of restriction isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
  {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar) [IsOpenImmersion i]
  (c : Compactification.BoundaryCompactification (p ≫ i))
  (A : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))

/-- The route that first extends the interchange arrow's coefficients, then applies
its proper direct-image mate and the canonical open coefficient comparison.
Source: blueprint compact-support proof, Composition, left route of the scalar square
(blueprint: lem-sfb-scalar-proper-open-interchange-square). -/
def scalarProperOpenLeft
    (m : D(openImmersionLowerShriek Λ.X i).obj
        ((RootCoordinateFace.lower Λ.X p).obj A) ⟶
      (RootCoordinateFace.lower Λ.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ.X c.obj.obj.i).obj A)) :
    (scalarSixChange a Ybar).obj (D(openImmersionLowerShriek Λ.X i).obj
        ((RootCoordinateFace.lower Λ.X p).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A)) :=
  (scalarSixChange a Ybar).map m ≫
    (scalarDirectImageMate a c.obj.obj.g).app
      (D(openImmersionLowerShriek Λ.X c.obj.obj.i).obj A) ≫
    (RootCoordinateFace.lower Λ'.X c.obj.obj.g).map
      ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom
        c.obj.obj.i).hom.app A)

/-- The route that first compares open extension and proper direct image with scalar
extension, and then applies the interchange over the new coefficients.
Source: blueprint compact-support proof, Composition, right route of the scalar square
(blueprint: lem-sfb-scalar-proper-open-interchange-square). -/
def scalarProperOpenRight
    (m' : D(openImmersionLowerShriek Λ'.X i).obj
        ((RootCoordinateFace.lower Λ'.X p).obj ((scalarSixChange a X).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A))) :
    (scalarSixChange a Ybar).obj (D(openImmersionLowerShriek Λ.X i).obj
        ((RootCoordinateFace.lower Λ.X p).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A)) :=
  (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i).hom.app
      ((RootCoordinateFace.lower Λ.X p).obj A) ≫
    D(openImmersionLowerShriek Λ'.X i).map ((scalarDirectImageMate a p).app A) ≫ m'

/-- Restriction of a route to Y using the actual open unit and the inverse open scalar
comparison on its source, and the published canonical exchange on its target. Thus
postcomposition with the inverse of Rp_* of the j' open unit gives the usual restricted
map from T Rp_* A to Rp_* T A. The theorem uses its equivalent forward-unit equation.
Source: blueprint compact-support proof, Composition, restriction characterization
(blueprint: lem-sfb-scalar-proper-open-interchange-square). -/
def scalarProperOpenRestriction
    (m : (scalarSixChange a Ybar).obj (D(openImmersionLowerShriek Λ.X i).obj
        ((RootCoordinateFace.lower Λ.X p).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A))) :
    (scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X p).obj A) ⟶
      (RootCoordinateFace.lower Λ'.X p).obj
        (D(upperStar Λ'.X c.obj.obj.i).obj
          (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A))) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X i).unit.app
      ((scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X p).obj A)) ≫
    D(upperStar Λ'.X i).map
      ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i).inv.app
        ((RootCoordinateFace.lower Λ.X p).obj A)) ≫
    D(upperStar Λ'.X i).map m ≫
    compositionInterchangeRestriction Λ'.X p i c
      (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A))

/-- The normalized proper/open interchange commutes with every listed coefficient map.
Both restrictions are the specified direct-image mate under the canonical identifications;
the common source and target are bounded constructible of finite Tor amplitude.
The two interchange arrows are quantified with their defining normalization, which
uniquely determines them by properOpenInterchange; no additional geometric assumption
or arbitrary comparison map is supplied.

Source: blueprint latest, compact-support proof, Composition paragraph, returned step 6
(blueprint: lem-sfb-scalar-proper-open-interchange-square).

Proof plan:
1. det-sf-comp-composition-interchange identifies r inverse(Y) with X. Its open
   adjunctions give the canonical restriction rho. With sigma = Rp_*(u_j' inverse) rho,
   normalization reads u_i followed by i* iota followed by sigma equals the identity.
2. Transpose the defining Hom chain under p* left adjoint to Rp_*. The adjunct formula
   in lem-sfb-condensed-open-square-scalar-comparison and the open triangle identity
   identify rho with the unit-square-counit exchange of def-weil-pbc-ambient-ringed-exchange.
   lem-sfb-derived-open-square-restriction descends the same formula to unbounded complexes.
3. The pullback comparison in det-prop-scalar-six-direct-image is inverse theta of
   det-prop-scalar-six-pullback. lem-sfb-kflat-scalar-comparison-normalization identifies
   it with the balanced K-flat comparison. Apply lem-sfb-scalar-geometric-exchange-rectangle
   and lem-sfb-open-scalar-conjugate-normalization for i and j'. No scalar flatness is used.
4. Naturality of rho and gamma and the j' normalization give sigma i*(gamma_r then
   Rr_*delta_j') = gamma_p T(sigma) c_i. Substitute the normalization of the first iota
   and the i open scalar normalization. This proves the left restriction equation.
   The normalization of the second iota and naturality of u_i give the right one.
   Multiplying by Rp_*(u_j') writes these two equations in the forward-unit form below.
5. Precompose both routes with delta_i inverse. Their open adjuncts agree by step 4.
   Injectivity of the open adjunction bijection, followed by cancellation of delta_i
   inverse, proves the square. Restriction need not be faithful on arbitrary objects.
6. det-thm-sf-ctf-stability-direct-images (2),(3) preserves Dctf under p, the open i,
   the open j' and proper r. det-prop-scalar-six-ctf (3) preserves it under the listed
   scalar map. Applying these in the two orders gives the two endpoint assertions. -/
theorem scalarProperOpenInterchangeSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_ha : ListedCoefficientMap ell a)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Ybar.Over (Spec (.of k))]
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of k))] [QuasiCompact (Ybar ↘ Spec (.of k))]
    [IsSeparated (Ybar ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [QuasiCompact i] [IsProper p] [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (hA : constantModelBoundedConstructible Λ.X X A ∧ DerivedCategory.finiteTorAmplitude _ A)
    (m : D(openImmersionLowerShriek Λ.X i).obj
        ((RootCoordinateFace.lower Λ.X p).obj A) ⟶
      (RootCoordinateFace.lower Λ.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ.X c.obj.obj.i).obj A))
    (_hm : compositionInterchangeIsNormalized Λ.X p i c A m)
    (m' : D(openImmersionLowerShriek Λ'.X i).obj
        ((RootCoordinateFace.lower Λ'.X p).obj ((scalarSixChange a X).obj A)) ⟶
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
        (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A)))
    (_hm' : compositionInterchangeIsNormalized Λ'.X p i c ((scalarSixChange a X).obj A) m') :
    scalarProperOpenLeft a p i c A m = scalarProperOpenRight a p i c A m' ∧
    scalarProperOpenRestriction a p i c A (scalarProperOpenLeft a p i c A m) =
      (scalarDirectImageMate a p).app A ≫
        (RootCoordinateFace.lower Λ'.X p).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X c.obj.obj.i).unit.app
            ((scalarSixChange a X).obj A)) ∧
    scalarProperOpenRestriction a p i c A (scalarProperOpenRight a p i c A m') =
      (scalarDirectImageMate a p).app A ≫
        (RootCoordinateFace.lower Λ'.X p).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X c.obj.obj.i).unit.app
            ((scalarSixChange a X).obj A)) ∧
    (constantModelBoundedConstructible Λ'.X Ybar
        ((scalarSixChange a Ybar).obj (D(openImmersionLowerShriek Λ.X i).obj
          ((RootCoordinateFace.lower Λ.X p).obj A))) ∧
      DerivedCategory.finiteTorAmplitude _
        ((scalarSixChange a Ybar).obj (D(openImmersionLowerShriek Λ.X i).obj
          ((RootCoordinateFace.lower Λ.X p).obj A)))) ∧
    (constantModelBoundedConstructible Λ'.X Ybar
        ((RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
          (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A))) ∧
      DerivedCategory.finiteTorAmplitude _
        ((RootCoordinateFace.lower Λ'.X c.obj.obj.g).obj
          (D(openImmersionLowerShriek Λ'.X c.obj.obj.i).obj ((scalarSixChange a X).obj A)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
