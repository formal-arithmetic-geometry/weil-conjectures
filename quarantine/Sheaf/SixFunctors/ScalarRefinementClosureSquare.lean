/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CompactificationRefinementLocalizing
public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Compactification.NagataDensityNormalization
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Compactification.NagataDensityNormalizationSheaves
import Sheaf.SixFunctors.ScalarSixCtf
import Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization
import Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization
import Sheaf.Paper.IdentityOpenDerivedRestriction
import Sheaf.Paper.IdentityOpenUnderivedSquareNormalization
import Sheaf.Paper.OpenExtensionConstructibleFiniteTor
import Sheaf.SixFunctors.OpenScalarConjugateNormalization

/-! # Scalar extension and compactification refinements

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Independence paragraph
(blueprint: lem-sfb-scalar-refinement-closure-square).

Both squares use the published adjunction transpose and scalar conjugate. The second
square includes the actual proper-composition transport from p h to p'.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical open scalar comparison delta, with bundled condensed coefficients.
Source: blueprint scalar compact-support proof, Independence paragraph
(blueprint: lem-sfb-scalar-refinement-closure-square). -/
def scalarRefinementOpenIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ scalarSixChange a Z ≅
      scalarSixChange a X ⋙ (openImmersionLowerShriek Λ'.X j).mapDerivedCategory :=
  derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j

/-- The coefficient comparison C_c = Rp_*(delta_j) gamma_p.
Source: blueprint scalar compact-support proof, Independence paragraph
(blueprint: lem-sfb-scalar-refinement-closure-square). -/
def scalarCompactificationComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X c.g).obj
        ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K)) ⟶
      (RootCoordinateFace.lower Λ'.X c.g).obj
        ((openImmersionLowerShriek Λ'.X c.i).mapDerivedCategory.obj
          ((scalarSixChange a X).obj K)) :=
  (scalarDirectImageMate a c.g).app
      ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K) ≫
    (RootCoordinateFace.lower Λ'.X c.g).map ((scalarRefinementOpenIso a c.i).hom.app K)

/-- Proper composition Rh_* then Rp_*, identified with Rp'_* by the refinement triangle.
Source: blueprint scalar compact-support proof, application of Rp_*
(blueprint: lem-sfb-scalar-refinement-closure-square). -/
def scalarRefinementComposition (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    RootCoordinateFace.lower Λ.X r.hom.hom.hom ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g ≅
      RootCoordinateFace.lower Λ.X d.obj.obj.g :=
  (RootCoordinateFace.lowerComp Λ.X r.hom.hom.hom c.obj.obj.g).symm ≪≫
    eqToIso (congrArg (RootCoordinateFace.lower Λ.X) r.hom.hom.hom_g)

/-- The pushed refinement phi_h = Rp_*(e_h), with its proper-composition identification.
Source: blueprint scalar compact-support proof, application of Rp_*
(blueprint: lem-sfb-scalar-refinement-closure-square). -/
def scalarRefinementPushforward (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (RootCoordinateFace.lower Λ.X c.obj.obj.g).obj
        ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj K) ⟶
      (RootCoordinateFace.lower Λ.X d.obj.obj.g).obj
        ((openImmersionLowerShriek Λ.X d.obj.obj.i).mapDerivedCategory.obj K) :=
  (RootCoordinateFace.lower Λ.X c.obj.obj.g).map (localizingRefinementMap Λ.X r K) ≫
    (scalarRefinementComposition Λ r).hom.app
      ((openImmersionLowerShriek Λ.X d.obj.obj.i).mapDerivedCategory.obj K)

/-- Dense refinement and schematic-closure identifications are invertible and commute
with the specified scalar comparisons before and after proper direct image.
Source: blueprint scalar compact-support proof, Independence paragraph
(blueprint: lem-sfb-scalar-refinement-closure-square).

Proof:
1. lem-sfb-open-extension-zero-constructible-finite-tor puts j'_!K in Dctf, and
 det-prop-scalar-six-ctf puts T_X K in Dctf. Use the invertible open units from
lem-sfb-condensed-open-adjunction-localization over both coefficient rings.
2. lem-sfb-proper-direct-image-coefficient-restriction gives the open square for gamma_h.
The inverse-image condition makes the restricted map 1_X. Identify its exchange with
r_h by lem-sfb-identity-open-derived-restriction, the counit equation of
lem-sfb-identity-open-derived-adjunction-normalization and the underived normalization
lem-sfb-identity-open-underived-square-normalization. Then j^* gamma_h is T_X r_h
under these identifications. lem-sfb-open-scalar-conjugate-normalization identifies
j^* delta_j with the same K-flat scalar/pullback comparison and the actual open units.
3. The definition of localizingRefinementMap gives theta j^*e unit = identity.
Naturality of r_h and step 2 make both displayed composites have this same adjunct.
Cancel theta and the invertible open unit, and apply the open Hom bijection. This
proves the first square, with the actual specified maps, in both geometric cases.
4. det-sf-comp-coherence-refinement proves invertibility in the dense case. In the
closure case det-nagata-density-normalization-sheaves and
sk-lem-nagata-density-normalization give the unit-induced identification, whose open
restriction is identity. The Hom bijection identifies it with this same e_h. Repeat
for T_X K. No density of the original compactification is required in this case.
5. Apply Rp_* to the first square. Expand gamma_ph by composition and use naturality
of gamma_p at e_h, both from det-prop-scalar-six-direct-image (2). Reassociate to
obtain phi_(T_X K) C_c = C_c' T_Y(phi_K), with scalarRefinementComposition giving
exactly the proper-composition and refinement-triangle identifications. -/
theorem scalarRefinementClosureSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c d : Compactification.BoundaryCompactification f.left) (r : d ⟶ c)
    (_hcases :
      (IsSchemeTheoreticallyDominant c.obj.obj.i ∧
        IsSchemeTheoreticallyDominant d.obj.obj.i) ∨
      ∃ e : d.obj.obj.Z ≅ c.obj.obj.i.image,
        e.hom ≫ c.obj.obj.i.imageι = r.hom.hom.hom ∧
          d.obj.obj.i ≫ e.hom = c.obj.obj.i.toImage)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left))
    (_hK : constantModelBoundedConstructible Λ.X X.left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    IsIso (localizingRefinementMap Λ.X r K) ∧
    IsIso (localizingRefinementMap Λ'.X r ((scalarSixChange a X.left).obj K)) ∧
    ((scalarSixChange a c.obj.obj.Z).map (localizingRefinementMap Λ.X r K) ≫
        (scalarDirectImageMate a r.hom.hom.hom).app
          ((openImmersionLowerShriek Λ.X d.obj.obj.i).mapDerivedCategory.obj K) ≫
        (RootCoordinateFace.lower Λ'.X r.hom.hom.hom).map
          ((scalarRefinementOpenIso a d.obj.obj.i).hom.app K) =
      (scalarRefinementOpenIso a c.obj.obj.i).hom.app K ≫
        localizingRefinementMap Λ'.X r ((scalarSixChange a X.left).obj K)) ∧
    (scalarCompactificationComparison a c.obj.obj K ≫
        scalarRefinementPushforward Λ' r ((scalarSixChange a X.left).obj K) =
      (scalarSixChange a Y.left).map (scalarRefinementPushforward Λ r K) ≫
        scalarCompactificationComparison a d.obj.obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
