module

public import Sheaf.Paper.AffineLinePuritySource
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # The affine-line purity comparison

Source: main-20261015, sec-smooth-purity/sk-prop-an,
def-pur-affine-line-purity-comparison, order 2318
(blueprint: def-pur-affine-line-purity-comparison).

## Main definitions

* `integration`: restriction of the projective trace by the actual open counit.
* `projectionIso` and `augmentation`: Pi_K and a_K with the specified tensor order.
* `sourceWitness`: the retained canonical ordinary origin of M_K.
* `affineLinePurityComparison`: the specified restricted Hom transpose of a_K.

The trace is restricted by the actual extension-by-zero counit. Inverse canonical
projection and the coefficient unitor define a_K. Its specified bounded etale-origin
transpose defines gamma. The chosen representative supplies only applicability data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineLinePurity

open VectorIntegrationSite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ) (Y : Scheme.{u})
variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)

/-- Restrict the existing projective trace by the actual open-extension counit.
The initial comparison identifies C_X j_e^* B_P[2] with j_p^* C_P B_P[2].
Source: main-20261015, integration display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def integration [IsNoetherian Y] (hY : IsUnit (l : Γ(Y, ⊤))) :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLineCompactification Y)).obj (coefficient l E n Y r hA) ⟶
        unit (Scheme.finiteTateCoefficient l E n) Y :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (affineTraceLineCompactification Y)).map
      ((eqToIso (coefficient_comparison_eq l E n Y r hA)).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} Y)).map
          (eqToHom (etaleCoefficient_eq l E n Y r hA))) ≫
    restrictTrace (Scheme.finiteTateCoefficient l E n) Y
      ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)
      (projectiveTrace l E n Y hY (infinityCartier Y) r hA)

attribute [local irreducible] projectionMapOfCompactification

/-- Insert the two canonical signed symmetries around an invertible projection component.
Source: the coefficient-first projection display
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem reorderedProjection_isIso
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (h : IsIso (((projectionMapOfCompactification B c).app F).app K)) :
    IsIso (projection B c F K) := by
  unfold projection
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h inferInstance)

/-- Exact ordinary inverse image preserves boundedness via its canonical derived comparison.
Source: exact constant-coefficient inverse image
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem ordinaryPullback_bounded
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}} (f : X ⟶ Z)
    (W : Etale.DerivedCategoryModule A Z) (hW : DerivedCategory.TStructure.t.bounded W) :
    DerivedCategory.TStructure.t.bounded ((Etale.ordinaryFinitePullback A f).obj W) := by
  exact DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app W).symm
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).bounded_mapDerivedCategory_obj hW)

/-- A Tate sheaf in degree zero, shifted by two, is bounded in [-2,-2].
Source: the shifted Tate coefficient in the projection display
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem shiftedLine_bounded (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.bounded ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := by
  exact ⟨⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩,
    ⟨-2, DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2)⟩⟩

/-- The published projection comparison reduction, on the required ordinary origins.
Source: finite compact projection formula, boundedness and comparison steps
(blueprint: def-pur-affine-line-purity-comparison). -/
private theorem projectionFromOrigin_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (hW : DerivedCategory.TStructure.t.bounded W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Z)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z Ke)
    (eK : (comparison A Z).obj Ke ≅ K) :
    IsIso (projection (ModuleCat.{u + 1} A) c ((comparison A X).obj W) K) := by
  obtain ⟨a, b, hTor⟩ := hKe.2
  have hM := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hW
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hM hTor
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  have hPF := hasProjectionFormulaOfCompactification_of_comparison c
    (Iso.refl ((comparison A X).obj W)) eK hW hML inferInstance
  exact reorderedProjection_isIso (ModuleCat.{u + 1} A) c _ K hPF

-- Retain the public geometric applicability parameters; the generic proof needs fewer.
set_option linter.unusedVariables false in
/-- Invertibility of precisely the symmetry-adjusted canonical projection map.
Source: main-20261015, Pi_K paragraph
(blueprint: def-pur-affine-line-purity-comparison).
Proof: the ordinary Tate sheaf shifted by two is bounded in [-2,-2]. Exact
chart pullback and open extension preserve boundedness. The finite Tor interval
of Ke makes its tensor with that extension bounded below. Apply the finite-ring
proper projection formula and its published pro-etale comparison reduction at
the specified compactification, with eK and the literal coefficient origin.
The two signed tensor symmetries preserve invertibility of this canonical map.
No ambient exceptional adjunction is assumed. -/
theorem projection_isIso
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :
    ProjectionInvertible (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K := by
  have hW : DerivedCategory.TStructure.t.bounded (etaleCoefficient l E n Y r hA) := by
    unfold etaleCoefficient
    exact ordinaryPullback_bounded (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine.affineChart Y) _
      (shiftedLine_bounded (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine Y))
  unfold ProjectionInvertible
  exact projectionFromOrigin_isIso (Scheme.finiteTateCoefficient l E n)
    (affineTraceLineCompactification Y) (etaleCoefficient l E n Y r hA) hW K Ke hKe eK

/-- Pi_K is the inverse of PF, with the two specified tensor symmetries.
Source: main-20261015, Pi_K display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def projectionIso
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :=
  inverseProjection (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K
      (projection_isIso l E n Y r hA k aY hY K Ke hKe eK)

/-- The literal composite Pi_K, tensor of integration, and the coefficient right unitor.
The representative is used only to prove the projection map invertible.
Source: main-20261015, a_K display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def augmentation [IsNoetherian Y]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K) :=
  projectionTensorTrace (Scheme.finiteTateCoefficient l E n)
      (affineTraceLineCompactification Y) (coefficient l E n Y r hA) K
      (integration l E n Y r hA hY)
      (projection_isIso l E n Y r hA k aY hY K Ke hKe eK)

/-- The existing ordinary adjoint at the literal affine-chart compactification.
Source: ordinary exceptional adjunction (blueprint: def-pur-affine-line-purity-comparison). -/
instance ordinaryLeftAdjoint :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (affineTraceLineCompactification Y)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (Scheme.finiteTateCoefficient l E n) _

/-- The specified restricted transpose, before specializing the finite purity setting.
The source origin and tensor integration are the explicit constructions above.
Source: gamma display (blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def comparisonFromOrigin
    (k : Type u) [Field k] (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Y Ke)
    (eK : (comparison (Scheme.finiteTateCoefficient l E n) Y).obj Ke ≅ K.obj) :
    source l E n Y r hA K.obj ⟶
      (sfFiniteExceptionalAt (Scheme.finiteTateCoefficient l E n)
        (affineTraceLineCompactification Y)).obj K.obj :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  specifiedExceptionalHomEquiv (Scheme.finiteTateCoefficient l E n)
    (affineTraceLineCompactification Y)
    ⟨source l E n Y r hA K.obj, source_plus l E n Y r hA K.obj Ke hKe eK⟩
    (sourceWitness l E n Y r hA K.obj Ke hKe eK) K
      (augmentation l E n Y r hA hY k aY K.obj Ke hKe eK)

variable (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})

/-- The existing coefficient quotient at the node's positive exponent.
The Tate API is zero based: positivity gives (P.level - 1) + 1 = P.level.
Source: finite purity conventions (blueprint: def-pur-affine-line-purity-comparison). -/
abbrev Ring := Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)

/-- Canonical reindexing to the coefficient of the purity conventions.
Source: positive coefficient level (blueprint: def-pur-affine-line-purity-comparison). -/
def ringEquiv : Ring P ≃+* P.Coefficient :=
  RingEquiv.cast (R := fun m : ℕ ↦ ULift.{u + 1}
    (Padic.coefficientExtensionRing P.coefficients.l P.extension m))
      (Nat.sub_add_cancel P.level_pos)

variable (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)

/-- The coefficient prime is invertible on the base.
Source: finite purity conventions, ell different from the characteristic
(blueprint: def-pur-affine-line-purity-comparison).
Proof: def-pur-conventions supplies coefficientPrime_isUnit_stalk at every point.
The local criterion isUnit_of_isUnit_germ gives invertibility of the constant
global section ell; natCast is preserved by every germ map. The empty scheme
also satisfies this criterion. -/
theorem primeUnit (aY : Y ⟶ Spec (.of P.field.k)) :
    IsUnit (P.coefficients.l : Γ(Y, ⊤)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk Y aY y

/-- The affine-line purity comparison gamma_{p,K}, defined as Phi(a_K).
The input Ke and eK are the chosen ordinary finite-Tor representative of K;
finiteTorComparisonNoetherian ensures that every K in D^b_ctf has such inputs.
No exceptional adjunction on arbitrary pro-etale complexes is used, and no
isomorphy of gamma is asserted.
Source: main-20261015, final affine-line purity comparison display
(blueprint: def-pur-affine-line-purity-comparison). -/
@[irreducible]
def affineLinePurityComparison
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    source P.coefficients.l P.extension (P.level - 1) Y r hA K.obj ⟶
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification Y)).obj K.obj :=
  comparisonFromOrigin P.coefficients.l P.extension (P.level - 1) Y r hA
    P.field.k aY (primeUnit P Y aY) K Ke hKe eK

end AlgebraicGeometry.ProEtale.AffineLinePurity
