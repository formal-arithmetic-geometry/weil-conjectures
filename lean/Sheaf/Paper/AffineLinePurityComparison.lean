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

/-- Invertibility of precisely the symmetry-adjusted canonical projection map.
Source: main-20261015, Pi_K paragraph
(blueprint: def-pur-affine-line-purity-comparison).
Proof: the base and the affine line are finite type over k and Noetherian.
The restricted shifted Tate line is bounded constructible. Apply the pro-etale
clause of lem-weil-finite-compact-projection-formula to that line and Ke, using
eK and the identity witness for the line. The two signed tensor symmetries are
isomorphisms, so the coefficient-first composite is invertible. The theorem
uses the specified compactification, and never assumes an ambient adjunction. -/
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
  sorry

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
  sorry

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
