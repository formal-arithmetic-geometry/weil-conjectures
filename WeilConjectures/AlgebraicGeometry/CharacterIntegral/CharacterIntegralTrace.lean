/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-! # The signed rational coordinate-tower trace

Source: latest blueprint, lem-fd-character-integral, zero-form paragraph, and its
DAG clarification concerning arbitrary algebraically closed coefficient fields.
The projective traces below retain the whole completed reference, rather than
only an unspecified rational isomorphism (blueprint: def-fd-character-integral-trace).
Every arrow is an actual open counit, projection comparison, or normalized projective trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CharacterIntegral
open DiagonalCoefficients RationalP1 CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))

/-- The existing degree-q model's coefficient module category, in the two rational
coefficient conventions. Source: blueprint coefficient preamble
(blueprint: def-fd-character-integral-trace). -/
abbrev Modules (T : Scheme.{u}) := DiagonalCoefficients.Modules (coefficient ℓ c).X T

/-- A projective-line coefficient family normalized by the actual completed
finite trace system and its root-normalized realization. In particular its trace
is not allowed to be rescaled together with its diagonal class.
Source: blueprint zero-form trace clarification and diagonal-tower coefficient
extension (blueprint: def-fd-character-integral-trace). -/
structure ProjectiveTraceData (T : Scheme.{u}) where
  family : Family ℓ T
  normalized :
    ∃ (iT : DiagonalTraceLocalizations ℓ T)
      (iP : DiagonalTraceLocalizations ℓ (ProjectiveLine T))
      (iW : DiagonalTraceLocalizations ℓ (diagonalSurface T)),
      letI := iT
      letI := iP
      letI := iW
      ∃ (hT : IsUnit (ℓ : Γ(T, ⊤)))
        (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface T))),
        DiagonalCompletionSpec ℓ (diagonalSurface T) D ∧
        DiagonalCycleSystemSpec ℓ T hT D ∧
        ∃ δ : diagonalCompletedDomain ℓ T ⟶ diagonalCompletedCodomain ℓ T,
          DiagonalTrace.IsDiagonalLimit ℓ T hT D δ ∧ Nonempty (Reference ℓ T δ family)

/-- Compact support for one coordinate, using the standard affine chart of P1.
Source: blueprint coordinate-tower integration
(blueprint: def-fd-character-integral-trace). -/
def lineLeft (T : Scheme.{u}) :
    DerivedCategory (Modules ℓ c (𝔸(PUnit.{u + 1}; T))) ⥤
      DerivedCategory (Modules ℓ c T) :=
  (CondensedRing.openImmersionLowerShriek (coefficient ℓ c).X
    (ProjectiveLine.affineChart T)).mapDerivedCategory ⋙
      moduleObjectDerivedPushforward (coefficient ℓ c).X (ProjectiveLine T ↘ T)

/-- Pull back to P1, twist by the existing positive root line and shift by two,
then restrict to its affine chart. This is the canonical a^*(-)(1)[2].
Source: blueprint coordinate-tower integration
(blueprint: def-fd-character-integral-trace). -/
def lineRight (T : Scheme.{u}) :
    DerivedCategory (Modules ℓ c T) ⥤
      DerivedCategory (Modules ℓ c (𝔸(PUnit.{u + 1}; T))) :=
  moduleObjectDerivedPullback (coefficient ℓ c).X (ProjectiveLine T ↘ T) ⋙
    twist (coefficient ℓ c).X (ProjectiveLine T) (line ℓ c (ProjectiveLine T)) ⋙
      (CondensedRing.upperStar (coefficient ℓ c).X
        (ProjectiveLine.affineChart T)).mapDerivedCategory

/-- The ordered left word computes RΓc on the coordinate affine-space tower.
Source: blueprint iterated affine-line compactification and Fubini
(blueprint: def-fd-character-integral-trace). -/
def compact (T : Scheme.{u}) : (r : ℕ) →
    DerivedCategory (Modules ℓ c (affineTraceTower T r)) ⥤
      DerivedCategory (Modules ℓ c T)
  | 0 => 𝟭 _
  | r + 1 => lineLeft ℓ c (affineTraceTower T r) ⋙ compact T r

/-- The ordered right word is a^*(-)(r)[2r], retaining each canonical pullback,
root line and shift separately. Source: blueprint coordinate-tower trace
(blueprint: def-fd-character-integral-trace). -/
def twistedPull (T : Scheme.{u}) : (r : ℕ) →
    DerivedCategory (Modules ℓ c T) ⥤
      DerivedCategory (Modules ℓ c (affineTraceTower T r))
  | 0 => 𝟭 _
  | r + 1 => twistedPull T r ⋙ lineRight ℓ c (affineTraceTower T r)

/-- The object at the r-th stage of the right word, starting with the actual
coefficient unit. Source: blueprint Λ(r)[2r] convention
(blueprint: def-fd-character-integral-trace). -/
def twistedUnit (T : Scheme.{u}) (r : ℕ) :
    DerivedCategory (Modules ℓ c (affineTraceTower T r)) :=
  (twistedPull ℓ c T r).obj (unit (coefficient ℓ c).X T)

/-- The only extra witnesses used in the trace formula are proofs of
invertibility of the fixed projection comparisons at these shifted Tate lines.
All map data are in the normalized existing projective coefficient families.
Source: blueprint zero-form paragraph, finite traces followed by completion and
scalar extension (blueprint: def-fd-character-integral-trace). -/
structure TraceData (T : Scheme.{u}) where
  projective : ∀ r : ℕ, ProjectiveTraceData ℓ (affineTraceTower T r)
  projection : ∀ r : ℕ,
    IsIso (projectionMap (coefficient ℓ c).X
      (ProjectiveLine (affineTraceTower T r) ↘ affineTraceTower T r)
      (twistedUnit ℓ c T r)
      (((DerivedCategory.singleFunctor
        (Modules ℓ c (ProjectiveLine (affineTraceTower T r))) 0).obj
          (line ℓ c (ProjectiveLine (affineTraceTower T r)))) ⟦(2 : ℤ)⟧))

/-- One actual open counit followed by the normalized projective trace counit.
Source: blueprint projective-line-normalized affine-line integration
(blueprint: def-fd-character-integral-trace). -/
def coordinateTrace (T : Scheme.{u}) (d : TraceData ℓ c T) (r : ℕ) :
    (lineLeft ℓ c (affineTraceTower T r)).obj (twistedUnit ℓ c T (r + 1)) ⟶
      twistedUnit ℓ c T r :=
  let S := affineTraceTower T r
  let K := (twist (coefficient ℓ c).X (ProjectiveLine S)
    (line ℓ c (ProjectiveLine S))).obj
      ((moduleObjectDerivedPullback (coefficient ℓ c).X (ProjectiveLine S ↘ S)).obj
        (twistedUnit ℓ c T r))
  (moduleObjectDerivedPushforward (coefficient ℓ c).X (ProjectiveLine S ↘ S)).map
      ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (coefficient ℓ c).X (ProjectiveLine.affineChart S)).counit.app K) ≫
    counitComponent (coefficient ℓ c).X S (line ℓ c)
      (diagram ℓ c S (d.projective r).family) (twistedUnit ℓ c T r) (d.projection r)

/-- The unsigned ordered integration t_r: identity in rank zero, then the last
coordinate counit followed by the preceding coordinate integrations.
Source: blueprint normalized affine-space top trace
(blueprint: def-fd-character-integral-trace). -/
def integration (T : Scheme.{u}) (d : TraceData ℓ c T) : (r : ℕ) →
    (compact ℓ c T r).obj (twistedUnit ℓ c T r) ⟶ unit (coefficient ℓ c).X T
  | 0 => 𝟙 _
  | r + 1 => (compact ℓ c T r).map (coordinateTrace ℓ c T d r) ≫ integration T d r

/-- The vector-bundle trace in the purity convention of this node is (-1)^r t_r.
The sign multiplies the entire actual derived morphism, not merely a label.
Source: blueprint lem-fd-character-integral, DAG trace clarification
(blueprint: def-fd-character-integral-trace). -/
def trace (T : Scheme.{u}) (d : TraceData ℓ c T) (r : ℕ) :
    (compact ℓ c T r).obj (twistedUnit ℓ c T r) ⟶ unit (coefficient ℓ c).X T :=
  ((-1 : ℤ) ^ r) • integration ℓ c T d r

end AlgebraicGeometry.ProEtale.CharacterIntegral
