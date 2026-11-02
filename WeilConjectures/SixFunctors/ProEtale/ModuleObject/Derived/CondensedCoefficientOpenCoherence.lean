/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # Condensed coefficient and open comparison coherence

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-thm-sf-compatibility/fix-prop-coherence.md
and its proof, tensor reassociation, evaluation and adjunction units and counits.
(blueprint: def-sf-open-quotient-koszul-models).

All functors below are the ordinary derived functors of internal condensed modules.
The comparison components are the imported canonical constructions. The structures
record coherence data, not an existence or preservation theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ambient category D(T,Lambda), with the existing pulled-back condensed ring.
Source: standing setting (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev OpenCoherenceDerived (A : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  DerivedCategory (ModuleRingedComparison.internalModules A.X X)

/-- The intrinsic finite-Tor constructible domain of the standing setting.
Source: standing setting (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev OpenCoherenceCtf (A : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  CondensedConstructibleFiniteTor A.X X

/-- Restriction of actual scalar extension, using only the supplied domain certificate.
Source: exceptional comparison domain (blueprint: def-sf-open-quotient-koszul-models). -/
def openCoherenceScalar {A B : ScalarSixRing.{u}} (a : A ⟶ B) (X : Scheme.{u})
    (h : ∀ K : OpenCoherenceCtf A X,
      condensedConstructibleFiniteTor B.X X ((scalarSixChange a X).obj K.obj)) :
    OpenCoherenceCtf A X ⥤ OpenCoherenceCtf B X :=
  ObjectProperty.lift _ ((condensedConstructibleFiniteTor A.X X).ι ⋙ scalarSixChange a X) h

/-- Restriction of the prescribed proper/open compact-support functor.
Source: exceptional comparison domain (blueprint: def-sf-open-quotient-koszul-models). -/
def openCoherenceLower (A : ScalarSixRing.{u}) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ K : OpenCoherenceCtf A X, condensedConstructibleFiniteTor A.X Y
      ((rightDerivedLowerShriekOfCompactification A.X c).obj K.obj)) :
    OpenCoherenceCtf A X ⥤ OpenCoherenceCtf A Y :=
  ObjectProperty.lift _ ((condensedConstructibleFiniteTor A.X X).ι ⋙
    rightDerivedLowerShriekOfCompactification A.X c) h

/-- Supplied exceptional adjunctions and certificates permitting their stated domains.
No existence, preservation, or invertibility assertion is made by this data type.
Source: exceptional-adjoint proviso (blueprint: def-sf-open-quotient-koszul-models). -/
structure OpenCoherenceExceptionalContext {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  scalarX : ∀ K : OpenCoherenceCtf A X,
    condensedConstructibleFiniteTor B.X X ((scalarSixChange a X).obj K.obj)
  scalarY : ∀ K : OpenCoherenceCtf A Y,
    condensedConstructibleFiniteTor B.X Y ((scalarSixChange a Y).obj K.obj)
  lowerA : ∀ K : OpenCoherenceCtf A X, condensedConstructibleFiniteTor A.X Y
    ((rightDerivedLowerShriekOfCompactification A.X c).obj K.obj)
  lowerB : ∀ K : OpenCoherenceCtf B X, condensedConstructibleFiniteTor B.X Y
    ((rightDerivedLowerShriekOfCompactification B.X c).obj K.obj)
  rightA : OpenCoherenceCtf A Y ⥤ OpenCoherenceCtf A X
  rightB : OpenCoherenceCtf B Y ⥤ OpenCoherenceCtf B X
  adjA : openCoherenceLower A c lowerA ⊣ rightA
  adjB : openCoherenceLower B c lowerB ⊣ rightB

/-- Exceptional comparison with exactly the two structural adjunction equations.
The comparison need not be invertible. All maps used in the equations are the
supplied adjunctions or the prescribed compact-support comparison.
Source: structural-arrow family, exceptional unit and counit
(blueprint: def-sf-open-quotient-koszul-models). -/
structure OpenCoherenceExceptionalComparison {A B : ScalarSixRing.{u}} {a : A ⟶ B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (H : OpenCoherenceExceptionalContext a c) where
  beta : H.rightA ⋙ openCoherenceScalar a X H.scalarX ⟶
    openCoherenceScalar a Y H.scalarY ⋙ H.rightB
  unit : ∀ K : OpenCoherenceCtf A X,
    (openCoherenceScalar a X H.scalarX).map (H.adjA.unit.app K) ≫
      beta.app ((openCoherenceLower A c H.lowerA).obj K) ≫
      H.rightB.map (H.gamma K) =
        H.adjB.unit.app ((openCoherenceScalar a X H.scalarX).obj K)
  counit : ∀ K : OpenCoherenceCtf A Y,
    H.gamma (H.rightA.obj K) ≫ (openCoherenceLower B c H.lowerB).map (beta.app K) ≫
      H.adjB.counit.app ((openCoherenceScalar a Y H.scalarY).obj K) =
        (openCoherenceScalar a Y H.scalarY).map (H.adjA.counit.app K)

/-- The actual integral quotient map at positive exponent n+1.
Source: finite-reduction paragraph (blueprint: def-sf-open-quotient-koszul-models). -/
def openCoherenceIntegralReduction (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) : (⟨twistIntegralRing ell E⟩ : ScalarSixRing.{u}) ⟶
      ⟨twistFiniteRing ell E n⟩ :=
  CommMon.homMk (Mon.ofHom (twistReduction ell E n))

/-- All finite quotient reductions, including the identity at equal positive levels.
Source: finite-reduction paragraph (blueprint: def-sf-open-quotient-koszul-models). -/
def openCoherenceFiniteReduction (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n m : ℕ) (hmn : m ≤ n) :
    (⟨twistFiniteRing ell E n⟩ : ScalarSixRing.{u}) ⟶ ⟨twistFiniteRing ell E m⟩ :=
  let step : ∀ j : ℕ, (⟨twistFiniteRing ell E (j + 1)⟩ : ScalarSixRing.{u}) ⟶
      ⟨twistFiniteRing ell E j⟩ :=
    fun j ↦ CommMon.homMk (Mon.ofHom (twistFiniteReduction ell E j))
  Nat.leRecOn (C := fun j ↦
    (⟨twistFiniteRing ell E j⟩ : ScalarSixRing.{u}) ⟶ ⟨twistFiniteRing ell E m⟩)
    hmn (fun {j} b ↦ step j ≫ b) (𝟙 _)

/-- The canonical six comparison components at a coefficient map, with exchange.
These are aliases of the dependency declarations; no new comparison is chosen.
Source: retained comparison families (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev openCoherenceTensor {A B : ScalarSixRing.{u}} (a : A ⟶ B) (X : Scheme.{u})
    (K M : OpenCoherenceDerived A X) := scalarSixTensorIso a X K M

/-- The evaluation-transpose Hom component, unchanged.
Source: retained h (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev openCoherenceHom {A B : ScalarSixRing.{u}} (a : A ⟶ B) (X : Scheme.{u})
    (K M : OpenCoherenceDerived A X) := scalarSixHomComparison a X K M

/-- The prescribed scalar/open extension-by-zero isomorphism.
Source: displayed s formula (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev openCoherenceOpen {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  derivedOpenImmersionShriekIso (Λ := A.X) (Λ' := B.X) a.hom.hom j

/-- The unit/square/counit derived exchange mate, unchanged.
Source: derived exchange clause (blueprint: def-sf-open-quotient-koszul-models). -/
abbrev openCoherenceExchange (A : ScalarSixRing.{u}) {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) := moduleObjectDerivedExchange A.X sq

-- Keep the native derived-category implementations opaque during endpoint matching.
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 2000000 in
-- The simultaneous scalar/adjunction endpoint checks exceed the default elaboration budget.
end AlgebraicGeometry.ProEtale.CondensedRing
