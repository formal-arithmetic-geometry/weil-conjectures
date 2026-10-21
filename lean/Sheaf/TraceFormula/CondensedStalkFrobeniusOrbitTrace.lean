/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.ProfinitePointPullback

/-!
# Condensed stalk Frobenius traces along an endomorphism orbit

Source: blueprint main-20261015, lem-trf-local-frobenius-conjugacy.proof.md, parts (2)--(3),
with the condensed coefficient analogue specified in the DAG
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (Ψ : End X) (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Ψ).obj M ≅ M)

/-- The point over itself has locally finite-type structure map, the identity.
Source: blueprint local Frobenius conjugacy, part (2)
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace). -/
instance condensedOrbitPointLocallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

/-- The point over itself has quasi-compact structure map, the identity.
Source: blueprint local Frobenius conjugacy, part (2)
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace). -/
instance condensedOrbitPointQuasiCompact :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

/-- The point over itself has separated structure map, the identity.
Source: blueprint local Frobenius conjugacy, part (2)
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace). -/
instance condensedOrbitPointIsSeparated :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The iterated Weil isomorphism: identity comparison at zero, and pull back the preceding
iterate along Ψ before applying ψ at a successor. The composition comparison is the restriction
of the canonical module-object derived comparison.
Source: blueprint local Frobenius conjugacy, parts (2)--(3)
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace). -/
def condensedOrbitWeilIterate (n : ℕ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (Ψ ^ n)).obj M ≅ M :=
  match n with
  | 0 => (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app M
  | n + 1 =>
    (eqToIso (congrArg
      (fun f : End X ↦
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)
      (pow_succ Ψ n))) ≪≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Ψ (Ψ ^ n)).app M ≪≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Ψ).mapIso
      (condensedOrbitWeilIterate n) ≪≫ ψ

/-- Fixed-point stalk Frobenius: identify the stalk with pullback along the common composite,
apply the pullback compositor, and then pull back the iterated Weil map.
Source: blueprint local Frobenius conjugacy, parts (2)--(3)
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace). -/
def condensedOrbitStalkFrobenius (n : ℕ) (z : Over.mk (𝟙 (Spec (.of k))) ⟶ X)
    (hz : z ≫ Ψ ^ n = z) :
    End ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj M) :=
  (eqToIso (congrArg
    (fun f : Over.mk (𝟙 (Spec (.of k))) ⟶ X ↦
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)
    hz.symm)).hom ≫
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ z (Ψ ^ n)).hom.app M ≫
  (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).map
    (condensedOrbitWeilIterate ℓ Ψ M ψ n).hom

/-- A fixed point's translate is fixed, and the two stalk Frobenius traces coincide in the
endomorphisms of the coefficient unit, using the canonical Koszul braiding.
Source: blueprint local Frobenius conjugacy, parts (2)--(3), condensed analogue
(blueprint: lem-zl-condensed-stalk-frobenius-orbit-trace).

Proof: (1) Commuting powers of Ψ give z[j+m] = z[j], hence fixedness of the translate.
(2) Let B[j] be the pullback at z[j], and A[j] : B[j+1] ≅ B[j] the pullback of ψ preceded
by the composition comparison. Coherence from lem-weil-pbc-profinite-point-pullback gives
A[j+m] = A[j] after the fixed-point identifications.
(3) Induction on r, simultaneously for all j, expands pullback of ψ[r] as
A[j] ... A[j+r-1]. The base is the identity comparison; the successor uses naturality and
associativity of the pullback compositors. At r=m this is the stated stalk operator.
(4) Associativity and A[m]=A[0] give A[0] V[1,m] = V[0,m] A[0]. For m=0 both V are
identities and the same intertwining holds.
(5) Apply lem-zl-dualizable-categorical-trace-conjugacy, namely trace_eq_of_iso, to A[0]
and the two assumed right duals. Both traces belong to End of the same coefficient unit. -/
theorem condensed_stalk_frobenius_orbit_trace
    (m : ℕ) (z : Over.mk (𝟙 (Spec (.of k))) ⟶ X) (hz : z ≫ Ψ ^ m = z)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj M)]
    [HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (z ≫ Ψ)).obj M)] :
    ∃ htranslate : (z ≫ Ψ) ≫ Ψ ^ m = z ≫ Ψ,
      @trace _ _ _
        (boundedConstructibleBraiding (Profinite.padicAlgClRingObj ℓ)
          (Over.mk (𝟙 (Spec (.of k))))) _ _
        (condensedOrbitStalkFrobenius ℓ Ψ M ψ m (z ≫ Ψ) htranslate) =
      @trace _ _ _
        (boundedConstructibleBraiding (Profinite.padicAlgClRingObj ℓ)
          (Over.mk (𝟙 (Spec (.of k))))) _ _
        (condensedOrbitStalkFrobenius ℓ Ψ M ψ m z hz) := sorry

end AlgebraicGeometry.ProEtale.CondensedRing
