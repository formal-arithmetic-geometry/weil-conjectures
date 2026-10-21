/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.CoefficientHeart
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.StratifiedLattice
import Sheaf.Paper.IntegralRationalizationExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CartesianCoefficients
import Sheaf.SixFunctors.ScalarSixPullback
import Sheaf.Paper.CoefficientHeartFiltration
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.Paper.ContinuousRingUniverseRealization

/-!
# Integral lattice subquotients of a lisse extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-integral-models,
sk-lem-integral-models-generators.proof.md, proof (1)
(blueprint: lem-sfb-lattice-subquotient-filtration).

The assertion uses the actual condensed continuous coefficient rings, pulled back from
Profinite, and their internal module objects. Its lattices rationalize along their own
inclusions. Filtration terms are subobjects of the specified locally closed extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The subobject and lattice clauses over specified pulled-back coefficient rings.
This predicate records exactly the conclusion, without introducing any new sheaf notion.
Source: blueprint main-20261015, integral-models-generators, proof (1)
(blueprint: lem-sfb-lattice-subquotient-filtration). -/
def LatticeSubquotientFiltrationData
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a] : Prop :=
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        (∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)) ∧
        ∃ F : Fin (R.n + 1) →
            Subobject ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L),
          F 0 = ⊥ ∧ F (Fin.last R.n) = ⊤ ∧
          ∃ h : ∀ b : Fin R.n, F b.castSucc ≤ F b.succ,
            ∀ b : Fin R.n,
              letI : IsImmersion (R.immersion b) := R.isImmersion b
              Nonempty (cokernel (Subobject.ofLE (F b.castSucc) (F b.succ) (h b)) ≅
                (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
                  ((coefficientHeartLocallyClosedExtension A (R.immersion b ≫ a)
                    inferInstance).obj (M b)))

/-- The complete lattice and ordered subquotient assertion, with coefficients in the
canonical spectral norm topology. The lets install only the recorded coefficient
constructions and their structures, not extra hypotheses. The Noetherian structure is
constructed from finite type over the field. Locally closed extension is the existing
`i_* u_!` through the scheme-theoretic closure, for both integral and field coefficients.

Source: blueprint main-20261015, integral-models-generators, proof (1)
(blueprint: lem-sfb-lattice-subquotient-filtration). -/
def LatticeSubquotientFiltration (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] {S X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (a : S ⟶ X) [IsImmersion a] : Prop :=
  letI := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u}
    (Padic.coefficientExtensionIntegers ℓ E))
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  let B := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  letI : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  letI : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  LatticeSubquotientFiltrationData A B c a

/-- A lisse field-coefficient sheaf has stratified integral lattices whose rationalized
extensions are the successive quotients of its extension by zero. Ranks may vary and
filtration inclusions need not be strict, including for empty strata or zero sheaves.

Source: blueprint main-20261015, integral-models-generators, proof (1)
(blueprint: lem-sfb-lattice-subquotient-filtration).

Proof plan:
1. Finite type over a field gives Noetherian S and X (pqf-lem-locnoeth-lft).
Apply sk-lem-stratified-lattice to L to obtain finitely many lisse integral lattices;
no global lattice or constant-rank hypothesis is needed.
2. Identify the pulled condensed coefficient rings and inclusion with continuous-function
coefficients by lem-sfb-continuous-ring-universe-realization. Then
lem-sfb-integral-rationalization-exact gives exactness of ordinary rationalization on
all module sheaves. sk-def-sfb-coefficient-change and sk-def-sfb-derived-categories
identify derived rationalization with the termwise exact functor.
3. Use det-lem-coefficient-heart-common-stratification to refine and order the strata
with open prefixes. Restrict the lattices using sk-prop-sfb-cartesian-coefficients;
exact pullback preserves their inclusions and local bases. The pullback comparison of
det-prop-scalar-six-pullback identifies their rationalizations with the restrictions of L.
4. The characterization in sk-lem-coefficient-heart makes L constructible. Apply
det-lem-coefficient-heart-filtration on S to obtain its subobject filtration by the
open-prefix extension counits, with quotients the extensions of its lisse restrictions.
5. Apply exact locally closed extension along a. The exactness and composition comparison
of lem-sfb-locally-closed-extension-coherence preserve the filtration and identify each
quotient with extension along the composite immersion R.immersion b followed by a.
6. det-prop-scalar-six-pullback commutes scalar change with this extension. Step 2
identifies both derived scalar changes with ordinary ones; degree-zero cohomology
therefore identifies the quotient with rationalization of the integral extension.
sk-def-sfb-module-lower-shriek and sk-lem-coefficient-heart identify this extension
with the recorded i_* u_!. Empty S permits n = 0. Empty strata and rank zero give
repeated filtration terms and zero quotients, which the non-strict inequalities allow. -/
theorem exists_latticeSubquotientFiltration (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S X : Scheme.{u}) [S.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (a : S ⟶ X) [a.IsOver (Spec (.of k))] [IsImmersion a] :
    LatticeSubquotientFiltration ℓ E k a := by
  sorry

end AlgebraicGeometry.ProEtale
