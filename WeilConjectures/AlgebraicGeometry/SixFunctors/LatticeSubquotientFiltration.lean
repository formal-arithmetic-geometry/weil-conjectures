/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedOrderedFiltration
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedSpectralLattices
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLocallyClosedScalarExtension

/-!
# Integral lattice subquotients of a lisse extension by zero

The assertion uses the actual condensed continuous coefficient rings, pulled back from
Profinite, and their internal module objects. Its lattices rationalize along their own
inclusions. Filtration terms are subobjects of the specified locally closed extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The subobject and lattice clauses over specified pulled-back coefficient rings.
This predicate records exactly the conclusion, without introducing any new sheaf notion. -/
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
`i_* u_!` through the scheme-theoretic closure, for both integral and field coefficients. -/
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

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriek

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Compose quotient comparisons over abstract coefficients to keep their structures shared.
private theorem lattice_filtration_assembly
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S))
    (R : S.FiniteLocallyClosedStratification)
    (ho : ∀ b : Fin (R.n + 1),
      IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i))
    (M : ∀ b : Fin R.n,
      Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
        (condensedRingObj A (R.domain b)))
    (he : ∀ b : Fin R.n, Nonempty
      ((Mod.extendScalars ((upperStarFromPoint (R.domain b)).map c)).obj (M b) ≅
        (CondensedRing.upperStar B (R.immersion b)).obj L)) :
    ∃ F : Fin (R.n + 1) →
        Subobject ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L),
      F 0 = ⊥ ∧ F (Fin.last R.n) = ⊤ ∧
      ∃ h : ∀ b : Fin R.n, F b.castSucc ≤ F b.succ,
        ∀ b : Fin R.n,
          letI : IsImmersion (R.immersion b) := R.isImmersion b
          Nonempty (cokernel (Subobject.ofLE (F b.castSucc) (F b.succ) (h b)) ≅
            (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
              ((coefficientHeartLocallyClosedExtension A (R.immersion b ≫ a)
                inferInstance).obj (M b))) := by
  obtain ⟨F, h0, hn, h, hq⟩ := exists_locallyClosedOrderedFiltration B a L R ho
  refine ⟨F, h0, hn, h, fun b ↦ ?_⟩
  have : IsImmersion (R.immersion b) := R.isImmersion b
  obtain ⟨e₀⟩ := hq b
  obtain ⟨e₁⟩ := he b
  obtain ⟨e₂⟩ := condensedLocallyClosedExtension_scalar A B c (R.immersion b ≫ a) (M b)
  exact ⟨e₀ ≪≫
    (coefficientHeartLocallyClosedExtension B (R.immersion b ≫ a) inferInstance).mapIso
      e₁.symm ≪≫ e₂⟩

private theorem lattice_filtration_from_lattices
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (hlat :
  ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S),
    IsLisseCoefficientModule B L →
    ∃ R : S.FiniteLocallyClosedStratification,
      (∀ b : Fin (R.n + 1),
        IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) ∧
      ∃ M : ∀ b : Fin R.n,
        Mod (Sheaf (Scheme.ProEt.topology (R.domain b)) Ab.{u + 1})
          (condensedRingObj A (R.domain b)),
        ∀ b : Fin R.n, IsLisseCoefficientModule A (M b) ∧
          ∃ ι : M b ⟶ (Mod.comap ((upperStarFromPoint (R.domain b)).map c)).obj
              ((CondensedRing.upperStar B (R.immersion b)).obj L),
            Mono ι ∧ IsIso
              (((Mod.extendRestrictAdjunction ((upperStarFromPoint (R.domain b)).map c)).homEquiv
                (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)) :
    LatticeSubquotientFiltrationData A B c a := by
  unfold LatticeSubquotientFiltrationData
  intro L hL
  obtain ⟨R, ho, M, hM⟩ := hlat L hL
  refine ⟨R, ho, M, hM, ?_⟩
  apply lattice_filtration_assembly A B c a L R ho M
  intro b
  obtain ⟨_, ι, _, hi⟩ := hM b
  have := hi
  exact ⟨asIso (((Mod.extendRestrictAdjunction
    ((upperStarFromPoint (R.domain b)).map c)).homEquiv
      (M b) ((CondensedRing.upperStar B (R.immersion b)).obj L)).symm ι)⟩

/-- A lisse field-coefficient sheaf has stratified integral lattices whose rationalized
extensions are the successive quotients of its extension by zero. Ranks may vary and
filtration inclusions need not be strict, including for empty strata or zero sheaves.

Proof. Choose ordered integral lattice inclusions by `exists_orderedSpectralLattices`.
The general ordered filtration theorem constructs actual subobjects of a_! L by pushing
forward the open-prefix filtration. For each stratum the invertible lattice adjoint
identifies its rational restriction with the scalar extension of its integral lattice.
Map this isomorphism through extension by zero and compose with the ordinary
scalar/locally-closed-extension comparison. The resulting cokernel is exactly the
rationalization of the integral extension along the composite stratum immersion.
Finite type over k supplies Noetherian S and X. Empty sources, empty strata and rank zero
allow repeated terms and zero quotients, as the non-strict inequalities require. -/
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
  have hlat := exists_orderedSpectralLattices ℓ E p k _hpℓ S
  let := spectralNorm.nontriviallyNormedField ℚ_[ℓ] E
  let A := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E))
  let B := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
  let c := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)
  have : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E))
      (fun U (a b : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionIntegers ℓ E)) ↦
        mul_comm a b)
  have : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E)
      (fun U (a b : ULift.{u + 1} C(U.unop, E)) ↦ mul_comm a b)
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have : IsNoetherian S :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k)) }
  have result := @lattice_filtration_from_lattices _ _ _ _ _ _ _ _ S X
    inferInstance inferInstance a inferInstance hlat
  exact result

end AlgebraicGeometry.ProEtale
