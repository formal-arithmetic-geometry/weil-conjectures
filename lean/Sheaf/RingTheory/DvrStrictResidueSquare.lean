module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.IntegralClosureIndEtaleBaseChange

/-!
# Compatible separable residue closures of discrete valuation rings

Source: Stacks Project, More on Algebra, Tag 09ET, with the perfect lower residue
hypothesis for weak-solution descent recorded in the DAG
(blueprint: lem-sfb-dvr-strict-residue-square).
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

universe u v w x y

namespace IsDiscreteValuationRing

/-- A finite weak solution: every upper normalized branch has maximal lower contraction,
both localizations are DVRs, and their extended maximal ideals agree. Here `C` is the
integral closure of `T` in `(H ⊗[F] M) ⧸ nilradical`, and the canonical normalization
map `R = integralClosure D M → C` is the restriction of `m ↦ 1 ⊗ m` followed by reduction
(stated inline, with the same bodies as the 09EM helpers, so that no downstream module is
imported).

Source: Stacks Project, More on Algebra, Tags 09EM and 09EN; the explicit weak-solution
convention of Tag 09ET in the DAG (blueprint: lem-sfb-dvr-strict-residue-square). -/
def IsFiniteWeakSolution
    (D : Type u) (T : Type w) (F : Type v) (H : Type x) (M : Type y)
    [CommRing D] [CommRing T] [Field F] [Field H] [Field M]
    [Algebra D T] [Algebra D F] [Algebra D H] [Algebra T H] [Algebra F H]
    [IsScalarTower D T H] [IsScalarTower D F H]
    [Algebra F M] [Algebra D M] [IsScalarTower D F M] : Prop :=
  let φ : integralClosure D M →+*
      integralClosure T ((H ⊗[F] M) ⧸ nilradical (H ⊗[F] M)) :=
    (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
      Algebra.TensorProduct.includeRight).restrictScalars D |>.comp
        (integralClosure D M).val).codRestrict
          ((integralClosure T ((H ⊗[F] M) ⧸ nilradical (H ⊗[F] M))).restrictScalars D)
          (fun a ↦ (a.property.map
            (((Ideal.Quotient.mkₐ F (nilradical (H ⊗[F] M))).comp
              Algebra.TensorProduct.includeRight).restrictScalars D)).tower_top) |>.toRingHom
  Module.Finite F M ∧
  ∀ (q : Ideal (integralClosure T ((H ⊗[F] M) ⧸ nilradical (H ⊗[F] M)))) [q.IsMaximal],
    (∃ _hn : (q.comap φ).IsMaximal,
      ∃ hdom : IsDomain (Localization.AtPrime (q.comap φ)),
        @IsDiscreteValuationRing (Localization.AtPrime (q.comap φ)) _ hdom) ∧
    (∃ hdom : IsDomain (Localization.AtPrime q),
      @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
    Ideal.map ((algebraMap _ (Localization.AtPrime q)).comp φ) (q.comap φ) =
      Ideal.map (algebraMap _ (Localization.AtPrime q)) q

/-- A compatible square of injective local DVR maps with separable algebraic fraction
extensions and separable-closure residue extensions, preserving the lower maximal ideal.
If the original lower residue is perfect, existence of a finite weak solution upstairs
implies existence of a finite weak solution downstairs.

Source: Stacks Project, More on Algebra, Tag 09ET, statements (1)--(3), with the
perfect-lower-residue correction in the DAG (blueprint: lem-sfb-dvr-strict-residue-square).

Proof:
1. Use lem-weil-pbc-strict-henselization-functoriality to choose compatible separable
   residue closures. The triples construction lem-weil-pbc-strict-henselization-triples
   gives B_s; lem-sfb-local-ind-etale-dvr gives its DVR and fraction-field properties.
2. Apply lem-sfb-local-separable-residue-ind-finite-etale to A and the lower residue
   closure, mapping into B_s. Its colimit A_s is a DVR by lem-sfb-local-ind-etale-dvr,
   with the original uniformizer. Its map to B_s is injective: a nonzero prime kernel
   would contain that uniformizer, whose image under the original injective maps is nonzero.
3. Descend a finite weak solution H/K_s to a finite field extension N/F_i at a finite
   etale local stage A_i. Choose a basis including 1 and a stage containing its finitely
   many multiplication constants. Its F_i-span is a finite-dimensional domain, hence a
   field, and scalar extension recovers H.
4. Apply lem-sfb-integral-closure-ind-etale-base-change and
   lem-sfb-dvr-algebraic-normalization-structure to compare the normalizations at this
   stage. The relative clause of lem-sfb-local-ind-etale-dvr preserves the lower
   uniformizer, so the weak equality descends to A_i mapping into B_s.
5. With the perfect lower residue hypothesis, apply
   lem-sfb-finite-etale-weak-solution-transfer to obtain some finite weak solution N_0/K
   for A mapping into B_s; it need not be the particular field N viewed over K.
6. By lem-sfb-dvr-algebraic-normalization-structure every normalized branch over B
   lifts to one over B_s. Reduced tensor associativity and componentwise integrality
   identify the normalizations in the finite product of generic fields.
7. In the resulting chain of local DVRs write lower and middle uniformizers as unit
   times powers of the next ones using lem-weil-pbc-dvr-unit-times-uniformizer-power.
   Weakness upstairs forces the product of the two positive ramification indices to
   equal 1. The first index is 1, so every branch downstairs is weak as required.
-/
theorem exists_strict_residue_square
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L] :
    ∃ (Aₛ Bₛ : Type (max u v w x))
      (_ : CommRing Aₛ) (_ : IsDomain Aₛ) (_ : IsDiscreteValuationRing Aₛ)
      (_ : CommRing Bₛ) (_ : IsDomain Bₛ) (_ : IsDiscreteValuationRing Bₛ)
      (_ : Algebra A Aₛ) (_ : Algebra B Bₛ) (_ : Algebra Aₛ Bₛ) (_ : Algebra A Bₛ)
      (_ : IsScalarTower A B Bₛ) (_ : IsScalarTower A Aₛ Bₛ)
      (_ : IsLocalHom (algebraMap A Aₛ)) (_ : IsLocalHom (algebraMap B Bₛ))
      (_ : IsLocalHom (algebraMap Aₛ Bₛ)),
      Function.Injective (algebraMap A Aₛ) ∧ Function.Injective (algebraMap B Bₛ) ∧
      Function.Injective (algebraMap Aₛ Bₛ) ∧
      IsSepClosure (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField Aₛ) ∧
      IsSepClosure (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField Bₛ) ∧
      Ideal.map (algebraMap A Aₛ) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal Aₛ ∧
      ∃ (Kₛ Lₛ : Type (max u v w x))
        (_ : Field Kₛ) (_ : Field Lₛ)
        (_ : Algebra Aₛ Kₛ) (_ : IsFractionRing Aₛ Kₛ)
        (_ : Algebra Bₛ Lₛ) (_ : IsFractionRing Bₛ Lₛ)
        (_ : Algebra A Kₛ) (_ : Algebra K Kₛ)
        (_ : IsScalarTower A Aₛ Kₛ) (_ : IsScalarTower A K Kₛ)
        (_ : Algebra B Lₛ) (_ : Algebra L Lₛ)
        (_ : IsScalarTower B Bₛ Lₛ) (_ : IsScalarTower B L Lₛ)
        (_ : Algebra Aₛ Lₛ) (_ : Algebra Kₛ Lₛ)
        (_ : IsScalarTower Aₛ Bₛ Lₛ) (_ : IsScalarTower Aₛ Kₛ Lₛ),
        Algebra.IsSeparable K Kₛ ∧ Algebra.IsSeparable L Lₛ ∧
        (PerfectField (IsLocalRing.ResidueField A) →
          (∃ (H : Type (max u v w x)) (_ : Field H) (_ : Algebra Kₛ H)
            (_ : Algebra Aₛ H) (_ : IsScalarTower Aₛ Kₛ H),
            IsFiniteWeakSolution Aₛ Bₛ Kₛ Lₛ H) →
          ∃ (N : Type (max u v w x)) (_ : Field N) (_ : Algebra K N)
            (_ : Algebra A N) (_ : IsScalarTower A K N),
            IsFiniteWeakSolution A B K L N) := by
  sorry

end IsDiscreteValuationRing
