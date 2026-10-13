module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/--
The arithmetic residue-degree calculation for a finite etale morphism over the generic
point of a Cartier divisor.  This is the local Galois/DVR calculation (Stacks Project,
Tag 09EB): after identifying the normalization stalk with the integral closure of the
DVR stalk, the residue degree divides the degree of the generic Galois algebra, hence
(the latter being a stabilizer quotient) divides the order of the torsor group.
The geometric construction of the root chart is deliberately absent from this lemma;
it is supplied by the caller.
(blueprint: lem-sbc-root-normalization-generic-stalk-residue-degree-dvd-core)
-/
theorem normalization_residue_degree_dvd_core
    {N V P D : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (p : P ⟶ V) [IsFinite p] (a : P ⟶ N) [QuasiCompact a] [QuasiSeparated a]
    (hEtale : Etale p) (hNorm : IsFinite a.fromNormalization)
    (j : D ⟶ N) (hD : IsRegular D) (hDi : IsIntegral D)
    (hj : IsEffectiveCartierCenter j)
    (O : N.Opens)
    (hcomp : ∀ z : N, z ∈ O ↔ z ∉ Set.range j)
    (η : D) (hη : IsGenericPoint η Set.univ)
    (x : a.normalization) (hx : a.fromNormalization x = j η) :
    letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
    Module.finrank (N.residueField (a.fromNormalization x))
      (a.normalization.residueField x) ∣ Nat.card G := by
  sorry

end AlgebraicGeometry.Scheme
