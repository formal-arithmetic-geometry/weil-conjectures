module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.RingTheory.FormallySmoothAdic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FormallySmoothAdicCompleteSourceTarget
import WeilConjectures.RingTheory.FormallySmoothCompleteLocalRegular
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.NormalOfFlatNormalFibers

/-!
# A normal power-series cover of an adically formally smooth local algebra

Source: EGA IV4, proof of Theorem 21.14.1, first paragraph, with the completed-tensor-square
repair of the coefficient-normality step recorded in the DAG proof.
(blueprint: lem-sfb-formally-smooth-normal-power-series-cover)
-/

@[expose] public section

universe u v

namespace Algebra

/-- An adically formally smooth Noetherian local algebra with finite residue extension over an
analytically normal local ring admits a faithfully flat local cover by finitely many power-series
variables over a complete Noetherian normal local domain. The extension of the coefficient maximal
ideal contracts to the extension of the original base maximal ideal.

Source: EGA IV4, proof of Theorem 21.14.1, first paragraph; EGA 0_IV 19.3.6, 19.6.4,
19.7.1.5 and IV 7.5.1, 7.5.3, 6.5.4(ii), with the DAG's completed-tensor-square repair.
(blueprint: lem-sfb-formally-smooth-normal-power-series-cover)

Proof:
1. Complete A and B. The completion-local-ring, completion-Noetherian and module-completion
   theorems give complete Noetherian local rings with the same residue fields. The induced map
   is local and adically formally smooth by lem-weil-pbc-fs-adic-complete-source-target.
   The map from B to its completion R is faithfully flat by
   lem-weil-pbc-local-completion-faithfully-flat.
2. Apply lem-weil-pbc-formally-smooth-complete-local-regular to the completed map. Its fibres
   are geometrically regular, hence regular, hence normal by lem-weil-pbc-regular-ring-normal.
   By lem-weil-pbc-flat-normal-fibres-noetherian-normal, R is normal since completed A is normal.
   A normal local ring is a normal domain. Set C = R.
3. By lem-sfb-formally-smooth-completed-local-tensor-square, the completion E of the tensor
   square of R over completed A at the diagonal residue point has faithfully flat local maps
   j1, j2 from R, both adically formally smooth and inducing the identity on the residue field.
   Multiplication gives a retraction mu of both. Use j2 for the C-algebra structure.
4. Choose representatives x1, ..., xd of a residue-field basis of ker(mu)/m_E ker(mu),
   allowing d = 0. By lem-sfb-split-local-power-series-section-criterion there is a local
   continuous C-algebra map phi from S = C[[T1, ..., Td]] to E, sending the variables to these
   representatives, inducing surjections phi_n modulo each positive power of the maximal ideals.
5. The kernel K of phi_n is contained in the maximal ideal of S/m_S^n and satisfies K^n = 0.
   Adic formal smoothness of j2 successively lifts E to the quotients by K^t, for t = 1, ..., n.
   Each successive kernel is square zero. All lifts are local because they preserve residues,
   hence kill m_E^n; they give sections of phi_n. For n = 1 use the residue identity.
   The section criterion now makes phi a C-algebra isomorphism. Take D = S and
   iota = phi.symm composed with j1 and B to R.
6. Apply regularity and ascent of normality once more to j2 to show E is normal, hence a
   normal domain. Transport along phi to obtain the same properties for D. Locality and faithful
   flatness of iota follow by composition and invariance under isomorphism.
7. Put J = j2(m_C)E. The completed-tensor-square lemma says R/m_A R to E/J is faithfully flat,
   hence injective by lem-weil-pbc-faithfully-flat-ideal-contraction. Thus j1 contracts J to
   m_A R. Applying the same contraction theorem to B to R contracts this ideal to m_A B.
   The C-algebra isomorphism phi identifies m_C D with J, giving the asserted contraction.
   The construction retains the stated dimension and primality hypotheses even though this
   argument does not need them separately. -/
theorem exists_normal_powerSeries_cover_of_formallySmoothAdic
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hfs : FormallySmoothAdic A B (IsLocalRing.maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B)
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hp : ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).IsPrime) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsLocalRing C),
      IsNoetherianRing C ∧ IsDomain C ∧ IsIntegrallyClosed C ∧
      IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
      ∃ (d : ℕ) (_ : Algebra B (MvPowerSeries (Fin d) C)),
        Module.FaithfullyFlat B (MvPowerSeries (Fin d) C) ∧
        IsLocalHom (algebraMap B (MvPowerSeries (Fin d) C)) ∧
        IsNoetherianRing (MvPowerSeries (Fin d) C) ∧
        IsDomain (MvPowerSeries (Fin d) C) ∧
        IsIntegrallyClosed (MvPowerSeries (Fin d) C) ∧
        ((IsLocalRing.maximalIdeal C).map (MvPowerSeries.C (σ := Fin d))).comap
            (algebraMap B (MvPowerSeries (Fin d) C)) =
          (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  sorry

end Algebra
