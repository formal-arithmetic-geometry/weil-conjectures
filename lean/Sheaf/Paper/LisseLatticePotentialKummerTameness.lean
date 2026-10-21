/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import Sheaf.Paper.GaloisLisseRepresentations
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Sheaf.Paper.CartesianCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.TotallyDisconnectedCoefficientRealization
import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison

/-!
# Potential Kummer tameness of lisse lattices

Source: Bhatt--Scholze, Proposition 6.8.4(1), and ILO, Expose IX, Proposition 2.1,
printed pp. 133--134. This is the residual-cover consequence recorded in
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Bundle the recorded continuous-map ring for the recorded valuation ring, with its
subspace topology. Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
def latticeIntegralCondensedRing : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  { X := Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers ℓ E)
    mon := Profinite.continuousMapRingObjOfUniverseMonObj _ }

/-- The recorded pointwise multiplication on integral coefficients is commutative.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
instance latticeIntegralCondensedRing_comm : IsCommMonObj (latticeIntegralCondensedRing ℓ E).X :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse _

/-- The canonical point pullback preserves commutativity of integral coefficients.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
instance latticeIntegralCoefficient_comm (X : Scheme.{u}) :
    IsCommMonObj ((upperStarFromPoint X).mapMon.obj (latticeIntegralCondensedRing ℓ E)).X :=
  inferInstanceAs (IsCommMonObj (condensedRingObj (latticeIntegralCondensedRing ℓ E).X X))

/-- The recorded quotient by the chosen uniformizer, with quotient topology, as a
continuous-map condensed ring. Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
def latticeResidualCondensedRing : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  { X := Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionRing ℓ E 1)
    mon := Profinite.continuousMapRingObjOfUniverseMonObj _ }

/-- Residual continuous coefficients have their recorded commutative multiplication.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
instance latticeResidualCondensedRing_comm : IsCommMonObj (latticeResidualCondensedRing ℓ E).X :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse _

/-- The actual condensed reduction map is postcomposition by the quotient homomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
def latticeResidualCondensedMap :
    latticeIntegralCondensedRing ℓ E ⟶ latticeResidualCondensedRing ℓ E where
  hom := Profinite.continuousMapRingObjMapOfUniverse
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ E 1)) continuous_quot_mk
  isMonHom_hom := Profinite.isMonHom_continuousMapRingObjMapOfUniverse _ _

/-- The actual rational coefficient map is postcomposition by the valuation-ring inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
def latticeRationalCondensedMap : latticeIntegralCondensedRing ℓ E ⟶ normContinuousRing E where
  hom := Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val
  isMonHom_hom := Profinite.isMonHom_continuousMapRingObjMapOfUniverse _ _

/-- The actual residual module M_0/varpi M_0, expressed by ordinary internal scalar
extension along the canonical quotient map pulled back from the point.
Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
abbrev latticeResidualModule (X : Scheme.{u})
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeIntegralCondensedRing ℓ E).X X)) :=
  (Mod.extendScalars
    (((upperStarFromPoint X).mapMon.map (latticeResidualCondensedMap ℓ E)).hom)).obj M₀

/-- The rationalization A_E tensor_{A_O_E} M_0 uses the canonical inclusion, with
ordinary internal extension of scalars. Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness). -/
abbrev latticeRationalModule (X : Scheme.{u})
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeIntegralCondensedRing ℓ E).X X)) :=
  (Mod.extendScalars
    (((upperStarFromPoint X).mapMon.map (latticeRationalCondensedMap ℓ E)).hom)).obj M₀

/-- One connected finite etale residual cover makes the rationalized lattice Kummer tame
for every regular SNC boundary pair mapping through it.
Source: Bhatt--Scholze, Proposition 6.8.4(1), and ILO IX, Proposition 2.1, pp. 133--134
(blueprint: lem-sfb-lisse-lattice-potential-kummer-tameness).

Proof (the eight steps of the DAG):
1. Use lem-weil-pbc-continuous-coefficient-realizations and the internal-module equivalence
of def-weil-pbc-internal-abelian-sheaf-module-equivalence. The reduction equivalence
lem-sfb-integral-lisse-reduction-equivalence gives compatible finite free reductions.
By det-pe-finite-local-systems-twist these finite local systems have etale models.
2. Apply lem-weil-pbc-finite-set-monodromy-torsor to the first reduction. The module
correspondence cor-galois-lisse-representations makes its trivialization module-linear.
Its fibre is finite free of rank d, including d = 0. Choose this cover once and for all.
3. Fix Y,D,g and arbitrary strict-local boundary parameters. The strict henselization is
Noetherian regular by lem-sc-strict-henselization-noetherian and
lem-sc-strict-henselization-regular. Its puncture is nonempty integral, by
lem-trf-regular-local-ufd-boundary-factorization. Cartesian coefficient pullback
(sk-prop-sfb-cartesian-coefficients) preserves the actual reductions and residual basis.
4. Filter the kernel of GL_d(O_E/varpi^n) -> GL_d(O_E/varpi) by congruence powers.
Successive quotients are additive matrix groups over the finite residue field of
characteristic ell, hence the kernel is an ell-group. Use
lem-weil-valued-dvr-finite-quotients and lem-weil-l-adic-extension-integers-dvr.
5. By det-pe-finite-local-systems-twist, cor-galois-lisse-representations and
thm-galois-fundamental the actual image of finite-level monodromy gives a torsor
trivializing that reduction. Its order is an ell-power and thus prime to p.
6. Apply lem-sfb-strict-local-prime-to-p-kummer-splitting separately at every level.
Each finite root cover is dominated by the full root tower. Pulling back a section of
the torsor trivializes the actual reduction on that tower; use Cartesian exactness.
7. Choose compatible bases inductively: the discrepancy between two residual bases is
a locally constant GL_d-valued function, by lem-sfb-totally-disconnected-coefficient-realization.
Every matrix lifts across consecutive quotient rings: lift entries and test the determinant
modulo the maximal ideal. A finite set-theoretic section is continuous. Adjust the next basis.
8. Full faithfulness of lem-sfb-integral-lisse-reduction-equivalence on the tower itself
reconstructs the free integral module. Rationalize using
 def-sfb-condensed-pullback-tensor-comparison and sk-prop-sfb-cartesian-coefficients,
then return through the coefficient realizations. This works for every parameter choice;
rank zero and the empty boundary tuple give the zero module and identity tower. -/
theorem lisseLattice_potential_kummer_tame
    (p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]
    (S : Scheme.{u}) [S.Over (Spec (.of k))] [ConnectedSpace S]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (latticeIntegralCondensedRing ℓ E).X S))
    (_hM₀ : IsLisseCoefficientModule (latticeIntegralCondensedRing ℓ E).X M₀) :
    ∃ (H : Scheme.{u}) (c : H ⟶ S), ConnectedSpace H ∧ IsFinite c ∧ Etale c ∧ Surjective c ∧
      Mod.IsFree (condensedRingObj (latticeResidualCondensedRing ℓ E).X H)
        ((CondensedRing.upperStar (latticeResidualCondensedRing ℓ E).X c).obj
          (latticeResidualModule ℓ E S M₀)) ∧
      ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))],
        LocallyOfFiniteType (Y ↘ Spec (.of k)) → QuasiCompact (Y ↘ Spec (.of k)) →
        IsSeparated (Y ↘ Spec (.of k)) → IsRegularScheme Y →
        ∀ (D : Y.IdealSheafData), IsStrictNormalCrossingsBoundary D →
          ∀ (W : Scheme.{u}) (w : W ⟶ Y), IsOpenImmersion w →
            Set.range w = (D.support : Set Y)ᶜ →
            ∀ (g : W ⟶ S), (∃ h : W ⟶ H, h ≫ c = g) →
              IsStrictLocalKummerTameModule p (normContinuousRing E).X D w
                ((CondensedRing.upperStar (normContinuousRing E).X g).obj
                  (latticeRationalModule ℓ E S M₀)) := by
  sorry

end AlgebraicGeometry.ProEtale
