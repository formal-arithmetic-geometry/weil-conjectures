/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcQbarCategory
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import Sheaf.Paper.PurLisseMorphismRigidity
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.Paper.IntegralConstructibleReductionFibres
import Sheaf.Paper.IntrinsicQbarCategory

/-! # Closed support of a constructible rational adic section

Source: Bhatt--Scholze, Section 6.8, Definitions 6.8.6 and 6.8.10,
Propositions 6.8.4(1), 6.8.11 and 6.8.14
(blueprint: lem-a1-adic-section-closed-support).

The support is characterized simultaneously at every geometric point. The same
closed subset works after finite scalar extension and inclusion into the common-stage
category. The restriction functors below only install the already derived
invertibility of the coefficient prime; they impose no additional hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (T : Scheme.{u}) [T.Over (Spec (.of D.k))]

/-- Restriction of the recorded rational completed pullback to an open subscheme.
Source: BS 6.8.14 and Remark 6.8.15 (blueprint: lem-a1-adic-section-closed-support). -/
def a1RationalOpenRestriction (U : T.Opens) :
    sfRationalConstructibleCategory l E T ⥤ sfRationalConstructibleCategory l E U.toScheme := by
  letI := smoothQbarResidueInvertible D l hl T
  letI := smoothQbarResidueInvertible D l hl U.toScheme
  exact rationalDerivedPullback l E U.ι

/-- A closed subset characterized by the nonzero geometric fibre maps of the section,
with zero restriction on its open complement. Quantification over every lift expresses
independence of the geometric point over a given underlying point.
Source: BS 6.8.4, 6.8.11 and 6.8.14 (blueprint: lem-a1-adic-section-closed-support). -/
def A1RationalSectionSupport
    {A M : sfRationalConstructibleCategory l E T} (t : A ⟶ M) (S : Set T) : Prop :=
  IsClosed S ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
      (sfAdicRationalFiber l E T x).map t ≠ 0 ↔ (SpecToEquivOfField Ω T x).1 ∈ S) ∧
    ∀ (U : T.Opens), (U : Set T) = Sᶜ →
      (a1RationalOpenRestriction D l hl E T U).map t = 0

variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The same recorded completed restriction after coherent common-stage descent.
Source: BS 6.8.14 and Remark 6.8.15 (blueprint: lem-a1-adic-section-closed-support). -/
def a1CommonOpenRestriction (U : T.Opens) :
    generalAlgebraicallyClosedConstructibleCategory l Qbar T ⥤
      generalAlgebraicallyClosedConstructibleCategory l Qbar U.toScheme := by
  letI := smoothQbarResidueInvertible D l hl T
  letI := smoothQbarResidueInvertible D l hl U.toScheme
  exact commonStageDerivedPullback l Qbar U.ι

/-- The common-stage version of the same support characterization and zero restriction.
Every fibre functor is required to have the recorded finite-stage tensor normalization;
no arbitrary unnormalized functor or choice of a mere nonempty object is used.
Source: BS 6.8.14 (blueprint: lem-a1-adic-section-closed-support). -/
def A1CommonSectionSupport
    {A M : generalAlgebraicallyClosedConstructibleCategory l Qbar T}
    (t : A ⟶ M) (S : Set T) : Prop :=
  IsClosed S ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
      (F : generalAlgebraicallyClosedConstructibleCategory l Qbar T ⥤
        ModuleCat.{max (u + 1) v} Qbar),
      SfAdicCommonFiberSpec l T x Qbar F →
        (F.map t ≠ 0 ↔ (SpecToEquivOfField Ω T x).1 ∈ S)) ∧
    ∀ (U : T.Opens), (U : Set T) = Sᶜ →
      (a1CommonOpenRestriction D l hl T Qbar U).map t = 0

variable [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
  [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]

/-- A section of a constructible rational adic sheaf has closed nonzero-fibre support,
independent of geometric lifts, and restricts to zero off that support. These assertions
use the same closed subset after finite coefficient extension and common-stage inclusion;
they also hold for every common-stage heart object and every common-stage section.
Finite fields inside Qbar use their recorded small coefficient models, so every finite
extension in the specified closure is included.
Source: BS 6.8.4(1), Definitions 6.8.6 and 6.8.10, Propositions 6.8.11 and 6.8.14
(blueprint: lem-a1-adic-section-closed-support).

Proof:
1. Use prop-weil-localized-tstructure to represent M by an integral heart object F.
By def-weil-pbc-rational-category clear one common uniformizer denominator from t,
obtaining an integral section u. The denominator and representing isomorphism do not
change zero or nonzero of any rational fibre map.
2. Apply lem-a1-integral-constructible-reduction-fibres to F and u. Its ordinary
quotients have compatible constructible etale origins G_n on one finite lisse
stratification; their inverse-limit germs a_x rationalize to the fibres of u.
Refine the strata into finitely many connected components using
lem-sfb-noetherian-connected-components-open. Integral torsion is allowed.
3. For every m and positive n, lem-sc-etale-section-zero-open shows that the locus
C_(m,n) where the germ of varpi^m u modulo varpi^n is nonzero is closed.
By lem-pur-lisse-morphism-rigidity it is a union of entire connected strata.
4. For fixed m these loci increase with n. There are only finitely many strata,
so the union is one C_(m,N_m), hence closed. It is the locus A_m where varpi^m a_x
is nonzero in the inverse limit, since a limit element vanishes iff every coordinate does.
This uses the finite stratification, not stabilization of arbitrary closed chains.
5. The localization equality criterion gives a_x/1 = 0 iff some varpi^m a_x = 0.
Thus S(t) is the intersection of the closed A_m and is closed, including torsion cases.
6. The natural fibre comparison of lem-per-adic-heart-pullback-fibres makes the
characterization independent of lifts. On the complement every fibre of the restricted
map is zero. Exactness makes its image have zero fibres; joint conservativity makes
that image zero, so the restricted map is zero. The complement remains finite type.
7. Finite coefficient extension identifies the fibre maps with tensor extension.
Extension to a field preserves and reflects zero maps, so S and its zero restriction
are preserved. By def-weil-pbc-qbar-category a common-stage object and section descend
to one finite stage in the heart. Apply the finite-stage result there and extend its
fibres to Qbar; the same detection of zero gives independence of the representative.
-/
theorem adicSectionClosedSupport :
    (∀ (L : Padic.FiniteCoefficientFields l Qbar)
      (M : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) T)
      (t : rationalCohomologyCoefficient D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) T ⟶ M.obj),
      ∃ S : Set T,
        A1RationalSectionSupport D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) T t S ∧
        (∀ (N : Padic.FiniteCoefficientFields l Qbar) (h : L ≤ N),
          A1RationalSectionSupport D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar N) T
            ((GeneralAlgebraicallyClosedCoefficients.transition l Qbar T L N h).map t) S) ∧
        A1CommonSectionSupport D l hl T Qbar
          ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := T) L).map t) S) ∧
    ∀ (L : Padic.FiniteCoefficientFields l Qbar) (M : sfCommonStageHeart l T Qbar)
      (t : (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := T) L).obj
        (rationalCohomologyCoefficient D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) T) ⟶ M.obj),
      ∃ S : Set T, A1CommonSectionSupport D l hl T Qbar t S := by
  sorry

end WeilConjectures
