/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.DeligneLaumon.RawHeartAdicLisseData
import Sheaf.Paper.ZlSfPbcNormalizedHeartModel
import Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices
import Sheaf.Paper.ClassicalSystemRawLisseRealization

/-! # Finite classical models on reduced lisse strata

Source: Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Remark 6.8.15;
blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.RawHeartAdic
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- A supplied finite-stage heart object and its continuous constructible realization
have classical lisse models on a finite reduced partition, at that same stage.
This assertion selects strata and their finite models; it asserts no Weil or frontier
extension.

Source: BS 6.8.4(1),(4), 6.8.13, 6.8.14(2), 6.8.15; the finite-model clause of
lem-zl-sf-pbc-normalized-heart-model, lem-zl-continuous-constructible-stratified-lattices,
and lem-zl-classical-system-raw-lisse-realization
(blueprint: lem-zl-raw-heart-adic-strata-bridge).

Proof: Use the supplied finite-stage heart object N and its specified continuous
constructible realization F in degree zero. Apply the stratified-lattice theorem
to its finite lisse-partition witness. It gives a finite reduced refinement and
lisse integral lattices whose localizations are the restrictions of F, all at E.
Give each stratum the structure map induced from X; an immersion into a separated
finite-type scheme over a field is separated finite type. These are the bases
and the base_map equations. The completed-system comparison takes each lattice
to its ordinary finite-free etale quotient tower. Regard that tower as the object
of RawRational with the canonical ULift coefficient identification. The normalized
continuous pullback comparison carries N restricted to the stratum to F there.
The specified lattice-localization isomorphism and the comparison for b identify
the two continuous derived images. Lift this isomorphism through the fully faithful
continuous realization and the identity sf/PBC equivalence, orienting it from the
raw restriction to the classical realization. This is the restriction field of
the conclusion. No common-stage representative is selected here. On the empty
scheme the partition is empty, and zero local ranks use zero towers; no extension
of E or assertion about derived reductions of a torsion representative is needed. -/
theorem raw_heart_adic_strata_bridge
    (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l)
    (b : ClassicalFamily D l hl a c) (S : FdCoefficientComparisonSystem.{u} l Ω)
    (r : ContinuousRational.Family.{u} l)
    (hheart : ∀ Y : PerAdic.Base D.k,
      Nonempty (HeartComparison D l hl Ω a S r Y
        (hDim := baseDimension D l hl Y) (hInv := basePrimeUnit D l hl Y)))
    (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (N : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X.scheme)
    (F : pbcModules X.scheme
      (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω i)))
    (hF : ∃ t : Scheme.FiniteLocallyClosedStratification X.scheme, ∀ j : Fin t.n,
      ((proEtaleModuleInverseImage (t.immersion j)
        (rationalCoefficientSheaf l X.scheme
          (pbcFiniteField.{u} l Ω i))).obj F).IsFiniteLocallyFree)
    (hreal : letI := baseDimension D l hl X
      letI := basePrimeUnit D l hl X
      Nonempty (((r.realization (pbcFiniteField.{u} l Ω i)
      (continuousBase D l hl X)).J.obj
        (((S.coefficients X.scheme).stage i).rational.functor.obj N.obj)) ≅
          (DerivedCategory.singleFunctor _ 0).obj F)) :
    ∃ (partition : Scheme.FiniteLocallyClosedStratification X.scheme),
      (∀ ν : Fin partition.n, IsReduced (partition.domain ν)) ∧
      ∃ (bases : Fin partition.n → PerAdic.Base D.k)
        (domain : ∀ ν : Fin partition.n, (bases ν).scheme = partition.domain ν),
        (∀ ν : Fin partition.n,
          eqToHom (domain ν) ≫ partition.immersion ν ≫ (X.scheme ↘ Spec (.of D.k)) =
            ((bases ν).scheme ↘ Spec (.of D.k))) ∧
        ∃ model : ∀ ν : Fin partition.n, ClassicalStage D l hl Ω (bases ν) i,
          ∀ ν : Fin partition.n,
            Nonempty ((@rationalDerivedPullback l _
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) _ _ _ _ _
              (eqToHom (domain ν) ≫ partition.immersion ν)
              (baseInvertible D l hl (bases ν)) (baseInvertible D l hl X)).obj N.obj ≅
                (b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
                  (bases ν)).realization.obj (model ν)) := by sorry

end WeilConjectures.RawHeartAdic
