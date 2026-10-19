/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.AdicLisseCohomologyCalculus
public import Sheaf.SixFunctors.ArbitraryFieldVerdier
public import Mathlib.Topology.KrullDimension

import Sheaf.RingTheory.ExcellentRing
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.PbcRationalCategory
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.RingTheory.FieldsExcellent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.AdicClosedConstructible
import Sheaf.Paper.AdicExceptionalProjection
import Sheaf.Paper.FiniteRegularReductionDualizing
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Generic lisse local form of the relative dualizing complex

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; Illusie--Laszlo--Orgogozo,
Exposé XVII, Proposition 6.2.2.1 (blueprint: lem-per-qbar-generic-duality-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits Topology Set Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PerAdic
open AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.Scheme.PerAdic

/-- Source: scheme separation conventions (blueprint: lem-per-qbar-generic-duality-model).
A separated morphism to the separated point `Spec k` gives an absolutely
   separated scheme.  The recorded `Base` structure stores the relative
   separatedness, while the lisse and Verdier interfaces ask for this derived
   scheme instance. -/
instance baseSchemeSeparated {k : Type u} [Field k] (W : Base.{u} k) :
    W.scheme.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from (W.scheme ↘ Spec (.of k)),
    IsSeparated.comp_iff]
  infer_instance

/-- Constant rank in addition to whole-component lissity. The fibres are the calculus'
completed adic geometric fibres, transported along its normalized comparison.
Source: Bhatt--Scholze 6.8.4 (blueprint: lem-per-qbar-generic-duality-model). -/
def genericModelConstantRank (l : ℕ) [Fact l.Prime]
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] {k : Type u} [Field k]
    (W : Base.{u} k) [Fact (IsUnit (l : k))]
    (C : AdicLisseCohomologyCalculus l Qbar W.scheme)
    (K : intrinsicPbcQbarCategory l Qbar W.scheme) (n : ℕ) : Prop :=
  HasCommonStageLisseLattice l Qbar W.scheme K ∧
    ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ W.scheme),
      Module.finrank Qbar ((C.fiber κ x).obj (C.comparison.inverse.obj K)) = n

/-- Adic cohomology in the intrinsic coefficient presentation. The calculus fixes it on
all integral representatives by the standard integral cohomology comparison; hence it
is the standard cohomology of the recorded heart, transported by the recorded equivalence.
Source: Bhatt--Scholze 6.8.11, 6.8.14 (blueprint: lem-per-qbar-generic-duality-model). -/
def genericModelCohomology (l : ℕ) [Fact l.Prime]
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] {k : Type u} [Field k]
    (W : Base.{u} k) [Fact (IsUnit (l : k))]
    (C : AdicLisseCohomologyCalculus l Qbar W.scheme) (r : ℤ) :
    intrinsicPbcQbarCategory l Qbar W.scheme ⥤ intrinsicPbcQbarCategory l Qbar W.scheme :=
  C.comparison.inverse ⋙ C.cohomology r ⋙ C.comparison.functor

/-- The actual adic linear dual tensored with the rank-one lisse coefficient sheaf.
Source: Bhatt--Scholze 6.8.15 (blueprint: lem-per-qbar-generic-duality-model). -/
def genericModelDualTensor (l : ℕ) [Fact l.Prime]
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] {k : Type u} [Field k]
    (W : Base.{u} k) [Fact (IsUnit (l : k))]
    (C : AdicLisseCohomologyCalculus l Qbar W.scheme)
    (M O : LisseAlgebraicSheaf l W.scheme Qbar) :
    intrinsicPbcQbarCategory l Qbar W.scheme :=
  C.comparison.functor.obj ((adicCalculusTensor l Qbar W.scheme C.comparison).obj
    (C.realization.obj (C.dual.obj (op M)), C.realization.obj O))

/-- Duality for every bounded complex with whole-component lisse cohomology. Its premise
places no constant-rank or stratification restriction on that complex. The represented
sheaf M is precisely the cohomology in degree -r-2d, not in degree r.
Source: Bhatt--Scholze 6.8.15 (blueprint: lem-per-qbar-generic-duality-model). -/
def genericDualityClause {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
    (Qbar : Type (u + 1)) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar] (W : Base.{u} k) (hl : IsUnit (l : k))
    [Fact (IsUnit (l : k))]
    (C : AdicLisseCohomologyCalculus l Qbar W.scheme)
    (B : ArbitraryFieldVerdier.Datum.{u, u + 1} l hl Qbar (𝟙 W.scheme))
    (d : ℕ) (O : LisseAlgebraicSheaf l W.scheme Qbar) : Prop :=
  ∀ L : intrinsicPbcQbarCategory l Qbar W.scheme,
    (∀ r : ℤ, HasCommonStageLisseLattice l Qbar W.scheme
      ((genericModelCohomology l Qbar W C r).obj L)) →
    ∀ r : ℤ, ∃ M : LisseAlgebraicSheaf l W.scheme Qbar,
      Nonempty (((genericModelCohomology l Qbar W C (-r - 2 * (d : ℤ))).obj L) ≅
        C.comparison.functor.obj (C.realization.obj M)) ∧
      Nonempty (((genericModelCohomology l Qbar W C r).obj
        ((B.dualX l hl Qbar).obj (op L))) ≅ genericModelDualTensor l Qbar W C M O) ∧
      HasCommonStageLisseLattice l Qbar W.scheme (genericModelDualTensor l Qbar W C M O) ∧
      (IsZero (genericModelDualTensor l Qbar W C M O) ↔
        IsZero ((genericModelCohomology l Qbar W C (-r - 2 * (d : ℤ))).obj L))

/-- Generic local duality over an arbitrary field, using the actual dualizing object
Ra! of the coefficient unit and its internal-Hom dual. The Verdier datum is taken for
the identity morphism of each component: its X structure adjunction is thus the
identity compact-support functor followed by the component's structure-map functor.
Source: Bhatt--Scholze 6.7.20, 6.8.14--15; ILO Exposé XVII 6.2.2.1
(blueprint: lem-per-qbar-generic-duality-model).
Proof: (1) Noetherianity and finite dimension give finitely many irreducible components.
Remove their pairwise intersections to obtain disjoint neighborhoods of their generic
points. (2) Boundedness and constructibility give finitely many cohomology sheaves and
finite lisse stratifications. Shrink each neighborhood to the stratum of its generic
point. The ranks are constant by irreducibility. (3) Excellence of the base field and
its J-2 property allow a further shrinking on which the reduction is regular; the
local ring at the generic point of a reduced irreducible scheme is a field. No
smoothness or perfectness is needed. (4) The union contains all component generic
points. Appending an ambient component to a chain in the complement proves strict
dimension drop, including the empty-complement case in dimension zero.
(5) Exceptional pullback of the integral coefficient unit has, on this regular
reduction, the normalized rank-one Tate reduction tower, shifted by twice dimension,
by finite regular-reduction duality. (6) The lisse completed-system comparison and
Milnor's epimorphic-tower theorem identify its ordinary inverse limit with its derived
limit. Completeness and uniqueness of derived limits reconstruct the integral
rank-one lisse object shifted by 2d. (7) Rationalize and descend adjunction Hom
bijections to common coefficient stages. Yoneda identifies this object with the
specified Datum.omegaX; hence omega is O[2d]. (8) On a common finite stage and a cover
trivializing the lisse sheaves, evaluation identifies RHom(M,O) with M-dual tensor O.
Internal Hom restriction and the adic lisse calculus descend this to the given category.
(9) Induct on a cohomological amplitude for L using its top truncation triangle.
Contravariant exactness and shift reversal give H^r(RHom(L,O)) equal to the dual of
H^-r(L) tensored with O. The shift 2d gives the displayed -r-2d index.
(10) Fibres of a finite-dimensional vector-space dual tensored with a line vanish
exactly when the original fibre vanishes. Conservativity of the adic geometric fibres
proves the zero-object equivalence; the lisse tensor and dual calculus proves lissity. -/
theorem lem_per_qbar_generic_duality_model
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    [hl : Fact (IsUnit (l : k))] (Qbar : Type (u + 1)) [Field Qbar]
    [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
    (W : Base.{u} k) (hW : Nonempty W.scheme)
    (s : ℕ) (K : Fin s → intrinsicPbcQbarCategory l Qbar W.scheme) :
    ∃ (U : W.scheme.Opens) (t : ℕ) (V : Fin t → Base.{u} k)
      (j : ∀ i, (V i).scheme ⟶ W.scheme) (d : Fin t → ℕ)
      (B : ∀ i, ArbitraryFieldVerdier.Datum.{u, u + 1} l hl.out Qbar (𝟙 (V i).scheme))
      (C : ∀ i, AdicLisseCohomologyCalculus l Qbar (V i).scheme)
      (O : ∀ i, LisseAlgebraicSheaf l (V i).scheme Qbar),
      Dense (U : Set W.scheme) ∧
      (∀ i, Nonempty (V i).scheme) ∧
      (∀ i, IrreducibleSpace (V i).scheme) ∧
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ i, (j i).IsOver (Spec (.of k))) ∧
      (∀ i, Set.range (j i).base ⊆ (U : Set W.scheme)) ∧
      (U : Set W.scheme) = ⋃ i, Set.range (j i).base ∧
      (∀ i₁ i₂, i₁ ≠ i₂ →
        Disjoint (Set.range (j i₁).base) (Set.range (j i₂).base)) ∧
      (∀ x : W.scheme, x ∈ genericPoints W.scheme → x ∈ U) ∧
      topologicalKrullDim (((U : Set W.scheme)ᶜ : Set W.scheme)) <
        topologicalKrullDim W.scheme ∧
      (∀ i, topologicalKrullDim (V i).scheme = (d i : WithBot ℕ∞)) ∧
      (∀ i, Nonempty (ArbitraryFieldVerdier.Properties l hl.out Qbar (B i))) ∧
      (∀ i, genericModelConstantRank l Qbar (V i) (C i)
        ((C i).comparison.functor.obj ((C i).realization.obj (O i))) 1) ∧
      (∀ a r i, ∃ n : ℕ, genericModelConstantRank l Qbar (V i) (C i)
        ((genericModelCohomology l Qbar (V i) (C i) r).obj
          ((ArbitraryFieldVerdier.pull l hl.out Qbar (j i)).obj (K a))) n) ∧
      (∀ i, Nonempty ((B i).omegaX l hl.out Qbar ≅
        ((C i).comparison.functor.obj ((C i).realization.obj (O i)))⟦2 * (d i : ℤ)⟧)) ∧
      (∀ i, genericDualityClause l Qbar (V i) hl.out (C i) (B i) (d i) (O i)) := by
  sorry

end AlgebraicGeometry.Scheme.PerAdic
