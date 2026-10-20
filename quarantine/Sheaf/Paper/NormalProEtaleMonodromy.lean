/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Sheaf.Paper.GaloisLisseRepresentations
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.LisseCompletedSystemComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.Paper.EtaleLocalMonodromyRealization
import Sheaf.Paper.LatticeSheafLocallyConstant
import Sheaf.SecPurity.NormalLocallyConstantFiniteSection
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence

/-!
# Normal pro-etale monodromy

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Section 7.4,
Lemmas 7.4.7 and 7.4.10, with integral normalization from Proposition 6.8.4
(blueprint: lem-a1-normal-proetale-monodromy).

The bundled monodromy point records the connected, quasi-compact, quasi-separated,
topologically Noetherian base, the geometric point, and its profinite fundamental-group
model. The realization data below records the lisse rational-module equivalence and the
simultaneous finite-level normalization for every invariant lattice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/--
A normalized monodromy equivalence on a normal base. Its functor realizes jointly
continuous finite-dimensional representations as lisse modules over the continuous
rational coefficient sheaf. The finite-level and inverse-limit lattice data are the
`SfLatticeNormalization` records, and `naturality` requires their compatibility on
lattice-preserving equivariant maps.

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6) and Lemmas 7.4.7, 7.4.10
(blueprint: lem-a1-normal-proetale-monodromy).
-/
structure NormalProEtaleMonodromy (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X : Scheme.{u}}
    (p : SfMonodromyPoint X) where
  finiteCorrespondence : GaloisLisseFiniteCorrespondence p.point p.group
  functor : SfContinuousRepresentations l E p ⥤ SfRationalModules l E X
  fullyFaithful : functor.FullyFaithful
  additive : functor.Additive
  linear : ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W) (a : E)
      (U : X.ProEtᵒᵖ) (x : (functor.obj V).val.obj U),
    (functor.map (a • f)).val.app U x =
      ProEtale.lisseFieldConstantSized l E X U a • (functor.map f).val.app U x
  lisse : ∀ V, (functor.obj V).IsFiniteLocallyFree
  normalization : ∀ (V : SfContinuousRepresentations l E p)
      (B : SfInvariantLattice l E V),
    SfLatticeNormalization l E p finiteCorrespondence functor V B
  naturality : ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W)
      (B : SfInvariantLattice l E V) (C : SfInvariantLattice l E W)
      (h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule),
    Nonempty (SfNormalizationMap l E f B C h (normalization V B) (normalization W C))
  equivalence : ObjectProperty.FullSubcategory
      (fun F : SfRationalModules l E X => F.IsFiniteLocallyFree) ≌
      SfContinuousRepresentations l E p
  equivalence_realization : Nonempty
    (equivalence.inverse ⋙ ObjectProperty.ι _ ≅ functor)

/--
On a connected locally Noetherian separated normal scheme, the normalized pro-etale
monodromy equivalence exists. The `SfMonodromyPoint` parameter is the bundled form of
the chosen geometric point and its profinite etale fundamental group; its fields record
nonemptiness, connectedness, quasi-compactness, quasi-separatedness, and topological
Noetherianity. Normality is stated stalkwise as the integral-domain and integrally-closed
condition. Rank zero is included by the finite-free and lisse predicates.

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Section 7.4,
Lemmas 7.4.7 and 7.4.10, and Proposition 6.8.4(1),(4),(6)
(blueprint: lem-a1-normal-proetale-monodromy).

Proof plan: identify completed and continuous-function coefficients; use the
fully faithful etale-local monodromy realization; construct the locally constant
lattice-class sheaf and obtain a finite-etale section from normality; descend an
integral lattice; reconstruct its finite-level fibres and inverse limit; prove the
resulting integral fibre finite free and continuously acted on; then use the normalized
finite-level comparison for essential surjectivity. The quasi-inverse is obtained from
full faithfulness, and all constructions include the zero representation.
-/
theorem normal_proEtale_monodromy (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [X.IsSeparated]
    (p : SfMonodromyPoint X)
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty (NormalProEtaleMonodromy l E p) := by
  sorry

end AlgebraicGeometry.Scheme
