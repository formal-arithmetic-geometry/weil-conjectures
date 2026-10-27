/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.Paper.EtaleSystemCofinalData
import Sheaf.CategoryTheory.SystemEvaluationKFlat
import Sheaf.CategoryTheory.SystemSelectedDerivedExtension
import Sheaf.CategoryTheory.SystemOrdinarySelectedExtension
import Sheaf.Paper.SystemBlockRepetition
import Sheaf.Paper.EtaleSystemCoefficientProjection
import Sheaf.CategoryTheory.SystemLevelLeftExtension

/-! # Geometric realization of cofinal support

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The geometric cofinal-extension presentation, before taking a support right mate.
Source: Zheng, Construction 4.1, printed p. 21, and the paragraph preceding Lemma 4.10,
printed p. 23; finite-block form of the coefficient construction
(blueprint: lem-pur-etale-cofinal-support-realization).

Proof: let t(m) be the least i with m ≤ r(i). It is monotone, onto, and its fibers
are nonempty finite intervals: t(r(i))=i and t(m)=i implies m≤r(i). Apply the block
repetition theorem on each small etale site to obtain the exact repetition functors,
their endpoint adjunctions, and preservation of K-injective complexes. Normalize the
ordinary proper comparison on sections, and the open comparison by the extension by
zero adjunction. Their derived composite is exactly CofinalRepeatSupport.kappa.
Transport the selected ordinary extension through strictSystemSequenceEquivalence.
It has at m the tensor C_m ⊗_{C_{r(t(m))}} N_{t(m)}, with transitions given by the
original system transition followed by the tensor associator. Its unit has component
x↦1⊗x at a selected index. The ordinary selected-extension theorem proves its
adjunction to the actual sectionwise cofinalRestriction, not just to an isomorphic
unrecorded restriction. Derive this adjunction using flat-term K-flat representatives
on the sequence site. Evaluation is an exact ringed-topos inverse image and takes
these representatives to level K-flat representatives. The normalized derived-mate
comparison therefore supplies the recorded level isomorphism and its representative
normalization. Transport through a flat-term K-flat resolution also proves computation
on every K-flat representative, by the acyclic K-flat cone criterion.
The ordinary extension is repetition followed by change of coefficients for the actual
map D_m=C_{r(t(m))}→C_m. Identify those left adjoints by equality of their units. On
simultaneously level K-flat representatives both compute the same ordinary strict
complex, including transitions; universal left-derived uniqueness supplies the
factorization and exactly its displayed counit normalization.
Use etaleSystemCoefficientProjection for the fixed compactification. Its q for D→C
is invertible. Define h by the X factorization, the inverse of q on repeated systems,
the derived repetition comparison kappa, and the inverse Y factorization. Cancellation
of these four factors proves the support normalization. Evaluate the same word at m.
The normalized cochain comparisons identify repetition with evaluation at t(m), and
coefficient projection evaluation is compactScalarMap for C_{r(t(m))}→C_m. Cancel the
ordinary/derived factorization isomorphisms to obtain precisely CofinalSupport.evaluation.
Choose the ordinary restriction compositors to be identity on selected sections and
localize them. These constructions give every field of CofinalSupport. No right adjoint
to compact support, counit formula for such a right adjoint, or subsequence coherence
is used in this construction. -/
theorem etaleCofinalSupport_realization
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (hl : l.Prime) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ t : CofinalSupport c l,
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings),
        IsIso (t.projection.q a)) ∧
      (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
        t.projection.q (a ≫ b) = t.projection.path a b) := by
  sorry

end AlgebraicGeometry.Etale.SystemProjection
