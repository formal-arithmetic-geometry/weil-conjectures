/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.DeligneLaumon.RawHeartAdicLisseData
import Sheaf.Paper.ClassicalLisseWeilFrontierRestriction

/-! # Weil and frontier extension of classical lisse strata

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

/-- Extend a supplied normalized finite classical partition to finite-field frontiers
and to rational Weil isomorphisms on descended pieces. The original partition and
its coefficient stage remain inputs.

Source: blueprint thm-zl-real-mixed-by-curves, proof paragraphs 6--7;
lem-zl-classical-lisse-weil-frontier-restriction and
lem-zl-smooth-affine-frontier-stratification; BS 6.8.4(4), 6.8.15
(blueprint: lem-zl-raw-heart-adic-restriction-bridge).

Proof: Transport the supplied partition across e and apply smooth affine frontier
stratification. Use the canonical associativity isomorphism of the two geometric
base changes: its first projection is the composite of the two first projections.
In the descent proof the finite diagram is descended over this projection, so the
piece factorizations hold for this same canonical isomorphism. Transport back along
e to obtain the refinement field. The other fields are precisely the finite closed
chain, its differences and its smooth affine geometrically connected components.
For the Weil clause, the model and field projection equations define geometric
Frobenius on W by the pullback universal property, transported through eW. The
hypotheses on the model square imply equivariance with the mth ambient Frobenius.
Pull the carrier identification and the iterated Weil isomorphism to W, inserting
the actual completed-pullback compositors. The model remains lisse under pullback.
Fullness of the common classical realization lifts this isomorphism and its inverse;
faithfulness proves both inverse equations. The common-stage Hom definition places
the two maps and both equations at a single finite enlargement containing s.stage.
Take the resulting finite model, its carrier isomorphism, and its rational Weil
isomorphism. The realization equation is exactly the conjugation by that carrier
and the specified classicalPullIso. The point normalization intertwines all iterates.
An invariant integral lattice is never required. Empty partitions make the Weil
clause vacuous, and the frontier theorem includes empty geometric schemes. -/
theorem raw_heart_adic_restriction_bridge
    (a : LisseRealization.Family D l hl) (ha : Normalized D l hl Ω a)
    (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c)
    (hcommon : (∀ Y : PerAdic.Base D.k, Nonempty (ClassicalCommon D l hl Ω a c b Y)))
    (X : PerAdic.Base D.k) (M : sfCommonStageHeart l X.scheme Ω)
    (s : Strata D l hl Ω a c b X M) :
        (∀ (Y₀ : Over (Spec (.of D.k₀)))
          [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
          (e : X.scheme ≅ (D.geometricFiber Y₀).left.nilradical.subscheme),
          Nonempty (Frontier D l hl Ω s Y₀ e)) ∧
        (∀ (Y₀ : Over (Spec (.of D.k₀)))
          [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
          (e : X.scheme ≅ (D.geometricFiber Y₀).left)
          (K : sfCommonStageWeilComplex D l hl Y₀ Ω),
          Nonempty ((pullCommon D l hl Ω (X := X) (Y := geometricBase D Y₀) e.hom).obj
            K.carrier ≅ M.obj) →
          ∀ (ν : Fin s.partition.n) (m : ℕ) (hm : 1 ≤ m)
            (V₀ : Over (Spec (.of (D.extensionSubfield m hm))))
            (j₀ : V₀ ⟶ finiteModel D Y₀ m hm), IsImmersion j₀.left →
          ∀ (W : PerAdic.Base D.k)
            (eW : W.scheme ≅ ((geometricChange D m hm).obj V₀).left),
            eW.hom ≫ ((geometricChange D m hm).obj V₀).hom =
              (W.scheme ↘ Spec (.of D.k)) →
          ∀ (j : W.scheme ⟶ (s.bases ν).scheme), IsImmersion j →
            (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫
                pullback.fst Y₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
              eW.hom ≫ pullback.fst V₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m hm) D.k))) ≫
                j₀.left ≫ pullback.fst Y₀.hom
                  (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) →
            (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫
                (D.geometricFiber Y₀).hom = (W.scheme ↘ Spec (.of D.k)) →
            Nonempty (WeilLift D l hl Ω s Y₀ e K ν m hm V₀ W eW j)) := by sorry

end WeilConjectures.RawHeartAdic
