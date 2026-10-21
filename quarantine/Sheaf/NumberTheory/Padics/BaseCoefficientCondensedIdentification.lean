/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Condensed realizations of the base p-adic coefficients

Source: blueprint `main-20261015`, `sk-thm-existence`, opening paragraphs of
`det-existence-localizing.proof.md` and `det-existence-restriction.proof.md`
(blueprint: lem-sfb-base-coefficient-condensed-identification).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace Profinite

/-- The structural image of the base field and its unit ball give the usual rational and
integral condensed coefficients, compatibly with inclusion. The bottom intermediate field
has its inherited subspace norm; `PadicAlgCl.integers` is the unit ball for precisely this
norm. Ring objects here use the tensor product of condensed abelian groups.

Source: blueprint `main-20261015`, `sk-thm-existence`, introductory coefficient
specializations in `det-existence-localizing.proof.md` and
`det-existence-restriction.proof.md`
(blueprint: lem-sfb-base-coefficient-condensed-identification).

Proof: (1) Restrict the structural embedding to its image, the bottom intermediate field.
Its inverse sends an image element to its unique preimage; this is
`IntermediateField.botEquiv`. Both maps preserve the ring operations by injectivity.
(2) The ambient norm extends the p-adic norm, so this ring equivalence preserves norms and
distances. Substituting inverse images proves that its inverse is also an isometry.
(3) Norm preservation identifies the two unit balls. Restrict the equivalence and its
inverse to obtain an isometric ring equivalence of the integer rings, using
`def-weil-l-adic-coefficient-extension` and the explicitly prescribed subspace norm.
(4) Apply the continuous-map construction of `sk-def-sfb-condensed-ring` to these four
continuous ring maps. Their components are postcomposition, preserve the pointwise ring
operations, and are inverse pointwise; hence they give isomorphisms of ring objects.
(5) Precomposition with a profinite map commutes with each of the four postcomposition
maps, giving naturality for both isomorphisms and both inverses. The integral equivalence
is the restriction of the rational equivalence, so composing with inclusion gives the
same scalar map. Postcomposition on sections proves the compatibility square below. -/
theorem base_coefficient_condensed_identification (l : ℕ) [Fact l.Prime] :
    ∃ (e : ℚ_[l] ≃+* (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))
      (eInt : ℤ_[l] ≃+*
        PadicAlgCl.integers l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))),
      e.toRingHom = algebraMap ℚ_[l] (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ∧
      eInt.toRingHom = AlgebraicGeometry.ProEtale.padicIntToIntegers l
        (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ∧
      Isometry e ∧ Isometry e.symm ∧ Isometry eInt ∧ Isometry eInt.symm ∧
      ∃ (qIso : (Mon.mk (continuousMapRingObj.{u} ℚ_[l]) : CondensedRing.{u}) ≅
          Mon.mk (continuousMapRingObj
            (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))
        (zIso : (Mon.mk (continuousMapRingObj.{u} ℤ_[l]) : CondensedRing.{u}) ≅
          Mon.mk (continuousMapRingObj
            (PadicAlgCl.integers l (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))),
        (∀ (S : Profinite.{u}) (a : C(S, ℚ_[l])) (s : S),
          ((qIso.hom.hom.hom.app (op S)) (ULift.up a)).down s = e (a s)) ∧
        (∀ (S : Profinite.{u})
          (a : C(S, (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))) (s : S),
          ((qIso.inv.hom.hom.app (op S)) (ULift.up a)).down s = e.symm (a s)) ∧
        (∀ (S : Profinite.{u}) (a : C(S, ℤ_[l])) (s : S),
          ((zIso.hom.hom.hom.app (op S)) (ULift.up a)).down s = eInt (a s)) ∧
        (∀ (S : Profinite.{u})
          (a : C(S, PadicAlgCl.integers l
            (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)))) (s : S),
          ((zIso.inv.hom.hom.app (op S)) (ULift.up a)).down s = eInt.symm (a s)) ∧
        zIso.hom.hom ≫
            (sheafCompose (coherentTopology Profinite.{u})
              (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (continuousMapRingSheafMap
                (PadicAlgCl.integers l
                  (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))).subtype
                continuous_subtype_val) =
          (sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (padicIntCondensedRingToPadicCondensedRing l) ≫ qIso.hom.hom := by
  sorry

end Profinite
