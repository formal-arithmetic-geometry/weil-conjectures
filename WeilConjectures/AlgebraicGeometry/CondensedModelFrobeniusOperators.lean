/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsStructural
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusIterates
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusGlobal
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusLocal

/-! Canonical condensed model Frobenius comparison, a step of the operator theorem. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

set_option maxHeartbeats 4000000 in
-- Combining the dependent witnesses unfolds the large derived-category signatures.
/-- Model and semilinear structures have identical iterates and identical global and
local operators in the ordinary derived category of actual condensed coefficient modules.

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-model-frobenius-operators).

Proof plan (the twelve steps of the DAG node):
1. Factor Phi^m using prop-trf-frobenius-factorization. The linear trivialization
   lem-pur-condensed-frobenius-linear-trivialization and the coherent coefficient
   compositors give kappa. Its naturality is lem-pur-condensed-absolute-frobenius-pullback.
2. Multiplicative iteration of lem-trf-absolute-frobenius-site and coefficient
   coherence show kappa_(r+m) = G_r(kappa_m) kappa_r.
3. Naturality and the strict-pair iteration then give u_(r+m) = u_r P_r(u_m).
   Every u_m is an isomorphism, yielding the model Weil object.
4. The geometric-point equivalence lem-weil-pbc-geometric-field-proetale-evaluation
   defines the point reparametrization. On s[S] relative Frobenius fixes S; hence the
   point normalization is kappa_s = r_m inverse, on all condensed modules.
5. Choose a dense model compactification by det-nagata-theorem-dense and base change
   it. Flatness of the field extension preserves schematic density. Open Frobenius
   squares are Cartesian by lem-trf-frobenius-open-square. Compact-support composition
   sk-thm-sf-comp-composition identifies this model with chosen Ra_!. The semilinear
   exchange is the proper mate followed by open exchange, as specified by
   lem-pod-condensed-automorphism-compact-exchange.
6. Under the pullback/direct-image adjunction, the two transposes of the proper
   model comparison are equal by naturality of kappa and its structure-map square.
   Thus Rp_*(kappa) rho_P = E_G r_m inverse. This uses no Cartesian model square.
7. Under j_! adjoint to j^*, both transposes of the open comparison equal
   G_X(eta_j) kappa_X. Hence b_G kappa_Z = j_!(kappa_X) b_P.
8. The mate chi of b_P restricts to identity on X. The uniqueness assertion in
   det-sf-comp-composition-interchange identifies it with proper/open interchange;
   lem-zl-condensed-open-proper-pasting gives the same normalized compositor.
   The triangle identity yields chi j_!(eta_X) = R_Z(b_P) eta_Z.
9. Combine the preceding two equations: C(kappa) rho_model = e_m r_m inverse.
   Composing C(theta^[m]) proves the global-operator comparison. Transport by the
   canonical common-refinement isomorphism to the chosen compact-support functor.
10. Paste proper mates and inverse open mates. The middle unit/counit cancel,
    giving e_(r+m) = (e_r G_m)(Q_r e_m), with the coherent square compositors.
11. Naturality of e_r and r_r, together with iteration of theta, gives
    F_(r+m) = F_r F_m; induction gives F_m = F_1^m.
12. The lift of an F_(q^m)-point is fixed by Phi^m; on coefficients g_X^m x = x g_s^m.
    Absolute-Frobenius naturality and kappa_s = r_m inverse identify the model
    stalk comparison with the semilinear return. Compose pullback of theta^[m].
    These are equal module morphisms before cohomology or trace. No trace-formula
    equality, dualizability or lattice is used.
-/
theorem condensed_model_frobenius_operators
    [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D₀.p)]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (c₀ : Compactification X₀.hom) :
    ∃ (w : Factorization D₀ X₀)
      (hB : boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
        K.carrier.obj)
      (hf : ∀ m : ℕ, IsFinite (frobeniusIterate (modelEnd D₀ X₀) m).left)
      (hu : ∀ m : ℕ, IsUniversalHomeomorphism (frobeniusIterate (modelEnd D₀ X₀) m).left)
      (wj : ∀ m : ℕ,
        ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) ≫
            (geometricCompactification D₀ X₀ c₀).i =
          (geometricCompactification D₀ X₀ c₀).i ≫
            ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m))
      (wp : ∀ m : ℕ,
        ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m) ≫
            (geometricCompactification D₀ X₀ c₀).g =
          (geometricCompactification D₀ X₀ c₀).g ≫
            ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m)),
      (∀ m : ℕ, 1 ≤ m →
        modelStructure D₀ X₀ ell K w m =
          modelIterate D₀ X₀ ell K w m) ∧
      (∀ m : ℕ, 1 ≤ m →
        compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) (wj m) (wp m)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom =
        (compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ 1)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ 1)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ 1) (wj 1) (wp 1)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) 1).hom) ^ m) ∧
      (∀ m : ℕ, 1 ≤ m →
        (compactIdentification ell (geometricCompactification D₀ X₀ c₀)
          ⟨K.carrier.obj, hB⟩).inv ≫
          modelGlobal ell (frobeniusIterate (modelEnd D₀ X₀) m) (hf m) (hu m)
            (modelObject ell (frobeniusIterate (modelEnd D₀ X₀) m) ⟨K.carrier.obj, hB⟩
              (modelStructure D₀ X₀ ell K w m)) ≫
          (compactIdentification ell (geometricCompactification D₀ X₀ c₀)
            ⟨K.carrier.obj, hB⟩).hom =
        compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) (wj m) (wp m)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m) (z : D₀.extensionPoints X₀ m hm),
        ∃ (x : RationalPoint (D₀.geometricFiber X₀))
          (hx : x ≫ frobeniusIterate (modelEnd D₀ X₀) m = x)
          (wx : x.left ≫ ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) =
            ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) ≫ x.left),
          x.left ≫ pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) =
            Spec.map (CommRingCat.ofHom (D₀.extensionSubfield m hm).subtype) ≫ z.left ∧
          (localIdentification ell ⟨K.carrier.obj, hB⟩ x).inv ≫
            modelLocal ell (frobeniusIterate (modelEnd D₀ X₀) m)
              (modelObject ell (frobeniusIterate (modelEnd D₀ X₀) m) ⟨K.carrier.obj, hB⟩
                (modelStructure D₀ X₀ ell K w m)) x hx ≫
            (localIdentification ell ⟨K.carrier.obj, hB⟩ x).hom =
          stalkReturn (Profinite.padicAlgClRingObj ell) x.left
            ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
            ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) wx
            (iterateStructure (Profinite.padicAlgClRingObj ell)
              (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom) := by
  obtain ⟨w, hB, hf, hu, wj, wp, _⟩ :=
    condensed_model_frobenius_operators_structural D₀ X₀ ell K c₀
  refine ⟨w, hB, hf, hu, wj, wp, ?_, ?_, ?_, ?_⟩
  · exact condensed_model_frobenius_iterates D₀ X₀ ell K w
  · exact (condensed_model_frobenius_global D₀ X₀ ell K c₀ w hB hf hu wj wp).1
  · exact (condensed_model_frobenius_global D₀ X₀ ell K c₀ w hB hf hu wj wp).2
  · exact condensed_model_frobenius_local D₀ X₀ ell K w hB

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
