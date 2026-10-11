/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.Topology.RingedSpaceModuleCohomology
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Basic

/-! # Finiteness of cohomology of ideal powers over the Rees algebra

Source: Stacks Project, Cohomology of Schemes, Lemma 02O8, and its preceding paragraph
(blueprint: lem-weil-pbc-cohomology-powers-ideal-rees-finite).

The sheaves `I^n F` are the shared `Scheme.idealModuleProduct (Scheme.idealSheafPower
J.toModulesι n).2 F` (at `n = 0` the power is `O_X` with identity inclusion, so the product
is canonically `F`), and `H^q(X, -)` is an `A`-module by restriction of scalars along
`A ≅ Γ(Spec A, O) → Γ(X, O_X)`, as in the landed statements.
-/

universe v

open CategoryTheory Opposite DirectSum

namespace AlgebraicGeometry

open Classical in
/-- For a proper scheme over a Noetherian affine base and a coherent module, the
cohomology of its ideal powers is finite over the Rees algebra. `J` is the extended ideal
`I O_X`. The multiplication maps are specified on every open after the inclusions into `F`.
The double finite sum is the convolution formula: its degree `n` consists exactly of terms
with `k + m = n`.

Source: Stacks Project, Lemma 02O8 and the preceding paragraph
(blueprint: lem-weil-pbc-cohomology-powers-ideal-rees-finite).

Proof:
1. The base is Noetherian and proper implies finite type, so X is Noetherian. Coherence
implies quasi-coherence (pqf-lem-coherent-ft-locnoeth). Extend I by comap; on affine opens
its powers times F have sections f^sharp(I^n) F(U), by
lem-weil-pbc-module-pullback-ideal-quotient and
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections. Multiplication by a in I^k
therefore carries the mth image into the (m+k)th image. This holds on arbitrary opens by
checking on an affine cover. The resulting lambda maps are additive in a, compose by
multiplication of coefficients, and in degree zero are scalar multiplication.
2. The Rees algebra has degree k piece I^k t^k and degree zero A
(prop-nagata-rees-graded, lemma-nagata-rees-degree-zero). Noetherianity makes I finitely
generated, hence its Rees algebra finite type over A (prop-nagata-rees-finite-generation).
3. Regard the family I^m F with these maps as a graded module sheaf. Local generators of
F in degree zero generate all degrees: on affine opens write a section as a sum a_j u_j
and locally express each u_j in the chosen generators. Thus the graded sheaf is finite
type, and the maps satisfy all the conditions of lem-weil-pbc-graded-finiteness-cohomology.
4. Apply that lemma (Stacks 0897 (1)): the direct sum of cohomology is a finite Rees
module with the asserted convolution action. For degree zero the induced cohomology map
is the A-scalar action, by the convention defining the A-module structure.
-/
theorem cohomology_powers_ideal_rees_finite {A : Type v} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ) :
    ∃ lam : ∀ (k m : ℕ) (a : A) (_ha : a ∈ I ^ k),
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F ⟶
          Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι (m + k)).2 F,
      (∀ (k m : ℕ) (a : A) (ha : a ∈ I ^ k) (U : X.Opens)
        (s : (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.obj
          (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
            U).hom ((lam k m a ha).app U s) =
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom a) •
            ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
              U).hom s) ∧
      (∀ (m : ℕ) (a : A) (ha : a ∈ I ^ 0)
        (x : (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F))),
        ((RingedSpace.moduleCohomology X.toRingedSpace q).map (lam 0 m a ha)).hom x =
          a • x) ∧
      ∃ mod : Module (reesAlgebra I) (⨁ n : ℕ, (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))),
        @Module.Finite (reesAlgebra I) (⨁ n : ℕ, (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))) _ _
          mod ∧
        ∀ (b : reesAlgebra I) (x : ⨁ n : ℕ, (ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
              ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))),
          @SMul.smul _ _ mod.toSMul b x =
            ∑ k ∈ b.val.support, ∑ m ∈ x.support,
              DirectSum.of (fun n : ℕ ↦ (ModuleCat.restrictScalars
                  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
                    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F)))
                (m + k)
                (((RingedSpace.moduleCohomology X.toRingedSpace q).map
                  (lam k m (b.val.coeff k) (b.property k))).hom (x m)) := by
  sorry

end AlgebraicGeometry
