/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix

public import Sheaf.AlgebraicGeometry.ContinuousFieldMatrixElimination

/-!
# Lifting a specified continuous matrix factorization to module sheaves

Source: Hemo--Richarz--Scholbach, Example 3.1, and the Gaussian elimination step
of the accompanying rank/descent argument.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lift an explicit continuous matrix block factorization along an open immersion.
Source: steps 6--7 of the rank/descent argument accompanying Hemo--Richarz--Scholbach,
Example 3.1 (blueprint: lem-weil-pbc-continuous-field-matrix-sheaf-normal-form).
Proof: for the continuous-function ring, a regular-module endomorphism is multiplication
by its value at one. Linearity gives this on arbitrary sections; naturality along the
unique map to the terminal site object identifies these values with restrictions of
a global continuous function. Conversely multiplication by a global function is a
linear natural transformation. The assignments are inverse and preserve addition and
composition. Biproduct inclusions and projections extend this correspondence to finite
matrices. Thus P and Q give automorphisms. The chosen injections split source and target
indices into the selected r entries and their finite complements. For the open immersion,
the monoidal inverse-image/localization-restriction comparison identifies the component
functions of the restricted map with composition along g. Transport along e and the
finite-biproduct comparisons gives the two changes of basis a and b; enumerate the finite
complements by Fin of their cardinalities. The explicit matrix factorization then gives
the asserted equality. Rank zero, zero-sized matrices and empty opens are permitted. -/
theorem continuousField_matrix_sheaf_normalForm
    (E : Type u) [NormedField E] {V W : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (g : W ⟶ V) [IsOpenImmersion g]
    (r : ℕ) (ρ : Fin r → Fin n) (γ : Fin r → Fin m)
    (hρ : Function.Injective ρ) (hγ : Function.Injective γ)
    (P : Matrix (Fin n) (Fin n) (C(W, E)))
    (Q : Matrix (Fin m) (Fin m) (C(W, E)))
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : (continuousFieldPresentationMatrix E V e f).map
        (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) =
      P * ((Matrix.fromBlocks 1 0 0 0 :
        Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
          (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q) :
    ∃ (s t : ℕ)
      (a : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R m) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) s)
      (b : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R n) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) t),
      ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f =
        a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv := by sorry

end AlgebraicGeometry.ProEtale
