/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Affine formal maps and inverse limits of sections

Source: Stacks Project, Tags 087W, 00MA and 0889(1).
(blueprint: lem-weil-pbc-affine-formal-map-limit-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The affine dictionary identifies a formal morphism with a completed linear map,
and identifies that map with the actual inverse limit of its section maps.
No torsion hypothesis or annihilator conclusion is involved.

Source: Stacks Project, Tags 087W, 00MA and 0889(1), affine comparison before
applying Remark 0888.
(blueprint: lem-weil-pbc-affine-formal-map-limit-dictionary).

Proof:
1. Transport X and its ideal along X.isoSpec. The ideal of the top affine open
   becomes I, so the transported formal systems satisfy the hypotheses of 087W.
   Apply its equivalence to N. Let Q be the resulting finite S-module; its inverse
   comparison, transported back to X, gives rho. The limit cone supplied by 087W
   identifies its underlying A-module with the categorical limit of N's sections,
   giving the A-linear equivalence a.
2. The tilde presentation epsilon and coherence of H imply that P is finite over A.
   Thus B = S tensor P is finite over S, and is complete for the extended ideal.
   The inverse comparison of 087W, or the finite-module completion comparison of
   00MA, identifies B with the limit of the section system C(B). Denote this
   canonical A-linear equivalence by cB. Define b as cB followed by the limit map
   of eta inverse and then by that of completion(epsilon). This uses the supplied
   eta, even when it differs from the tensor unit; all three maps are invertible.
3. Form the formal-system map f = rho inverse followed by delta, then by
   completion(epsilon inverse), then by eta, from C(Q) to C(B). Fullness of the
   affine equivalence, using its inverse comparison on Q and B, produces an
   S-linear phi with C(phi) = f. Cancelling the isomorphisms gives the displayed
   factorization of delta. Naturality of the specified limit cones gives
   cB(phi(x)) = lim(C(phi))(a0(x)), where a0 compares Q with lim sections C(Q).
   Take a to be a0 followed by lim(rho inverse). Applying lim(eta inverse) and
   lim(completion(epsilon)) gives the required square with the actual section-limit
   map of delta. No arbitrary linear bijection is substituted.
These constructions use finite-module completeness over the Noetherian completed
ring. For I=0 the quotient systems are constant, and for I=A all formal modules
and limits are zero. Thus the same comparisons apply to these cases and to the
zero ring. No data definition chooses a witness from this existence theorem.
-/
theorem affine_formal_map_limit_dictionary
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∀ (P : ModuleCat.{u} A) (ε : L.obj P ≅ H.obj)
      (η : C.obj P ≅ C.obj (ModuleCat.of A (S ⊗[A] P))),
    ∃ Q : ModuleCat.{u} S,
      letI := Module.restrictScalars A S Q
      letI := IsScalarTower.restrictScalars A S Q
      ∃ (φ : Q →ₗ[S] S ⊗[A] P)
        (ρ : N.obj ≅ C.obj (ModuleCat.of A Q))
        (a : Q ≃ₗ[A] ↥(limit (N.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A))
        (b : (S ⊗[A] P) ≃ₗ[A] ↥(limit (((completion X J).obj H).obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A)),
        δ.hom = ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫
          η.inv ≫ (formalCompletionFunctor J).map ε.hom ∧
        ∀ x : Q, b (φ x) =
          (lim.map (Functor.whiskerRight δ.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))).hom (a x) := by sorry

end AlgebraicGeometry
