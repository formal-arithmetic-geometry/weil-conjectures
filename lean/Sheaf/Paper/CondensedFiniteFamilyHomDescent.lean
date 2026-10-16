/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.CondensedLocalCoefficientAdjoints
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.Paper.CondensedCoefficientFamilyHomStage

/-!
# One-way finite coefficient factorization on a finite family of qcqs schemes

Source: archived ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(blueprint: lem-weil-pbc-condensed-finite-family-hom-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open MonObj

/-- Finite-stage comparison maps in both directions on all pairwise pullbacks.

Source: archived `TwoColimit.lean`, (Obj) overlap descent paragraph.
(blueprint: lem-weil-pbc-condensed-finite-family-hom-descent).

Proof: fix a pair i,j and write W for its pullback. Identify both pulled E-rings
with E_W, using the monoidal composition comparison and `upperStarFromPointComp`,
and do the same for every later coefficient field and for Omega. Write P_i and P_j
for the transported modules on W, and V for the transported pullback of M. Pullback
preserves their finite presentations: apply its left adjoint to the finite free
cokernel presentation, using preservation of finite biproducts and the identification
of the pulled regular module with the regular module. Scalar transport along a ring
isomorphism preserves the same presentations.

The pulled isomorphisms give u_i : Omega tensor_E P_i ≅ V and u_j similarly.
Transpose u_i.hom followed by u_j.inv under E-to-Omega scalar adjunction to obtain
an E-map P_i → Res_EOmega(Omega tensor_E P_j); also form the reverse map.
Apply `condensed_coefficient_family_hom_stage` to this finite family indexed by
ordered pairs and the two directions. For its common F, transpose each factor b_ij
under E-to-F adjunction to obtain s_ij : F tensor_E P_i → F tensor_E P_j.

Let q_i be the canonical F-adjoint into Res_FOmega V. Under E-to-F adjunction,
the composite s_ij followed by q_j corresponds to b_ij followed by Res_EF(q_j).
By tensor transitivity and the unit formula this is the composite of b_ij with
the specified mixedScalarMap and Res_EOmega(u_j.hom). Its factorization equation
makes it the transpose of u_i.hom followed by u_j.inv followed by u_j.hom,
hence the transpose of u_i.hom. This is also the E-to-F transpose of q_i,
so injectivity of that adjunction proves s_ij followed by q_j equals q_i.
The reverse direction has the identical calculation with i and j interchanged.
Transport back by the inverse-image comparisons. The two identifications of V
differ by exactly the displayed `upperStarCompIso`; in the reverse direction its
inverse occurs. These are precisely the two asserted equations for the defined
`finiteCoefficientLocalAdjoint`. No identity for the composites of s and t is
needed. If the index type is empty choose F = E; every equation is vacuous.
-/
theorem exists_finiteCoefficient_family_hom_factorizations
    (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (I : Type u) [Finite I] (Y : I → Scheme.{u}) (g : ∀ i, Y i ⟶ X)
    [∀ (i j : I), CompactSpace (pullback (g i) (g j) : Scheme.{u})]
    [∀ (i j : I), QuasiSeparatedSpace (pullback (g i) (g j) : Scheme.{u})]
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (g i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (g i)).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, (Mod.extendScalars ((upperStar Ab.{u + 1} (g i)).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj (N i) ≅
      ((upperStar Ab.{u + 1} (g i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F),
      let L := fun i ↦ finiteCoefficientLocalModel T X f ℓ E (Y i) (g i) (N i) F hEF
      let q := fun i ↦ finiteCoefficientLocalAdjoint T X f ℓ E (Y i) (g i) (N i) M
        (e i).hom F hEF
      let B := ((Mod.comap ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M).X
      ∀ i j, ∃ (s : (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).obj (L i).X ⟶
          (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).obj (L j).X)
        (t : (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).obj (L j).X ⟶
          (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).obj (L i).X),
        (s ≫ (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map (q j).hom =
          (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map (q i).hom ≫
            (upperStarCompIso Ab.{u + 1} (pullback.condition (f := g i) (g := g j))).hom.app
              B) ∧
        (t ≫ (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map (q i).hom =
          (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map (q j).hom ≫
            (upperStarCompIso Ab.{u + 1} (pullback.condition (f := g i) (g := g j))).inv.app
              B) := by
  sorry

end AlgebraicGeometry.ProEtale
