/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData
import Sheaf.SixFunctors.ClopenComparisonTensorSquareDataExistence
import Sheaf.SixFunctors.ClopenComparisonTensorSquareEquations

/-! # Tensor squares for normalized clopen comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

/-- Tensor squares for the open-base-change and clopen-projection factors, and
therefore for their full comparison, in both coefficient settings.
Source: Stacks 0F7B, 07A4, 0GL1, 04TS
(blueprint: lem-sf-clopen-comparison-tensor-square).

Proof: (1) The geometric proper/open calculus makes the canonical lift clopen.
Use the normalized open comparisons and the canonical ringed tensor comparisons;
the tensor-structure theorem identifies their composition constraints. (2) Both
objects of the Cartesian tensor square lie in the fully faithful image of b_!.
Restrict to b; the open units cancel and both routes become mu_q. (3) Exact clopen
module gluing splits modules into the selected piece and its complement. Projection
onto the first factor is (identity,zero). The same coordinate functors commute with
all semilinear coefficient transitions. (4) Localize the exact first-factor
adjunction, retaining its unit and inverse-open-unit counit. Its Hom bijection tests
equality of arbitrary unbounded derived maps, before evaluation. (5) The two maps
of the clopen tensor square have the same transpose mu_s, by naturality of mu_s and
the open normalization. (6) The composite-open comparison and delta_k have identity
restriction under the composite open unit; full faithfulness equates them. (7)
Expand alpha as beta followed by b_!rho_s. Move rho_s past mu_q by naturality, apply
the Cartesian tensor square and then the clopen tensor square, and combine the two
open tensor comparisons using (6). The remaining factors are alpha_H tensor 1.
All arguments take place on the whole ringed site, with no boundedness, flatness,
constructibility, Tor-amplitude or proper projection-isomorphism hypothesis. -/
theorem clopenComparisonTensorSquare (m : Mode) {A B C D : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S)
    (t : SiteSquare (input m p i R S c))
    (o : Operations (input m p i R S c) t) (a : Assertion o) :
    Nonempty (Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h)) ∧
      ∀ v : Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h),
        Equations a v := by
  obtain ⟨v⟩ := data_nonempty m k i r p h R S c t o a
  refine ⟨⟨v⟩, ?_⟩
  intro w
  exact equations_for_data a w

end SheafOfModules.ClopenComparisonTensorSquare
