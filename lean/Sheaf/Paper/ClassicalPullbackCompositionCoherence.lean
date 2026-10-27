/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.Paper.LisseAdicAutomorphismPullback
public import Sheaf.Paper.LisseAdicFiberFunctors

/-! # Associativity of germ-normalized classical pullback composition

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15;
Weil II (1.1.1) b)--d). This is the three-pullback coherence used in the
constant-extension calculation, before any Weil map or iteration is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalLocalFrobenius

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Germ-normalization forces associativity of the inverse classical compositors.

Source: BS 6.8.4(1),(4), 6.8.15; Weil II (1.1.1) b)--d); the reassociation
step in the proof of classicalWeil_blocks
(blueprint: lem-zl-classical-pullback-composition-assoc).

Proof: apply the algebraic fibre functor to both threefold words. Its
functoriality and naturality of the pullback-fibre comparisons move the inner
compositor across the outer comparison. Solve the normalization equation for
the image of each inverse compositor and cancel adjacent inverse comparisons.
It remains to compare the two compositions of the canonical pullback-fibre
maps for f, g and h. These canonical maps are computed at the unchanged finite
coefficient models. At each finite quotient they send a germ (U,z,s) to the
identical germ with its structure map reindexed. Both threefold words send every
pointed-neighbourhood colimit injection to the germ with structure map x f g h.
Associativity of scheme composition identifies these maps and their pointed
lifts. Colimit extensionality gives equality at every quotient; inverse-limit
projections give equality on the integral fibres. Tensoring first with the finite
coefficient field and then Ω preserves the equality. Naturality is checked in
the same way, first for integral arrows, then for rational pure tensors and
finite sums, and finally for arrows in the coefficient localization.
The algebraic fibre functor is defined by these same scalar extensions. Its
pullback comparisons are natural, so the normalization equations give equality
for the displayed maps on every geometric fibre. To detect equality, decompose
the Noetherian scheme into its finitely many connected clopen components. On
each nonempty component choose a geometric point. Use the finite-coefficient
part of cor-galois-lisse-representations: finite lisse stalks detect arrows on
that component. For integral adic systems the free inverse-limit fibre surjects
onto each finite fibre; thus equality on the limit detects equality at every
finite level and hence of integral system arrows. For rational maps clear a
common denominator. Integral fibres are finite free and hence torsion-free, so
localizing them is injective and detects the numerator. For algebraic-coefficient
maps choose a common finite coefficient model in the filtered coefficient
localization. Faithfulness of field extension to Ω reduces equality to the
rational case. Consequently the actual algebraic fibre detects these arrows.
Restricting to each component gives equal arrows there; the finite clopen
restriction family detects equality at every finite level and after both
localizations by the same common-model argument. The empty scheme has only zero
sheaves. Thus the original arrows are equal after the associativity transport of
their sources, which is precisely the heterogeneous equality below.
The argument does not assume connectedness, a chosen geometric basepoint, a Weil
structure, or a stable integral lattice for a rational automorphism. -/
theorem normalizedClassicalComposition_assoc
    (c : ∀ h k : Y ≅ Y,
      lisseAlgebraicAutomorphismPullback k l Ω ⋙
        lisseAlgebraicAutomorphismPullback h l Ω ≅
          lisseAlgebraicAutomorphismPullback (h ≪≫ k) l Ω)
    (hc : ∀ (h k : Y ≅ Y) (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ Y) (F : LisseAlgebraicSheaf l Y Ω),
      let T := (lisseAlgebraicFiberFunctor l Y x Ω).copyObj
        (lisseAlgebraicFiber l Y Ω x)
        (fun M ↦ eqToIso (lisseAlgebraicFiberFunctor_obj l Y x Ω M))
      T.map ((c h k).hom.app F) ≫
          (lisseAlgebraicAutomorphismFiberIso (h ≪≫ k) l Ω x F).hom =
        (lisseAlgebraicAutomorphismFiberIso h l Ω x
          ((lisseAlgebraicAutomorphismPullback k l Ω).obj F)).hom ≫
        (lisseAlgebraicAutomorphismFiberIso k l Ω (x ≫ h.hom) F).hom ≫
        eqToHom (congrArg (fun y ↦ lisseAlgebraicFiber l Y Ω y F)
          (Category.assoc x h.hom k.hom)))
    (f g h : Y ≅ Y) (F : LisseAlgebraicSheaf l Y Ω) :
    HEq
      ((c f (g ≪≫ h)).inv.app F ≫
        (lisseAlgebraicAutomorphismPullback f l Ω).map ((c g h).inv.app F))
      ((c (f ≪≫ g) h).inv.app F ≫
        (c f g).inv.app ((lisseAlgebraicAutomorphismPullback h l Ω).obj F)) := by
  sorry

end WeilConjectures.ClassicalLocalFrobenius
