/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Pullback compatibility of the Artin--Schreier rows -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Artin--Schreier rows commute with structural pullback of regular functions.
Source: Stacks Project, Tag 0A3J, opening sequence and its functoriality.
(blueprint: lem-pbc-artin-schreier-pullback-rows)

Proof: On U over C, map a section to its pullback along U ×_C C' → U,
using a and a' to identify both section groups with regular functions.
The pullback square and the naturality of a and a' make this a morphism
G → lowerStar G'. Its adjoint is q and satisfies the displayed section formula.
Ring pullback commutes with powers and subtraction. The adjunction, applied to
that sectionwise equality, proves the square with wp and wp'. Let i' be the
constant-sheaf comparison upperStar(constant Z/p) ≅ constant Z/p on C',
followed by i0. Both composites from the pulled-back constant sheaf agree on
the constant-presheaf unit: they send c to c.val times one. The sheafification
universal property and the adjunction prove the square with i. Transport the
second given short exact sequence by this constant-sheaf isomorphism; its
middle and right terms stay fixed. This gives z' and short exactness. The
construction also works on empty schemes; it asserts no cohomology comparison. -/
theorem exists_artinSchreier_pullback_rows
    {C C' : Scheme.{u}} (ι' : C' ⟶ C) (p : ℕ) [Fact p.Prime]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (wp : G ⟶ G) (wp' : G' ⟶ G')
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hwp' : ∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
      a' U (wp'.hom.app U x) = (a' U x) ^ p - a' U x)
    (i : C.constantZMod p ⟶ G) (i0 : C'.constantZMod p ⟶ G')
    (hi : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (i.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)))
    (hi0 : ∀ (U : C'.Etaleᵒᵖ) (c : ZMod p),
      a' U (i0.hom.app U
        ((toSheafify C'.smallEtaleTopology
          ((Functor.const C'.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)))
    (z0 : i0 ≫ wp' = 0) (hs0 : (ShortComplex.mk i0 wp' z0).ShortExact) :
    ∃ (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
      (i' : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj (C.constantZMod p) ⟶ G')
      (z' : i' ≫ wp' = 0),
      (ShortComplex.mk i' wp' z').ShortExact ∧
      (Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q = i' ∧
      (Etale.upperStar AddCommGrpCat.{u + 1} ι').map wp ≫ q = q ≫ wp' ∧
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)) := by sorry

end AlgebraicGeometry.IsCurve
