/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport

/-! # Completed integral coefficients on a small site

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59
(blueprint: def-a1-completed-integral-small-site).
The existing scheme construction is retained. This interface allows a small representative,
a specified uniformizer, and either containing value universe. Index n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c a w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.CompletedSite

/-- Ring sheafification is transported from a small model in its value universe.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
instance ringSheafify {C : Type c} [SmallCategory C] (J : GrothendieckTopology C)
    [UnivLE.{c, a}] : HasSheafify J CommRingCat.{a} :=
  letI : EssentiallySmall.{a} C := inferInstance
  hasSheafifyEssentiallySmallSite J CommRingCat.{a}

variable {C : Type c} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type a) [CommRing A] (p : A)

/-- The constant ring in a universe containing the site and coefficients.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
abbrev constant : Sheaf J CommRingCat.{max a c w} :=
  (constantSheaf J CommRingCat.{max a c w}).obj (CommRingCat.of (ULift.{max c w} A))

/-- The n+1 residue ring, with the specified uniformizer.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
abbrev residue (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)

/-- Constant sheafification of the quotient factor map.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
def transition (n : ℕ) :
    constant.{c, a, w} J (residue A p (n + 1)) ⟶ constant.{c, a, w} J (residue A p n) :=
  (constantSheaf J CommRingCat.{max a c w}).map
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).ulift)

/-- The actual inverse sequence of constant residue ring sheaves.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
def tower : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max a c w} :=
  Functor.ofOpSequence (X := fun n ↦ constant.{c, a, w} J (residue A p n))
    (transition.{c, a, w} J A p)

/-- The completion is the limit, with its usual limit projections.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
abbrev ring : Sheaf J CommRingCat.{max a c w} := limit (tower.{c, a, w} J A p)

/-- The constant-to-residue quotient morphism.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
def quotient (n : ℕ) : constant.{c, a, w} J A ⟶ constant.{c, a, w} J (residue A p n) :=
  (constantSheaf J CommRingCat.{max a c w}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))).ulift)

/-- The quotient legs form the constant cone.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site).
Proof: the consecutive quotient factor composed with the quotient map is the lower
quotient map, on every representative. Constant sheafification preserves this equality. -/
theorem quotient_compatible (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (constant.{c, a, w} J A)).map
        (homOfLE (Nat.le_succ n)).op ≫ quotient.{c, a, w} J A p n =
      quotient.{c, a, w} J A p (n + 1) ≫
        (tower.{c, a, w} J A p).map (homOfLE (Nat.le_succ n)).op := by
  sorry

/-- The canonical map, defined by the actual quotient cone, rather than a chosen arrow.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
def constantMap : constant.{c, a, w} J A ⟶ ring.{c, a, w} J A p :=
  limit.lift _ { pt := constant.{c, a, w} J A
                 π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj (constant.{c, a, w} J A))
                   (G := tower.{c, a, w} J A p) (quotient.{c, a, w} J A p)
                   (quotient_compatible.{c, a, w} J A p) }

/-- The constant uniformizer gives a compatible family of completed sections.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site).
Proof: naturality of the constant sheafification unit and of constantMap identifies
restriction of the section at U with the section at V. -/
theorem uniformizer_natural {U V : Cᵒᵖ} (f : U ⟶ V) :
    (ring.{c, a, w} J A p).obj.map f
      ((constantMap.{c, a, w} J A p).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj
          (CommRingCat.of (ULift.{max c w} A)))).app U (ULift.up p))) =
    (constantMap.{c, a, w} J A p).hom.app V
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{max c w} A)))).app V (ULift.up p)) := by
  sorry

/-- The image of the constant chosen uniformizer, including on the empty site.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: def-a1-completed-integral-small-site). -/
def uniformizer : ((ring.{c, a, w} J A p).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (constantMap.{c, a, w} J A p).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (ULift.{max c w} A)))).app U (ULift.up p)),
    fun f ↦ uniformizer_natural.{c, a, w} J A p f⟩

end WeilConjectures.CompletedSite
