/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Descent

/-!
# The character--Picard sequence of a multiplicative isogeny

Source: Milne, Algebraic Groups (2017), Proposition 18.18, sequence (129), p.391,
and the character descent convention on p.390
(blueprint: lem-sfb-character-picard-isogeny-sequence).

Characters are morphisms of Mathlib group objects into the recorded multiplicative group.
Picard classes and pullback are the existing scheme Picard constructions. The connecting
homomorphism is specified by its equivariant frame on every test scheme, so infinitesimal
kernels are included. All auxiliary constructions below belong to these canonical arrows.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {F : Type u} [Field F]

/-- Commutativity of the recorded Laurent Hopf group, Milne §12.a
(blueprint: lem-sfb-character-picard-isogeny-sequence). This exposes the existing
Mathlib instance through the recorded definition, without choosing a new group law. -/
noncomputable instance characterPicard_multiplicativeComm :
    IsCommMonObj (StandardGroupSchemes.multiplicative F) :=
  inferInstanceAs
    (IsCommMonObj ((Spec (.of (LaurentPolynomial F))).asOver (Spec (.of F))))

/-- Character precomposition as an additive homomorphism (Milne 18.18, p.391;
(blueprint: lem-sfb-character-picard-isogeny-sequence)). The law is pointwise
multiplication, written additively using `Additive`. -/
noncomputable def characterPicard_precomp
    {G H : Over (Spec (.of F))} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] :
    Additive (Grp.mk H ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
      Additive (Grp.mk G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :=
  ((yonedaGrpObj (Grp.mk (StandardGroupSchemes.multiplicative F))).map
    (Grp.ofHom f).op).hom.toAdditive

/-- The regular value of a multiplicative-group point, obtained by evaluating the Laurent
coordinate t (Milne §12.a; (blueprint: lem-sfb-character-picard-isogeny-sequence)). -/
noncomputable def characterPicard_value (T : Over (Spec (.of F)))
    (a : T ⟶ StandardGroupSchemes.multiplicative F) : Γ(T.left, ⊤) :=
  a.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
    (LaurentPolynomial.T 1))

/-- Pull a frame back to a test scheme and use the canonical comparison of iterated
pullbacks (Milne 18.11 and 18.18; (blueprint: lem-sfb-character-picard-isogeny-sequence)). -/
noncomputable def characterPicard_frame {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (e : (Scheme.Modules.pullback f).obj L ≅ 𝟙_ X.Modules)
    {T : Scheme.{u}} (g : T ⟶ X) :
    Γ((Scheme.Modules.pullback (g ≫ f)).obj L, ⊤) :=
  (((Scheme.Modules.pullbackComp g f).app L).hom).app ⊤
    (pullbackΓ g ((Scheme.Modules.pullback f).obj L)
      (e.inv.app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ 1)))

/-- A Picard class descends the character-equivariant trivial line. With the convention
`(g,z)n = (gn,χ(n)⁻¹z)`, its frame satisfies `s(gn) = χ(n)s(g)`.
The equality is imposed on every scheme-valued point, including nonreduced test schemes;
the pullback congruence transports both sections to the same module. Source: Milne
18.11, p.389, and 18.14--18.18, pp.390--391
(blueprint: lem-sfb-character-picard-isogeny-sequence). -/
def IsCharacterPicardDescentClass
    {G₁ G₀ : Over (Spec (.of F))} [GrpObj G₁] [GrpObj G₀]
    (f : G₁ ⟶ G₀) [IsMonHom f]
    (χ : Additive (Grp.mk (GrpObj.ker f) ⟶
      Grp.mk (StandardGroupSchemes.multiplicative F))) (c : Additive G₀.left.Pic) : Prop :=
  ∃ e : (Scheme.Modules.pullback f.left).obj
      ((fromSkeleton G₀.left.Modules).obj c.toMul.val) ≅ 𝟙_ G₁.left.Modules,
    ∀ (T : Over (Spec (.of F))) (g : T ⟶ G₁) (n : T ⟶ GrpObj.ker f)
      (h : (g * (n ≫ GrpObj.kerι f)).left ≫ f.left = g.left ≫ f.left),
      (((Scheme.Modules.pullbackCongr h).app
        ((fromSkeleton G₀.left.Modules).obj c.toMul.val)).hom).app ⊤
          (characterPicard_frame f.left _ e (g * (n ≫ GrpObj.kerι f)).left) =
        characterPicard_value T (n ≫ χ.toMul.hom.hom) •
          characterPicard_frame f.left _ e g.left

/-- Milne, Algebraic Groups (2017), Proposition 18.18, sequence (129), printed p.391,
specialized to a finite diagonalizable kernel
(blueprint: lem-sfb-character-picard-isogeny-sequence).

Proof plan:
1. Choose B₀ and put B₁ = f⁻¹B₀. The nodes
   lem-sfb-borel-characteristic-picard-sequence and
   lem-sfb-multiplicative-isogeny-borel-comparison supply exact characteristic rows
   and identify their flag quotients. They also give the short exact character
   sequence of B₀, B₁ and N.
2. Precomposition and pullback commute with restriction and the characteristic maps.
   Lift χ on N to λ on B₁ and set δχ = p₀c₁λ. Another lift differs by f_B*β;
   its contribution is p₀c₀β = 0. Lifting sums proves additivity.
3. The frame [g,1] satisfies [gn,1] = [g,λ(n)], scheme-theoretically. The identity
   G₁ × N ≅ G₁ ×[G₀] G₁ identifies this with the full character descent datum.
   The map f is fpqc (faithfully flat and affine), and lem-pc-fpqc-descent
   identifies its descended invertible module with p₀c₁λ.
4. Injectivity of the Borel character maps gives injectivity on group characters.
   A character restricting trivially to N lifts from B₀, and its zero characteristic
   class then lifts from G₀. This proves exactness at X*(G₁).
5. For χ = res λ, δχ = 0 precisely when c₁λ = c₀β; subtracting f_B*β shows
   χ comes from G₁. For a Picard class killed by f*, lift it to the common flag
   Picard group; its vanishing image lifts further to a B₁-character. Finally,
   surjectivity of the characteristic rows proves surjectivity of Picard pullback.
-/
theorem characterPicard_isogeny_sequence [IsAlgClosed F]
    (G₁ G₀ : Over (Spec (.of F))) [GrpObj G₁] [GrpObj G₀]
    [IsAffine G₁.left] [IsAffine G₀.left]
    [LocallyOfFiniteType G₁.hom] [QuasiCompact G₁.hom]
    [LocallyOfFiniteType G₀.hom] [QuasiCompact G₀.hom]
    [Smooth G₁.hom] [Smooth G₀.hom]
    [ConnectedSpace G₁.left] [ConnectedSpace G₀.left]
    (f : G₁ ⟶ G₀) [IsMonHom f]
    (hflat : f.left.appTop.hom.FaithfullyFlat)
    (hfinite : IsFinite (GrpObj.ker f).hom)
    (hdiag : ∃ (M : Type u) (_ : CommGroup M) (_ : Finite M),
      Nonempty (Grp.mk (GrpObj.ker f) ≅
        Grp.mk ((Spec (.of (MonoidAlgebra F M))).asOver (Spec (.of F))))) :
    ∃ δ : Additive (Grp.mk (GrpObj.ker f) ⟶
        Grp.mk (StandardGroupSchemes.multiplicative F)) →+ Additive G₀.left.Pic,
      (∀ χ, IsCharacterPicardDescentClass f χ (δ χ)) ∧
      Function.Injective (characterPicard_precomp f) ∧
      Function.Exact (characterPicard_precomp f) (characterPicard_precomp (GrpObj.kerι f)) ∧
      Function.Exact (characterPicard_precomp (GrpObj.kerι f)) δ ∧
      Function.Exact δ (Scheme.Pic.mapHom f.left).toAdditive ∧
      Function.Surjective (Scheme.Pic.mapHom f.left).toAdditive := by
  sorry

end AlgebraicGeometry
