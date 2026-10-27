/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R8
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
import Sheaf.SmoothPurity.FiniteP1CoordinateKernel
import Sheaf.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-! # Assembling the finite projective-line diagonal kernel

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
`thm-amb-p1-adjunction.proof.md`, unit construction and both triangles.
(blueprint: lem-sp-finite-p1-adjunction-of-integrals).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek
  SfDiagonalKernel.unit SfDiagonalKernel.counit

/-- Assemble a kernel adjunction while keeping its functors abstract. -/
private theorem kernelAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : SfDiagonalKernel.Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣
      CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B) := by
  obtain ⟨hl, hr⟩ := SfDiagonalKernel.triangles A k J hJ n e h
  exact ⟨{ unit := SfDiagonalKernel.unit A k
           counit := SfDiagonalKernel.counit A k
           left_triangle_components := hl
           right_triangle_components := hr }⟩

/-- Assemble the projective-line adjunction from a supplied base-compatible
finite-root splitting and its two supported diagonal integral identities.
Source: blueprint `thm-amb-p1-adjunction.proof.md`, the displayed unit and both
triangle computations, using the arbitrary-base integrals of
`sk-prop-sp-tower-geometric-p1.proof.md`.
(blueprint: lem-sp-finite-p1-adjunction-of-integrals).

Proof in words: write q for the projective-line projection. Reindex the standard
ULift (Fin 2) homogeneous coordinates by Option (ULift (Fin 1)); the induced
scheme isomorphism commutes with q. Transport the splitting, its trace, and the
supported diagonal class through that isomorphism. Both diagonal integrals
remain identities, by functoriality and cancellation of the comparison inverses.
The counit is inverse proper projection, then tensor with the supplied trace,
then the tensor-unit constraint. To construct the unit on any complex M, identify
M with Rp2_*Delta_*M using p2 Delta = id. The closed-immersion projection formula
identifies Delta_*M with Delta_*Lambda tensor p1^*M. Tensor the supported diagonal
class with p1^*M, push along p2, and apply inverse proper exchange to obtain
q^*Rq_*M tensor Lambda(1)[2]. These operations give natural transformations.
For the first triangle, proper exchange, direct-image composition and projection
naturality rewrite the composite as Rq_* of M tensored with the first diagonal
integral. The first integral identity makes it the identity. In the second
triangle the common coefficient p1^*q^*K = p2^*q^*K comes outside p2_* by proper
projection; the remaining kernel map is the second diagonal integral, hence the
identity. The trace base-change equation supplied by hbc identifies the traces
in these two computations with the chosen splitting traces. The shifted line
has even shift two, so moving its two copies past each other gives sign +1.
The two triangles produce the adjunction on all unbounded complexes. Finally
move the shift outside right tensor using derivedTensorRightShiftIso. No
normalized abstract twist, normalization comparison, or new splitting is used. -/
theorem nonempty_finiteP1AdjunctionOfIntegrals
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (t : OrdinaryFiniteTwistTransport Λ N hΛ)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting Λ N hΛ t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange Λ N hΛ t d)
    (hi : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      finiteP1DiagonalProperty Λ N hΛ t d T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    Nonempty (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
      L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        ((derivedTensor (ModuleCat.{u + 1} Λ)
          ℙ(Option (ULift.{u} (Fin 1)); S)).flip.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)) ⋙
          shiftFunctor _ (2 : ℤ))) := by
  obtain ⟨k, e, hik⟩ := finiteP1CoordinateKernel Λ N hΛ t d hbc hi S hS
  have hJ : Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine S N Λ hΛ) := by
    have hInv (s : S) : IsUnit (N : S.presheaf.stalk s) := by
      simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ s (by trivial)).hom
    obtain ⟨U, hU⟩ := Scheme.finiteEtaleTateLine_localTrivial S N hN hInv Λ hΛ
    exact ⟨U, hU⟩
  obtain ⟨adj⟩ := kernelAdjunction Λ k
    (Scheme.finiteEtaleTateLine S N Λ hΛ) hJ 1 e hik
  let adj' := adj.ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
      (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))
  let B := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)
  let symm := ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ)
    ℙ(Option (ULift.{u} (Fin 1)); S)).app (B⟦(2 : ℤ)⟧))
  let shift := derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ) B (2 : ℤ)
  exact ⟨adj'.ofNatIsoRight
    (Functor.isoWhiskerLeft _ (symm ≪≫ shift))⟩

end AlgebraicGeometry.Etale
