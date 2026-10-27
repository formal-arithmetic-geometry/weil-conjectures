module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.EtaleGeometricFibreCompactSections
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Extensive

/-! # Connected fibres after two-branch pinching

Source: literature/stacks-project/more-morphisms.tex, Agent connected-fibre consequence
of Tag 0E25 (proposition-pushout-along-closed-immersion-and-integral), quotient topology and
geometric branch pinching; old common-model step 10 (blueprint:
lem-sfb-proper-chain-pinching-connected-fibres).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite proper chain with geometrically connected fibres remains connected after
pinching two marked branches. The hypotheses spell out the projective flat nodal families,
the two-sheeted finite etale pinching datum, the cartesian pushout squares and their
geometric-fibre stability. The conclusion includes the length-zero and empty-marking cases.

Source: literature/stacks-project/more-morphisms.tex, Agent connected-fibre consequence of Tag 0E25
(proposition-pushout-along-closed-immersion-and-integral), quotient topology and geometric branch
pinching; old common-model step 10, including closed-image composition for proper chains.
(blueprint: lem-sfb-proper-chain-pinching-connected-fibres).

Proof (the six steps of the DAG node):
1. Composition gives properness of `h`, including the identity for `m = 0`, by
   lem-weil-pbc-proper-fp-permanence. By lem-kun-projective-implies-proper, `X` and `Y`
   are proper over the trait. In particular `X` is separated over it, and
   lem-weil-pbc-proper-over-separated makes the induced `p` proper.
2. For a field-valued point of `C`, base change the chain. Its initial scheme is the field
   spectrum. Each link is proper by lem-weil-pbc-proper-fp-permanence, with nonempty connected
   fibres by hypothesis; hence it is a closed surjection and gives the quotient topology.
   Apply lem-weil-pbc-connected-fibres-quotient-preimage-connected inductively to the whole
   connected target. This proves the field-valued fibres of `h` are nonempty connected.
3. At an algebraically closed point `x` of `X`, put `Z = Y ×_X Spec Ω` and
   `E = W ×_X Spec Ω`. The map `E → Z` is finite surjective by
   lem-weil-pbc-finite-morphism-permanence and lem-weil-pbc-surjective-base-change.
   Off `N`, the complement isomorphism identifies `C ×_X Spec Ω` with one point.
   Then `E` is a fibre from step 2 and its surjective image `Z` is connected and nonempty.
4. On `N`, the field-valued point factors through the closed immersion of `N`. By
   lem-weil-pbc-finite-proper and lem-sfb-etale-geometric-fibre-compact-sections, the
   degree-two etale fibre of `B → N` is two copies of `Spec Ω`. The cartesian square
   identifies `C ×_X Spec Ω` with it. By lem-sc-etale-fibre-product-base-change-coproduct,
   `E` splits into the corresponding two fibres of `h`, both connected and nonempty.
5. The two marked sections in `W` give a point in each piece of `E`; their images in `Z`
   coincide by the pushout relation. The two connected images meet and cover `Z`, so
   every clopen separation has one empty side. Thus `Z` is connected and nonempty.
6. Apply lem-weil-geometrically-connected-algebraic-closure to each residue-field fibre
   to get the all-extension assertion for `p`. Its base change to a geometric trait fibre
   is a proper surjection with connected fibres. The quotient-topology preimage lemma of
   step 2 now carries connectedness of `X`'s fibre to connectedness of `Y`'s fibre.
   With empty markings only step 3 occurs; length zero uses the initial case of step 2.
   No connectedness of `C`, `W`, or intermediate total fibres is used.
-/
theorem proper_chain_pinching_connected_fibres
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (C W B N X Y : Over (Spec (.of R)))
    [IsHProjective C.hom] [IsHProjective W.hom]
    [Flat C.hom] [Flat W.hom]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation W.hom]
    (hCnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty ↥(pullback C.hom g) ∧ IsReduced (pullback C.hom g) ∧
      (pullback C.hom g).IsPureDimension 1 ∧
      ∀ x : ↥(pullback C.hom g), IsClosed ({x} : Set ↥(pullback C.hom g)) →
        x ∉ (pullback.snd C.hom g).smoothLocus →
        Nonempty (NodalFiber.completedLocalRing x ≃+* NodalFiber.powerSeriesQuotient Ω))
    (hWnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty ↥(pullback W.hom g) ∧ IsReduced (pullback W.hom g) ∧
      (pullback W.hom g).IsPureDimension 1 ∧
      ∀ x : ↥(pullback W.hom g), IsClosed ({x} : Set ↥(pullback W.hom g)) →
        x ∉ (pullback.snd W.hom g).smoothLocus →
        Nonempty (NodalFiber.completedLocalRing x ≃+* NodalFiber.powerSeriesQuotient Ω))
    [IsFinite B.hom] [IsFinite N.hom] [Etale B.hom] [Etale N.hom]
    (q : B ⟶ N) [IsFinite q.left] [Etale q.left]
    (hqdeg : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ N.left),
      Nat.card ↥(pullback q.left z) = 2)
    (iC : B ⟶ C) (iW : B ⟶ W) [IsClosedImmersion iC.left] [IsClosedImmersion iW.left]
    (hiCsmooth : ∀ b : B.left, iC.left b ∈ C.hom.smoothLocus)
    (hiWsmooth : ∀ b : B.left, iW.left b ∈ W.hom.smoothLocus)
    (h : W ⟶ C) (hmarks : iW ≫ h = iC)
    (m : ℕ) (V : Fin (m + 1) → Scheme.{u})
    (hV0 : V 0 = C.left) (hVm : V (Fin.last m) = W.left)
    (v : ∀ j : Fin m, V j.succ ⟶ V j.castSucc)
    (cv : ∀ j : Fin (m + 1), V j ⟶ C.left)
    (hcv0 : cv 0 = eqToHom hV0)
    (hcvstep : ∀ j : Fin m, v j ≫ cv j.castSucc = cv j.succ)
    (hcvlast : cv (Fin.last m) = eqToHom hVm ≫ h.left)
    (hvproper : ∀ j : Fin m, IsProper (v j))
    (hvconnected : ∀ j : Fin m, GeometricallyConnected (v j))
    (c : C ⟶ X) (w : W ⟶ Y) (nX : N ⟶ X) (nY : N ⟶ Y) (p : Y ⟶ X)
    (hp : w ≫ p = h ≫ c) (hpN : nY ≫ p = nX)
    (hpushC : IsPushout iC.left q.left c.left nX.left)
    (hpushW : IsPushout iW.left q.left w.left nY.left)
    (hpullC : IsPullback iC.left q.left c.left nX.left)
    (hpullW : IsPullback iW.left q.left w.left nY.left)
    [IsHProjective X.hom] [IsHProjective Y.hom]
    [IsFinite c.left] [IsFinite w.left] [Surjective c.left] [Surjective w.left]
    [IsClosedImmersion nX.left] [IsClosedImmersion nY.left]
    (hcompC : ∃ (UX : X.left.Opens) (UC : C.left.Opens),
      (UX : Set X.left) = (Set.range nX.left)ᶜ ∧
      (UC : Set C.left) = (Set.range iC.left)ᶜ ∧
      c.left ⁻¹ᵁ UX = UC ∧ IsIso (morphismRestrict c.left UX))
    (hcompW : ∃ (UY : Y.left.Opens) (UW : W.left.Opens),
      (UY : Set Y.left) = (Set.range nY.left)ᶜ ∧
      (UW : Set W.left) = (Set.range iW.left)ᶜ ∧
      w.left ⁻¹ᵁ UY = UW ∧ IsIso (morphismRestrict w.left UY))
    (hpushCbase : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      IsPushout ((Over.pullback g).map iC).left ((Over.pullback g).map q).left
        ((Over.pullback g).map c).left ((Over.pullback g).map nX).left)
    (hpushWbase : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      IsPushout ((Over.pullback g).map iW).left ((Over.pullback g).map q).left
        ((Over.pullback g).map w).left ((Over.pullback g).map nY).left) :
    IsProper h.left ∧ GeometricallyConnected h.left ∧
      IsProper p.left ∧ GeometricallyConnected p.left ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
        ConnectedSpace ↥(pullback X.hom g) → ConnectedSpace ↥(pullback Y.hom g) := by
  sorry

end AlgebraicGeometry
