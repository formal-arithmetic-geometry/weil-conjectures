/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.AlgebraicGeometry.SupportCohomology

/-!
# Elementary shears of concrete supported Kummer products

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, paragraph "Elementary shears", and its
expanded DAG proof (blueprint: lem-pur-kummer-product-shear-homotopy).

The class K is the published `frameBoundaryProduct`, for arbitrary tuples, not
only frames. Its empty product is `frameEmptyClass`. The interpolation class
below is the same construction on the affine line. Isomorphisms over the ambient
scheme express equality of closed subschemes, retaining their ideal structures.
The section squares identify inverse-image supports before comparing classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Replace exactly the i-th entry by h_i + a h_j, keeping the ordered index set.
Source: blueprint shear paragraph (blueprint: lem-pur-kummer-product-shear-homotopy). -/
def kummerShearTuple {X : Scheme.{u}} {c : ℕ} (h : Fin c → Γ(X, ⊤))
    (i j : Fin c) (a : Γ(X, ⊤)) : Fin c → Γ(X, ⊤) :=
  fun b ↦ if b = i then h i + a * h j else h b

/-- The actual affine-line interpolation, using the standard coordinate t.
Source: blueprint shear paragraph (blueprint: lem-pur-kummer-product-shear-homotopy). -/
def kummerShearHomotopyTuple {X : Scheme.{u}} {c : ℕ} (h : Fin c → Γ(X, ⊤))
    (i j : Fin c) (a : Γ(X, ⊤)) :
    Fin c → Γ(AffineSpace (ULift.{u} (Fin 1)) X, ⊤) :=
  kummerShearTuple
    (fun b ↦ (AffineSpace (ULift.{u} (Fin 1)) X ↘ X).appTop (h b)) i j
    (AffineSpace.coord X (ULift.up (0 : Fin 1)) *
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X).appTop a)

/-- Pull back a concrete product representative through the published normalized
supported-Hom pullback. The Cartesian square specifies its inverse-image support;
the coefficient comparison is the canonical finite Tate comparison.
Source: blueprint shear paragraph, endpoint substitution
(blueprint: lem-pur-kummer-product-shear-homotopy). -/
def kummerTuplePullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} {c : ℕ}
    (aY : Y ⟶ Spec (.of P.field.k)) (hX : Fin c → Γ(X, ⊤))
    (hY : Fin c → Γ(Y, ⊤)) (v : X ⟶ Y)
    (g : X.zeroLocusSubscheme (Set.range hX) ⟶ Y.zeroLocusSubscheme (Set.range hY))
    (sq : ChosenCartesianSquare g (X.zeroLocusSubschemeι (Set.range hX))
      (Y.zeroLocusSubschemeι (Set.range hY)) v)
    (α : cupSupportedHom P (Y.zeroLocusSubschemeι (Set.range hY))
      ((cupSingle P Y).obj (P.frameTwist Y c)) (2 * (c : ℤ))) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range hX))
      ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) :=
  P.functorialCupPullback true (Y.zeroLocusSubschemeι (Set.range hY))
    (X.zeroLocusSubschemeι (Set.range hX)) v g sq aY (2 * (c : ℤ)) c α

/-- Eta is exactly the ordered product of the individual Kummer boundaries of H.
It is constructed for every tuple, with no smoothness or frame assumption on T.
Source: blueprint shear paragraph, interpolated class
(blueprint: lem-pur-kummer-product-shear-homotopy). -/
def kummerShearHomotopyClass (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) {c : ℕ} (h : Fin c → Γ(X, ⊤))
    (i j : Fin c) (a : Γ(X, ⊤)) :=
  P.frameBoundaryProduct (AffineSpace (ULift.{u} (Fin 1)) X)
    ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ aX) c
    (kummerShearHomotopyTuple h i j a)

/-- Canonically compare the sheared product with the original support. The
isomorphism is over X, so is uniquely determined by the two closed immersions.
This only transports the existing concrete class; it chooses no cohomology class.
Source: blueprint shear paragraph, equality C_h' = C_h
(blueprint: lem-pur-kummer-product-shear-homotopy). -/
def kummerShearedProduct (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) {c : ℕ} (h : Fin c → Γ(X, ⊤))
    (i j : Fin c) (a : Γ(X, ⊤))
    (e : X.zeroLocusSubscheme (Set.range (kummerShearTuple h i j a)) ≅
      X.zeroLocusSubscheme (Set.range h))
    (he : e.hom ≫ X.zeroLocusSubschemeι (Set.range h) =
      X.zeroLocusSubschemeι (Set.range (kummerShearTuple h i j a))) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range h))
      ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) :=
  (cupSingle P X).map
    (P.frameClosedCoefficientIso
      (X.zeroLocusSubschemeι (Set.range (kummerShearTuple h i j a)))
      (X.zeroLocusSubschemeι (Set.range h)) e he).inv ≫
    P.frameBoundaryProduct X aX c (kummerShearTuple h i j a)

/-- Elementary shear invariance, with the interpolation support and both endpoint
identities. The class K_X(h) is frameBoundaryProduct X aX c h, defined for every
ordered tuple, including c=0 (the unit with full support). The shear conclusion
requires c>=2 and i!=j. The maps g0 and g1 and their Cartesian squares are the
canonical inverse images of the interpolation support along the two sections.
Both endpoint classes are read on C_h using the displayed isomorphism e.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, "Elementary shears"
(blueprint: lem-pur-kummer-product-shear-homotopy).

Proof (the five steps of the node):
1. On Spec R, the ideals generated by h and h' agree: subtract a*h_j to
recover h_i, using i!=j. On Spec R[t], subtract t*a*H_j to see that (H)=I R[t].
These ideal equalities glue, giving e and eT over the ambient schemes.
2. On the complement of each V(H_b), H_b is a unit. Apply the concrete
frameKummer, then frameBoundary, and take the existing left-associated
frameBoundaryProduct. The twist is A(c): lem-pur-twist-sheaf-locally-free
identifies derived and ordinary tensors of the finite rank-one Tate lines.
The empty tuple gives the supported unit. No regularity of the tuple is used.
3. Evaluation at t=0 pulls H back to h; evaluation at t=1 pulls it back to h'.
Principal ideals and their complements pull back accordingly. The total
inverse-image ideal at either endpoint is I. These give the Cartesian squares.
4. Apply lem-pur-supported-cup-functoriality to each Kummer class and its
individual localization boundary (thm-pur-with-support-exactness), then induct
through the ordered left fold using cup naturality. There is no permutation
or sign. This gives the two displayed endpoint identities with canonical twists.
5. Apply lem-pur-supported-affine-line-homotopy to C_h in degree 2c and twist c.
Both section pullbacks are the inverse of projection pullback. They therefore
agree on eta. Combine with the endpoint identities to obtain the final equality.
An etale frame neighbourhood is a special case; T need not be a frame. -/
theorem kummerProduct_shear_homotopy (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) (_hc : 2 ≤ c)
    (h : Fin c → Γ(X, ⊤)) (i j : Fin c) (_hij : i ≠ j) (a : Γ(X, ⊤)) :
    ∃ (e : X.zeroLocusSubscheme (Set.range (kummerShearTuple h i j a)) ≅
        X.zeroLocusSubscheme (Set.range h))
      (he : e.hom ≫ X.zeroLocusSubschemeι (Set.range h) =
        X.zeroLocusSubschemeι (Set.range (kummerShearTuple h i j a))),
      (∃ eT : (AffineSpace (ULift.{u} (Fin 1)) X).zeroLocusSubscheme
          (Set.range (kummerShearHomotopyTuple h i j a)) ≅
          pullback (X.zeroLocusSubschemeι (Set.range h))
            (AffineSpace (ULift.{u} (Fin 1)) X ↘ X),
        eT.hom ≫ pullback.snd (X.zeroLocusSubschemeι (Set.range h))
            (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) =
          (AffineSpace (ULift.{u} (Fin 1)) X).zeroLocusSubschemeι
            (Set.range (kummerShearHomotopyTuple h i j a))) ∧
      ∃ (g0 g1 : X.zeroLocusSubscheme (Set.range h) ⟶
          (AffineSpace (ULift.{u} (Fin 1)) X).zeroLocusSubscheme
            (Set.range (kummerShearHomotopyTuple h i j a)))
        (sq0 : ChosenCartesianSquare g0 (X.zeroLocusSubschemeι (Set.range h))
          ((AffineSpace (ULift.{u} (Fin 1)) X).zeroLocusSubschemeι
            (Set.range (kummerShearHomotopyTuple h i j a)))
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X))
        (sq1 : ChosenCartesianSquare g1 (X.zeroLocusSubschemeι (Set.range h))
          ((AffineSpace (ULift.{u} (Fin 1)) X).zeroLocusSubschemeι
            (Set.range (kummerShearHomotopyTuple h i j a)))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) X)),
        P.kummerTuplePullback
            ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ aX) h
            (kummerShearHomotopyTuple h i j a)
            (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X) g0 sq0
            (P.kummerShearHomotopyClass aX h i j a) = P.frameBoundaryProduct X aX c h ∧
        P.kummerTuplePullback
            ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ aX) h
            (kummerShearHomotopyTuple h i j a)
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) X) g1 sq1
            (P.kummerShearHomotopyClass aX h i j a) =
          P.kummerShearedProduct aX h i j a e he ∧
        P.kummerTuplePullback
            ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ aX) h
            (kummerShearHomotopyTuple h i j a)
            (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X) g0 sq0
            (P.kummerShearHomotopyClass aX h i j a) =
          P.kummerTuplePullback
            ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫ aX) h
            (kummerShearHomotopyTuple h i j a)
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) X) g1 sq1
            (P.kummerShearHomotopyClass aX h i j a) ∧
        P.kummerShearedProduct aX h i j a e he = P.frameBoundaryProduct X aX c h := by
  sorry

end WeilConjectures.PurityFiniteSetting
