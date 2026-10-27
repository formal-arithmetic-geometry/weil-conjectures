/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RelativeSplitTorusInvariantAffines
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.AmpleIdealSection
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-! # Affine eigensection charts for a supplied linearized ample line

Source: Stacks Project, Properties, Tags 01Q3 and 01PV, combined with relative
split-torus invariant affine neighbourhoods and the normalized Laurent coaction.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

open scoped MonObj

namespace AlgebraicGeometry

/-- Evaluate the actual scheme action on a test scheme.
Source: the action in the normalized Laurent-coaction argument for Stacks 01Q3.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeLineAction {S : Scheme.{u}} {G : Grp (Over S)}
    (X : CategoryTheory.Mod (Over S) G.X) (Q : Over S) (g : Q ⟶ G.X) (x : Q ⟶ X.X) :
    Q ⟶ X.X :=
  lift g x ≫ (ModObj.smul (M := G.X) (X := X.X))

/-- Pull the supplied linearization back along `(g,x)` and identify its source
with `x^* L`. The target is `(gx)^* L`, with the usual forward action convention.
Source: normalized linearization in the Laurent-coaction argument for Stacks 01Q3.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeLineLift {S : Scheme.{u}} {G : Grp (Over S)}
    (X : CategoryTheory.Mod (Over S) G.X) (L : X.X.left.Modules)
    (theta : (Scheme.Modules.tensorPullback (snd G.X X.X).left).obj L ≅
      (Scheme.Modules.tensorPullback (ModObj.smul (M := G.X) (X := X.X)).left).obj L)
    (Q : Over S) (g : Q ⟶ G.X) (x : Q ⟶ X.X) :
    (Scheme.Modules.tensorPullback x.left).obj L ≅
      (Scheme.Modules.tensorPullback (relativeLineAction X Q g x).left).obj L :=
  eqToIso (congrArg
    (fun f : Q.left ⟶ X.X.left ↦ (Scheme.Modules.tensorPullback f).obj L)
    (congrArg (fun f : Q ⟶ X.X ↦ f.left) (lift_snd g x)).symm) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp
      (lift g x).left (snd G.X X.X).left).app L ≪≫
    (Scheme.Modules.tensorPullback (lift g x).left).mapIso theta ≪≫
    (Scheme.Modules.tensorPullbackSectionComp
      (lift g x).left (ModObj.smul (M := G.X) (X := X.X)).left).symm.app L

/-- The canonical tensor-power comparison, normalized on pure tensor sections.
Source: Stacks 01CD and 01CA, used in the tensor-power step of the 01Q3 argument.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeLinePowerComparison {Y Z : Scheme.{u}} (f : Y ⟶ Z) (L : Z.Modules) :
    ∀ n : ℕ, (Scheme.Modules.tensorPullback f).obj (L.tensorPow n) ≅
      ((Scheme.Modules.tensorPullback f).obj L).tensorPow n
  | 0 => @asIso _ _ _ _ (Scheme.Modules.tensorPullbackObjUnitToUnit f)
      (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).1
  | n + 1 => Classical.choose (Scheme.Modules.module_pullback_tensor f) L (L.tensorPow n) ≪≫
      (Iso.refl _ ⊗ᵢ relativeLinePowerComparison f L n)

/-- The actual pullback of a global section, using the normalized adjunction unit.
Source: Stacks 0096, as used in the all-algebras normalization for Stacks 01Q3.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeLinePullbackSection {Y Z : Scheme.{u}} (f : Y ⟶ Z) (L : Z.Modules)
    (s : Γ(L, ⊤)) : Γ((Scheme.Modules.tensorPullback f).obj L, ⊤) :=
  ((Scheme.Modules.tensorPullbackSectionAdjunction f).unit.app L).app ⊤ s

/-- The induced tensor-power linearization, formed using the existing canonical
power isomorphism and monoidal pullback comparisons, with no frame chosen.
Source: tensor-power step of the normalized Laurent-coaction argument for Stacks 01Q3.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeLinePowerLift {S : Scheme.{u}} {G : Grp (Over S)}
    (X : CategoryTheory.Mod (Over S) G.X) (L : X.X.left.Modules)
    (theta : (Scheme.Modules.tensorPullback (snd G.X X.X).left).obj L ≅
      (Scheme.Modules.tensorPullback (ModObj.smul (M := G.X) (X := X.X)).left).obj L)
    (Q : Over S) (g : Q ⟶ G.X) (x : Q ⟶ X.X) (n : ℕ) :
    (Scheme.Modules.tensorPullback x.left).obj (L.tensorPow n) ≅
      (Scheme.Modules.tensorPullback (relativeLineAction X Q g x).left).obj (L.tensorPow n) :=
  relativeLinePowerComparison x.left L n ≪≫
    PGLLinearization.powerIso (relativeLineLift X L theta Q g x) n ≪≫
    (relativeLinePowerComparison (relativeLineAction X Q g x).left L n).symm

/-- The weight-w Laurent monomial on the rank-one relative split torus, evaluated
on an arbitrary test scheme. Its value at a unit t is t^w, including negative w.
It is obtained from the actual basis element of the torus's defining group algebra.
Source: Laurent weights in the normalized-coaction argument for Stacks 01Q3.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover). -/
def relativeTorusWeight (S : Scheme.{u}) (Q : Over S)
    (g : Q ⟶ (relativeSplitTorus S 1).X) (w : ℤ) : Γ(Q.left, ⊤) :=
  (g.left ≫ pullback.fst
    ((hopfSpec Γ(S, ⊤)).obj
      (op (CommHopfAlgCat.of Γ(S, ⊤)
        (AddMonoidAlgebra Γ(S, ⊤) (Fin 1 → ℤ))))).X.hom S.toSpecΓ).appTop
    ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra Γ(S, ⊤) (Fin 1 → ℤ)))).inv
      (AddMonoidAlgebra.single (fun _ : Fin 1 ↦ w) (1 : Γ(S, ⊤))))

/-- Every point lies in an affine invariant nonvanishing locus of an eigensection
of a positive power of the supplied ample line. The section identity is tested on
all schemes over Spec A, so in particular it is an equality on X_B for every
A-algebra B, with no flatness or reducedness assumption. In forward form it is
`theta_(g,x)(s(x)) = g^w s(gx)`; replacing x by g⁻¹y gives exactly
`(g • s_B)(y) = theta_(g,g⁻¹y)(s_B(g⁻¹y)) = g^w s_B(y)`.

Source: Stacks 01Q3, ideal-section argument; 01PV; normalized Laurent coaction.
(blueprint: lem-sfb-linearized-ample-eigen-affine-cover).

Proof:
1. If X is empty the assertion has no point to consider. Otherwise the Noetherian
   affine base and the relative split-torus invariant-affines theorem give an
   invariant affine neighbourhood U of the chosen point x
   (pqf-def-locnoeth; lem-sfb-relative-split-torus-invariant-affines).
2. Form the reduced closed boundary Z = X minus U and its quasi-coherent vanishing
   ideal. The ample ideal-section theorem gives a section u of a positive power
   of L vanishing on Z and nonzero at x
   (lem-weil-pbc-reduced-induced-closed-subscheme; lem-sc-ample-ideal-section).
3. Tensor the supplied linearization. The normalized Laurent section coaction
   writes u as a finite sum of weight sections u_w. Counitality gives the sum
   identity; coassociativity, by extracting Laurent coefficients, gives pure weight
   (lem-sfb-relative-linearized-line-sections-coaction).
4. Every u_w vanishes on Z: at z in Z evaluate the action of the indeterminate v
   over kappa(z)(v). Invariance keeps v⁻¹z outside U, hence the resulting Laurent
   polynomial is zero. Trivialize the residue-field line and compare coefficients.
   This uses no nonflat base-change isomorphism for global sections.
5. Since u(x) is nonzero, some coefficient s = u_w is nonzero at x. Its nonvanishing
   locus lies inside U and equals U intersect X_s, which is affine by 01PV
   (lem-sc-affine-cap-section-open; def-weil-pbc-ample-invertible-module).
6. The pure-weight coaction gives the displayed identity over every A-algebra.
   On the universal point of T times X_s, theta and the unit g^w preserve the
   generator criterion, so the action restricts to X_s scheme-theoretically.
   Inverses give equality of the two preimage opens, as asserted below. -/
theorem exists_linearized_ample_eigen_affine_neighbourhood
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (X : CategoryTheory.Mod (Over (Spec (.of A)))
      (relativeSplitTorus (Spec (.of A)) 1).X)
    [IsSeparated X.X.hom] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]
    (hnormal : ∀ p : X.X.left, IsDomain (X.X.left.presheaf.stalk p) ∧
      IsIntegrallyClosed (X.X.left.presheaf.stalk p))
    (L : X.X.left.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X.X.left L)
    (theta : (Scheme.Modules.tensorPullback
      (snd (relativeSplitTorus (Spec (.of A)) 1).X X.X).left).obj L ≅
        (Scheme.Modules.tensorPullback
          (ModObj.smul (M := (relativeSplitTorus (Spec (.of A)) 1).X) (X := X.X)).left).obj L)
    (hunit : ∀ (Q : Over (Spec (.of A))) (x : Q ⟶ X.X),
      HEq (relativeLineLift X L theta Q 1 x)
        (Iso.refl ((Scheme.Modules.tensorPullback x.left).obj L)))
    (hmul : ∀ (Q : Over (Spec (.of A)))
      (g h : Q ⟶ (relativeSplitTorus (Spec (.of A)) 1).X) (x : Q ⟶ X.X),
      HEq (relativeLineLift X L theta Q (g * h) x)
        (relativeLineLift X L theta Q h x ≪≫
          relativeLineLift X L theta Q g (relativeLineAction X Q h x)))
    (x : X.X.left) :
    ∃ (n : ℕ) (_ : 0 < n) (w : ℤ) (s : Γ(L.tensorPow n, ⊤)) (U : X.X.left.Opens),
      x ∈ U ∧ IsAffineOpen U ∧
      (U : Set X.X.left) = Scheme.Modules.nonvanishingLocus (L.tensorPow n) s ∧
      (ModObj.smul (M := (relativeSplitTorus (Spec (.of A)) 1).X) (X := X.X)).left ⁻¹ᵁ U =
        (snd (relativeSplitTorus (Spec (.of A)) 1).X X.X).left ⁻¹ᵁ U ∧
      ∀ (Q : Over (Spec (.of A)))
        (g : Q ⟶ (relativeSplitTorus (Spec (.of A)) 1).X) (y : Q ⟶ X.X),
        (relativeLinePowerLift X L theta Q g y n).hom.app ⊤
            (relativeLinePullbackSection y.left (L.tensorPow n) s) =
          relativeTorusWeight (Spec (.of A)) Q g w •
            relativeLinePullbackSection (relativeLineAction X Q g y).left (L.tensorPow n) s := by
  sorry

end AlgebraicGeometry
