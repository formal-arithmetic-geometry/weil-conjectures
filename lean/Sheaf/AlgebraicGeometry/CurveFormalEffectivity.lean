module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.PicardLift
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.Flat.FlatModulePowers
import WeilConjectures.Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Localization
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous

/-! # Effectivity of formal proper flat curves

Source: Stacks Project, quot.tex, Tag 0D58, lemma-curves-existence
(blueprint: lem-sfb-curve-formal-effectivity).

The index `n : ℕ` represents the positive order `n + 1`. Families are the existing
algebraic-space families, viewed over `Spec A`; this just remembers their composite
map to `Spec A`. Cartesian transition squares encode the specified base-change
isomorphisms. The concluding isomorphisms preserve the quotient bases and all these
specified transitions, rather than only identifying individual isomorphism classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveFamily

/-- The positive infinitesimal base `Spec(A / m^(n+1))`, with its canonical map to
`Spec A`. Source: Stacks, quot.tex, Tag 0D58, proof
(blueprint: lem-sfb-curve-formal-effectivity). -/
def effectivityBase (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Over (Spec (.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))

/-- The canonical adjacent quotient inclusion, as an arrow over `Spec A`.
Source: Stacks, quot.tex, Tag 0D58, proof
(blueprint: lem-sfb-curve-formal-effectivity). -/
def effectivityBaseStep (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    effectivityBase A n ⟶ effectivityBase A (n + 1) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) (Nat.le_succ (n + 1))))))
    (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1)

/-- The quotient-base inclusion into the terminal object of schemes over `Spec A`.
Source: Stacks, quot.tex, Tag 0D58, proof
(blueprint: lem-sfb-curve-formal-effectivity). -/
def effectivityBaseι (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    effectivityBase A n ⟶ Over.mk (𝟙 (Spec (.of A))) :=
  Over.mkIdTerminal.from (effectivityBase A n)

/-- Every specified formal system of flat proper finitely presented algebraic-space
curves over a complete Noetherian local ring is effective. Empty, zero-dimensional,
nonreduced and disconnected fibres are allowed, in every characteristic and with
arbitrary residue field.

Source: Stacks, quot.tex, Tag 0D58, lemma-curves-existence
(blueprint: lem-sfb-curve-formal-effectivity).

Proof:
1. Put k = A/m. Properness and the geometric dimension bound give dimension at most
   one for X_1 by lem-sfb-space-field-extension-dimension. The separated-space
   schematicity theorem lem-sfb-separated-space-dimension-one-scheme makes X_1 a scheme.
2. The cartesian transitions are quotient closed immersions by
   lem-weil-pbc-quotient-base-change-closed-immersion-ideal. Each X_n is a nilpotent
   thickening of X_1, so lem-sfb-thickening-of-scheme-space makes it a scheme too.
   Finite type over the Noetherian base makes these schemes Noetherian, by
   lem-weil-pbc-finite-type-over-noetherian. Their point spaces have dimension at most one.
3. Apply lem-sc-proper-dim-one-projective and
   lem-weil-pbc-projective-ample-invertible to choose an ample invertible module on X_1,
   also for the empty scheme.
4. Lift this module successively with lem-sc-pic-lift-closed-immersion-dim-le-one.
   Compose the adjacent pullback identifications recursively; associativity gives
   the cocycle identity at all nonadjacent orders. Only the first module must be ample.
5. Apply lem-sfb-polarized-formal-algebraization to get a proper scheme over A with
   compatible reductions. Invert its reduction isomorphisms to obtain the displayed e_n.
   Comparing both fibre-product projections gives exactly the last equation below.
   Properness gives quasi-compactness and separatedness; lem-pc-separated-quasi-separated
   and pqf-lem-lft-fp-locnoeth give finite presentation over the Noetherian base.
6. On each finite-type affine chart Spec B, B is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Quotient base change and
   lem-weil-pbc-flat-morphism-affine-criterion give flatness of B/m^n B over A/m^n.
   Apply lem-weil-pbc-flat-module-powers to B as a finite B-module. By
   lem-weil-pbc-affine-open-stalk-localization this gives flat stalks on the closed fibre.
7. By lem-weil-pbc-noetherian-flat-locus-neighborhood and
   lem-weil-pbc-flat-over-localization the flat locus is open and contains that fibre.
   Properness makes the image of its closed complement closed in Spec A. A nonempty
   closed subset of a local spectrum contains its closed point, so this image is empty.
   Thus the algebraized morphism is flat everywhere.
8. Apply lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous. The dimension-at-most-one
   locus contains the closed point, hence all of the local spectrum. Proper base change
   (lem-pc-proper-base-change) and lem-sfb-space-field-extension-dimension give the same
   bound on every geometric fibre. The resulting family is the required X. The adjacent
   compatibility equations compose to give compatibility with every specified transition.
-/
theorem formal_effectivity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : ∀ n : ℕ, ProperCurveFamily (effectivityBase A n))
    (i : ∀ n : ℕ, (X n).space.obj.obj ⟶ (X (n + 1)).space.obj.obj)
    (hcart : ∀ n : ℕ, IsPullback (i n) (X n).projection (X (n + 1)).projection
      (yoneda.map (effectivityBaseStep A n))) :
    ∃ Y : ProperCurveFamily (Over.mk (𝟙 (Spec (.of A)))),
      ∃ e : ∀ n : ℕ, pullback Y.projection (yoneda.map (effectivityBaseι A n)) ≅
          (X n).space.obj.obj,
        (∀ n : ℕ, (e n).hom ≫ (X n).projection =
          pullback.snd Y.projection (yoneda.map (effectivityBaseι A n))) ∧
        (∀ n : ℕ, (e n).inv ≫
            pullback.fst Y.projection (yoneda.map (effectivityBaseι A n)) =
          i n ≫ (e (n + 1)).inv ≫
            pullback.fst Y.projection (yoneda.map (effectivityBaseι A (n + 1)))) := by
  sorry

end AlgebraicGeometry.ProperCurveFamily
