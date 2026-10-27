/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.SmoothPurityTowerGammaData
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.SecSmoothPurity.FiniteGeneralRing

/-! # Invertibility of the finite purity word

Source: latest blueprint tower-geometric gamma proof (2).
(blueprint: lem-sp-finite-gamma-evaluation-isIso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerGamma
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The image of the finite ordinary purity map through the fixed site comparison
and right-adjoint identification is invertible on a retained constructible finite-Tor
input. This concerns a single level and asserts neither a tower map nor normalization.
Source: tower-geometric gamma proof (2), finite smooth-purity step
(blueprint: lem-sp-finite-gamma-evaluation-isIso).

Proof: the positive exponent is invertible on Y because ell differs from the
field characteristic. Its image is invertible in every stalk. Apply the library's
smooth_tensor_duality to the same finite quotient and smooth morphism; its tensor
map is exactly the second factor in finite gamma. The first factor is tensor of
alpha inverse, so is invertible for any supplied alpha. The unique right-adjoint
comparison and the site realization also preserve inverses. No input normalization
or ramification restriction is used. The n=0 exponent is ell > 0, and d=0 is included. -/
theorem finite_gamma_evaluation_isIso (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) 
    (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (dg : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)))
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n))
        (j ≫ p) ≅ Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n)
          (l ^ (n + 1)) (SpTowerP1.levelAnnihilates l E n) X d)
    (hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (_halpha : Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n)
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (SpTowerP1.levelAnnihilates l E n) (j ≫ p) d dg hX alpha)
    (K : SpTowerCalculus.C l E b q Y) :
    IsIso ((SpTowerP1.nu l E n X).map
      (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
        (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
          (SpTowerP1.levelAnnihilates l E n) X d) alpha
        ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
        (finiteRightComparison (SpTowerShriek.R l E n) j p
          (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _)) := by
  have hY : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)) :=
    (finiteGeneralRingPrimeSetting D l hne (n + 1) (Nat.succ_pos n)).diagonalExponent_isUnit
      (Y ↘ Spec (.of D.k))
  have ht := (Etale.smooth_tensor_duality (SpTowerP1.levelRing l E n)
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (SpTowerP1.levelAnnihilates l E n)
    (fun y ↦ by
      simpa only [map_natCast] using
        hY.map (Y.presheaf.germ ⊤ y (by trivial)).hom) (j ≫ p) d).2
  have := ht ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K))
  unfold Etale.FiniteSmoothPurity.gamma
  infer_instance

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
