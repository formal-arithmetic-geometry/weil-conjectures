/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData
public import Sheaf.Algebra.Homology.KoszulRoosComparisonData
public import Sheaf.Algebra.Homology.KFlatScalarTowerRealization
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.FiniteFreeResolutionTensor
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients

/-! # Strict Koszul-to-quotient comparison on one resolution

Source: blueprint, sec-smooth-purity/sk-lem-sp-tower, reduction and completeness sentences;
Stacks Project, Tags 06YP, 06YQ, 06YT, 06YY, 0A0E and 0941
(blueprint: lem-sp-koszul-quotient-strict-resolution-bridge).

The existing scalar-first symmetric tensor models are used throughout. Index n denotes
power n+1. The scalar presentations and their normalization are the universal pairs of
the recorded change-of-rings interface, not extra flatness assumptions on coefficients.
Localization is `KFlatScalarTower.localize`, canonically compared to Q by
`DerivedCategory.quotientCompQhIso`. Roos coordinates below are ordered (v,u).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient SheafOfModules.KFlatScalarTower
open CategoryTheory.KoszulRoos (unitSection B quotient summand)

namespace CategoryTheory.KoszulQuotientStrictResolution

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- The left arrow of the span is tensoring the given resolution map with each Koszul
complex. Source: Stacks 06YP and 06YQ
(blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
def koszulSpanLeft (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections)
    {P M : CochainComplex (Modules R) ℤ} (f : P ⟶ M) :
    koszulTensorTower R P (unitSection R s) ⟶ koszulTensorTower R M (unitSection R s) :=
  Functor.whiskerLeft (principalKoszulTower R (unitSection R s))
    ((MonoidalCategory.curriedTensor (Modules R)).map₂CochainComplex.flip.map f)

/-- The recorded strict Roos construction applied to a tower of complexes.
Source: Stacks 0941 (blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
abbrev towerRoos (R : Sheaf J CommRingCat.{r})
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ) :=
  roosF.obj (koszulTowerComplex R T)

/-- Its functorial action on the actual strict tower map.
Source: Stacks 0941 (blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
def towerRoosMap (R : Sheaf J CommRingCat.{r})
    {T U : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ} (a : T ⟶ U) :
    towerRoos R T ⟶ towerRoos R U := roosF.map (koszulTowerComplexMap R a)

/-- The stipulated reordered coordinates (unshifted product, shifted product).
In these coordinates the differential is (dv,-du-(1-s)v).
Source: Stacks 0941 (blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
def coordinates (R : Sheaf J CommRingCat.{r})
    (T : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ) (q : ℤ) :
    (towerRoos R T).X (q + 1) ≅
      (roosP (koszulTowerComplex R T)).X (q + 1) ⊞
        (roosP (koszulTowerComplex R T)).X q :=
  roosχ (koszulTowerComplex R T) q ≪≫ biprod.braiding _ _

variable [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  (p : ∀ {A S : Sheaf J CommRingCat.{r}} (a : A ⟶ S), Presentation a)
  (N : Normalization p)
  (R : Sheaf J CommRingCat.{r})
  (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]

/-- One strict quotient tensor tower, computed using the same representative at every
level, with the normalized identity-on-sections coefficient transitions.
Source: Stacks 06YY (blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
def scalarTower (b : ∀ n : ℕ, B R s (n + 1) ⟶ B R s n)
    (h : ∀ n : ℕ, quotient R s (n + 1) ≫ b n = quotient R s n)
    (P : CochainComplex (Modules R) ℤ) : ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦
      ((ordinaryEnd p (quotient R s n)).mapHomologicalComplex (.up ℤ)).obj P)
    (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex
      (ordinaryStep p N (quotient R s (n + 1)) (b n) (quotient R s n) (h n))
      (.up ℤ)).app P)

/-- The canonical derived quotient tower, with transitions adjoint to scalar composition.
Source: Stacks 06YY and 07A6
(blueprint: lem-sp-koszul-quotient-strict-resolution-bridge). -/
def derivedScalarTower (b : ∀ n : ℕ, B R s (n + 1) ⟶ B R s n)
    (h : ∀ n : ℕ, quotient R s (n + 1) ≫ b n = quotient R s n)
    (M : CochainComplex (Modules R) ℤ) : ℕᵒᵖ ⥤ DerivedCategory (Modules R) :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ (derivedEnd p N (quotient R s n)).obj ((localize R).obj M))
    (fun n : ℕ ↦
    (derivedStep p N (quotient R s (n + 1)) (b n) (quotient R s n) (h n)).app
      ((localize R).obj M))

/-- The normalized strict span, its canonical component comparisons, and the exact
completion-unit identity, all on the originally supplied flat-term K-flat resolution.
The right arrow is pinned by its degree-zero unit and by vanishing on every other
Koszul-degree summand. These conditions specify precisely tensoring the quotient
augmentation, rather than an arbitrary quasi-isomorphism to a scalar-extension object.

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, reduction/completeness sentences;
Stacks 06YP, 06YQ, 06YT, 06YY, 0A0E, 0941
(blueprint: lem-sp-koszul-quotient-strict-resolution-bridge).

Proof plan:
1. Every power of monic multiplication by s is monic. The cone L_n has H^-1=0 and
   H^0=B_n; its augmentation is a quasi-isomorphism and commutes with (s,1) and
   quotient transitions (def-pur-principal-koszul-quotient-towers).
2. L_n is bounded finite free, hence K-flat by lem-sfb-ringed-finite-free-resolution-tensor.
   Apply lem-pur-kflat-tensor-quasiiso-independent in the other variable, using the
   signed interchange (-1)^(ab), to show that the left span arrow is a quasi-isomorphism.
   No K-flatness of M is used.
3. K-flatness of P makes tensoring the quotient augmentation a quasi-isomorphism.
   The existing scalar-first comparison identifies it with the right arrow; on degree
   zero it is the ordinary scalar unit and all other Koszul summands vanish.
4. Tensor naturality gives strict tower maps. The normalized K-flat counits of
   lem-pe-kflat-scalar-tower-realization give epsilon and the component isomorphisms.
   Its transition identity yields compatibility with every composite quotient transition.
5. Exact countable products and lem-weil-strict-roos-comparison make both Roos span
   arrows invertible after localization. Set sf to the inverse left arrow followed by
   the right arrow. Braiding roosχ gives the specified (v,u) coordinates.
6. The common strict augmentation wP has components 1 tensor p and zero shifted part.
   Strictly R(b)wP=uM f and R(a)wP=vP. Localize and cancel the left span arrow and e
   to obtain Q(uM) sf=e^-1 Q(vP).
7. Project to each unshifted coordinate. The result is e^-1 Q(p maps to 1 tensor p),
   and the unit normalization of lem-pe-kflat-scalar-tower-realization identifies this
   with the actual derived quotient unit. The normalized Roos comparison identifies
   these zero-shifted augmentations with the completion units themselves. The given P
   was used at all levels, without boundedness or derived completeness of M.
-/
theorem koszulQuotientStrictResolutionBridge
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)]
    (hreg : Mono (globalSectionMultiplication R (unitSection R s)))
    (M P : CochainComplex (Modules R) ℤ) (f : P ⟶ M)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i))
    (hf : QuasiIso f) :
    ∃ (b : ∀ n : ℕ, B R s (n + 1) ⟶ B R s n)
      (h : ∀ n : ℕ, quotient R s (n + 1) ≫ b n = quotient R s n)
      (a : koszulTensorTower R P (unitSection R s) ⟶ scalarTower p N R s b h P)
      (c : (Functor.const ℕᵒᵖ).obj P ⟶ scalarTower p N R s b h P)
      (e : (localize R).obj P ≅ (localize R).obj M),
      e.hom = (localize R).map f ∧
      (∀ n : ℕ, c.app (op n) =
        (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (quotient R s n)).unit
          (.up ℤ)).app P) ∧
      (∀ n : ℕ, koszulRepresentativeAugmentation R P (unitSection R s) n ≫
        a.app (op n) = c.app (op n)) ∧
      (∀ (n : ℕ) (i j : ℤ), i ≠ 0 →
        summand R s n P i j (i + j) rfl ≫ (a.app (op n)).f (i + j) = 0) ∧
      (∀ n : ℕ, QuasiIso ((koszulSpanLeft R s f).app (op n)) ∧
        QuasiIso (a.app (op n))) ∧
      ∃ (beta : ∀ n : ℕ,
          (localize R).obj ((koszulTensorTower R P (unitSection R s)).obj (op n)) ≅
            (localize R).obj ((koszulTensorTower R M (unitSection R s)).obj (op n)))
        (gamma : ∀ n : ℕ,
          (localize R).obj ((koszulTensorTower R M (unitSection R s)).obj (op n)) ≅
            (derivedEnd p N (quotient R s n)).obj ((localize R).obj M)),
        (∀ n : ℕ, (beta n).hom =
          (localize R).map ((koszulSpanLeft R s f).app (op n))) ∧
        (∀ n : ℕ, IsIso (epsilon p N (quotient R s n) P ((localize R).obj M) e)) ∧
        (∀ n : ℕ, (gamma n).hom ≫
          epsilon p N (quotient R s n) P ((localize R).obj M) e =
            (beta n).inv ≫ (localize R).map (a.app (op n))) ∧
        (∀ (n m : ℕ) (hnm : n ≤ m),
          (localize R).map ((koszulTensorTower R M (unitSection R s)).map
            (homOfLE hnm).op) ≫ (gamma n).hom =
              (gamma m).hom ≫ (derivedScalarTower p N R s b h M).map (homOfLE hnm).op) ∧
        ∃ (uM : M ⟶ towerRoos R (koszulTensorTower R M (unitSection R s)))
          (vP : P ⟶ towerRoos R (scalarTower p N R s b h P))
          (left : (localize R).obj
              (towerRoos R (koszulTensorTower R P (unitSection R s))) ≅
            (localize R).obj (towerRoos R (koszulTensorTower R M (unitSection R s))))
          (right : (localize R).obj
              (towerRoos R (koszulTensorTower R P (unitSection R s))) ≅
            (localize R).obj (towerRoos R (scalarTower p N R s b h P)))
          (sf : (localize R).obj
              (towerRoos R (koszulTensorTower R M (unitSection R s))) ≅
            (localize R).obj (towerRoos R (scalarTower p N R s b h P))),
          (∀ q : ℤ, uM.f (q + 1) ≫
            (coordinates R (koszulTensorTower R M (unitSection R s)) q).hom =
              biprod.lift ((Pi.lift
                (koszulRepresentativeAugmentation R M (unitSection R s))).f (q + 1)) 0) ∧
          (∀ q : ℤ, vP.f (q + 1) ≫
            (coordinates R (scalarTower p N R s b h P) q).hom =
              biprod.lift ((Pi.lift (fun n : ℕ ↦ c.app (op n))).f (q + 1)) 0) ∧
          left.hom = (localize R).map (towerRoosMap R (koszulSpanLeft R s f)) ∧
          right.hom = (localize R).map (towerRoosMap R a) ∧
          sf.hom = left.inv ≫ right.hom ∧
          (localize R).map uM ≫ sf.hom = e.inv ≫ (localize R).map vP ∧
          (∀ n : ℕ, (localize R).map uM ≫ sf.hom ≫
            (localize R).map (roosEval
              (koszulTowerComplex R (scalarTower p N R s b h P)) n) =
                e.inv ≫ (localize R).map (c.app (op n))) ∧
          (∀ n : ℕ, e.inv ≫ (localize R).map (c.app (op n)) =
            (N.adjunction (quotient R s n)).unit.app ((localize R).obj M) ≫
              epsilon p N (quotient R s n) P ((localize R).obj M) e) := by
  sorry

end CategoryTheory.KoszulQuotientStrictResolution
