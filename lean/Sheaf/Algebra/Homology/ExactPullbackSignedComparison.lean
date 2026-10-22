/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Exact pullback and the normalized signed derived tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 06YS, 0G7E and 07A4;
sites-modules.tex, Tags 05VD and 03EL; derived.tex, Tag 015F;
more-algebra.tex, Tags 0FNG and 0FNH.
(blueprint: lem-pur-exact-pullback-signed-comparison).

The tensor and its representative isomorphisms are the published K-flat descent.
The helper structure records just the normalized associativity and symmetry maps
mentioned in the statement, on that same tensor; it does not choose another tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace SheafOfModules.ExactPullbackSigned

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso
attribute [local irreducible] IsNormalized HasCanonicalTensorShifts
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{wR} (Modules R)]

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Evaluation of the existing K-flat-derived tensor, without changing its data.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev tensor (A B : DerivedCategory (Modules R)) := ((derivedTensor R).obj A).obj B

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The existing derived bifunctor applied to a pair of morphisms.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev tensorMap {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B') :=
  (Functor.uncurry.obj (derivedTensor R)).map (Prod.mkHom a b)

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The composite signed two-input shift: extract the first shift, then the second.
The first total shift is unsigned; the second contributes (-1)^(bp) on an original
first-factor degree p. The final inverse addition comparison combines [b][a] to [a+b].
Source: Stacks 0FNH, item-shift-tensor
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def tensorShift [(derivedTensor R).CommShift₂Int]
    (a b : ℤ) (A B : DerivedCategory (Modules R)) :
    tensor R (A⟦a⟧) (B⟦b⟧) ≅ (tensor R A B)⟦a + b⟧ :=
  (((derivedTensor R).flip.obj (B⟦b⟧)).commShiftIso a).app A ≪≫
    (shiftFunctor _ a).mapIso (((derivedTensor R).obj A).commShiftIso b |>.app B) ≪≫
    ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (tensor R A B)).symm

set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Natural derived reassociation and symmetry, fixed by their total-complex models.
The equations use the actual unsigned cochain associator and Koszul braiding.
Thus these are the prescribed constraints of the existing tensor, not arbitrary maps.
Source: Stacks 07A4 and more-algebra.tex, 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
structure TensorConstraints where
  sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A
  sigma_natural : ∀ {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B'),
    tensorMap R a b ≫ (sigma A' B').hom = (sigma A B).hom ≫ tensorMap R b a
  alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)
  alpha_natural : ∀ {A A' B B' N N' : DerivedCategory (Modules R)}
    (a : A ⟶ A') (b : B ⟶ B') (n : N ⟶ N'),
    tensorMap R (tensorMap R a b) n ≫ (alpha A' B' N').hom =
      (alpha A B N).hom ≫ tensorMap R a (tensorMap R b n)
  sigma_model : ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    (representativeIso R P Q hp hq hf hg).hom ≫
        (sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (representativeIso R Q P hq hp hg hf).hom
  alpha_model : ∀ (P Q N : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hn : N.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n))
    (hi : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (N.X n)),
    ∃ (hpq : CochainComplex.IsKFlatIndependentCoefficients (((totalTensor R).obj P).obj Q))
      (hqn : CochainComplex.IsKFlatIndependentCoefficients (((totalTensor R).obj Q).obj N))
      (hfpq : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
        ((((totalTensor R).obj P).obj Q).X n))
      (hfqn : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
        ((((totalTensor R).obj Q).obj N).X n)),
      (representativeIso R (((totalTensor R).obj P).obj Q) N hpq hn hfpq hi).hom ≫
          tensorMap R (representativeIso R P Q hp hq hf hg).hom (𝟙 _) ≫
          (alpha (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
            (DerivedCategory.Q.obj N)).hom =
        DerivedCategory.Q.map (HomologicalComplex.associator P Q N).hom ≫
          (representativeIso R P (((totalTensor R).obj Q).obj N) hp hqn hf hfqn).hom ≫
          tensorMap R (𝟙 _) (representativeIso R Q N hq hn hg hi).hom

variable {R}
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} f)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The exact derived functor, with both derived-category universes fixed by its type.
Source: Stacks 015F (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev exactDerivedFunctor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S) :=
  f.L.mapDerivedCategory

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The existing exact-functor factorization, with its source and target fixed explicitly.
Source: Stacks 015F (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev exactFactorization : DerivedCategory.Q ⋙ exactDerivedFunctor f ≅
    pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q :=
  f.L.mapDerivedCategoryFactors

variable (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The prescribed normalization eta followed by kappa equals epsilon on resolving models.
Source: Stacks 06YY and derived.tex, 015F
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def IsNormalizedIdentification (eta : L ≅ (exactDerivedFunctor f)) : Prop :=
  ∀ (P : CochainComplex (Modules R) ℤ), P.IsKFlatIndependentCoefficients →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    eta.hom.app (DerivedCategory.Q.obj P) ≫ (exactFactorization f).hom.app P =
      epsilon.app P

attribute [local irreducible] IsNormalizedIdentification tensorShift

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Exact pullback identifies the canonical derived functor with exact localization,
and its uniquely normalized tensor comparison respects simultaneous signed shifts,
Koszul symmetry and unsigned reassociation, without boundedness assumptions.

Source: Stacks 015F, 06YY, 06YS, 0G7E, 05VD, 07A4, 03EL, 0FNG and 0FNH
(blueprint: lem-pur-exact-pullback-signed-comparison).

Proof plan (the node's ten steps):
1. lem-weil-pbc-exact-functor-derived-factorization supplies U, kappa and shifts.
   Additivity preserves (-1)^n d, so the termwise shift square is the identity.
2. lem-weil-pbc-ringed-topos-flat-module-pullback and the K-flat pullback lemma
   preserve the resolving class. The module adjunction and left-adjoint colimit
   lemma preserve every direct sum, and additivity preserves integer signs.
3. Choose a flat-term K-flat resolution P to A (lem-pc-kflat-resolution).
   Naturality of epsilon, exactness of F and invertibility of epsilon_P make
   epsilon_A invertible. Localization descends epsilon followed by kappa inverse
   and its inverse to a natural isomorphism eta.
4. Every object has a resolving representative; naturality along its invertible
   resolution map forces uniqueness of eta from its prescribed components.
5. Shift resolving complexes and compare the identity termwise shift maps.
   Uniqueness extends this square globally. At every degree-zero sheaf, including
   a nonflat one, the same epsilon equals eta followed by exact factorization.
6. Transport the normalized comparison of the shift-unit node through eta.
   Substitute epsilon_X = eta_X followed by kappa_X for X = P,Q,Tot(P,Q).
   Naturality cancels eta on the representative map, giving IsNormalized below.
   Tensor descent gives uniqueness among all natural comparisons.
7. On homogeneous degrees (p,q), both simultaneous-shift routes are
   (-1)^(bp) times (s tensor x) tensor (1 tensor y). Use total-tensor-integer-shifts.
8. The symmetry square reduces to cochain-pullback-tensor-coherence; both routes
   give (-1)^(pq) times (s tensor y) tensor (1 tensor x), using S-balancing.
9. kflat-total-tensor-model makes both triple totals resolving. Cancel their
   representative maps; cochain reassociation sends both routes to
   (s tensor x) tensor ((1 tensor y) tensor (1 tensor z)), with no extra sign.
10. Faithful restriction on resolving pairs from site-derived-tensor-descent
    extends the first two equations. Resolve three inputs and use naturality for
    associativity. All totals use direct sums, also for unbounded inputs.
-/
theorem exact_pullback_signed_comparison
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))) :
    ∃ (_ : L.CommShift ℤ) (_ : (derivedTensor R).CommShift₂Int)
      (_ : (derivedTensor S).CommShift₂Int),
      NatTrans.CommShift epsilon ℤ ∧
      HasCanonicalTensorShifts (R := R) ∧ HasCanonicalTensorShifts (R := S) ∧
      (∀ I : Type r, PreservesColimitsOfShape (Discrete I) f.L) ∧
      (∀ (M N : Modules R) (a : M ⟶ N) (z : ℤ),
        f.L.map (z • a) = z • f.L.map a) ∧
      (∀ M : Modules R, IsFlatOnSite (J := J) (R := R) M →
        IsFlatOnSite (J := K) (R := S) (f.L.obj M)) ∧
      (∀ P : CochainComplex (Modules R) ℤ, P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
        CochainComplex.IsKFlatIndependentCoefficients ((pull.{r, uC, vC, uD, vD} f).obj P) ∧
          ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pull.{r, uC, vC, uD, vD} f).obj P).X n)) ∧
      ∃ (eta : L ≅ (exactDerivedFunctor f)),
        IsNormalizedIdentification f L epsilon eta ∧
        (∀ eta' : L ≅ (exactDerivedFunctor f),
          IsNormalizedIdentification f L epsilon eta' → eta' = eta) ∧
        NatTrans.CommShift eta.hom ℤ ∧
        (∀ M : Modules R,
          eta.hom.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ≫
              (exactFactorization f).hom.app
                ((CochainComplex.singleFunctor (Modules R) 0).obj M) =
            epsilon.app ((CochainComplex.singleFunctor (Modules R) 0).obj M)) ∧
        ∃ (cR : TensorConstraints.{uC, vC, r, wR} R)
          (cS : TensorConstraints.{uD, vD, r, wS} S)
          (mu : Phi (exactDerivedFunctor f) ≅ Psi (exactDerivedFunctor f)),
          IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom mu.hom ∧
          (∀ tau : Phi (exactDerivedFunctor f) ⟶ Psi (exactDerivedFunctor f),
            IsNormalized f k (exactDerivedFunctor f) (exactFactorization f).hom tau →
              tau = mu.hom) ∧
          (∃ muL : Phi L ≅ Psi L, IsNormalized f k L epsilon muL.hom ∧
            ∀ A B : DerivedCategory (Modules R),
              mu.hom.app (A, B) = eta.inv.app (tensor R A B) ≫ muL.hom.app (A, B) ≫
                tensorMap S (eta.hom.app A) (eta.hom.app B)) ∧
          (∀ (a b : ℤ) (A B : DerivedCategory (Modules R)),
            mu.hom.app (A⟦a⟧, B⟦b⟧) ≫
                tensorMap S (((exactDerivedFunctor f).commShiftIso a).hom.app A)
                  (((exactDerivedFunctor f).commShiftIso b).hom.app B) ≫
                (tensorShift S a b ((exactDerivedFunctor f).obj A)
                  ((exactDerivedFunctor f).obj B)).hom =
              (exactDerivedFunctor f).map (tensorShift R a b A B).hom ≫
                ((exactDerivedFunctor f).commShiftIso (a + b)).hom.app (tensor R A B) ≫
                (mu.hom.app (A, B))⟦a + b⟧') ∧
          (∀ A B : DerivedCategory (Modules R),
            (exactDerivedFunctor f).map (cR.sigma A B).hom ≫ mu.hom.app (B, A) =
              mu.hom.app (A, B) ≫
                (cS.sigma ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)).hom) ∧
          (∀ A B N : DerivedCategory (Modules R),
            (exactDerivedFunctor f).map (cR.alpha A B N).hom ≫
                mu.hom.app (A, tensor R B N) ≫
                tensorMap S (𝟙 _) (mu.hom.app (B, N)) =
              mu.hom.app (tensor R A B, N) ≫
                tensorMap S (mu.hom.app (A, B)) (𝟙 _) ≫
                (cS.alpha ((exactDerivedFunctor f).obj A) ((exactDerivedFunctor f).obj B)
                  ((exactDerivedFunctor f).obj N)).hom) := by
  sorry

end SheafOfModules.ExactPullbackSigned
