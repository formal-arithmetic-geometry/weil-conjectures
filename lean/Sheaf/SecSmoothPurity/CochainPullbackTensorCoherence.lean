/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates

import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: lem-pur-cochain-pullback-tensor-coherence).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- The complete coherence conclusion: usual monoidal maps, composable ringed
morphisms and both canonical coefficient diagrams, including quotient transitions.  The
statement is independent of boundedness and flatness assumptions.
Source: Stacks 03EL, 07A4 and 0D6D
(blueprint: lem-pur-cochain-pullback-tensor-coherence). -/
def HasTensorCoherence (f : RingedPullback R S) (k : Comparison f) : Prop :=
  IsCoherent f k ∧
      (∀ {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
        {H : GrothendieckTopology E}
        [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
        {T : Sheaf H CommRingCat.{w}} (g : RingedPullback S T)
        (h : RingedPullback R T) (kg : Comparison g) (kh : Comparison h)
        (a : CompositePresentation f g h k kg kh),
        IsCompatibleWithComposition f g h k kg kh a) ∧
      (∀ (d : CoefficientSquare f) (k' : Comparison (changed f d)),
        IsCompatibleWithCoefficients f k d k')

/-- Signed cochain tensor comparison, composition, and coefficient coherence.
Source: Stacks 07A4, 03EL, and 0D6D
(blueprint: lem-pur-cochain-pullback-tensor-coherence).

Proof:
1. Use the normalized ordinary comparison of
   lem-weil-pbc-ringed-topoi-module-pullback-tensor on each pair of degrees.
   The adjunction lem-weil-pbc-ringed-topoi-module-adjunction preserves the full
   coproduct indexed by p+q=n. This gives c and its scalar-contraction inverse.
2. Naturality of the ordinary comparison commutes with d_P and d_Q; additivity
   preserves the factor (-1)^p in def-pc-tensor-complex-sheaves. Thus c is a chain map.
3. The insertion/contraction composites are identities on pure tensors.
   The sheaf tensor universal property lem-pc-sites-sheaf-tensor-bilinear-universal
   extends this equality and the two-variable naturality to sheaf morphisms.
4. On triple homogeneous tensors, the associator routes insert the same units.
   The braiding routes have the same (-1)^(pq); the two action-unit routes multiply
   by the same scalar. Use lem-pc-sheaf-modules-tensor-closed and total-tensor signs.
5. Use def-weil-pbc-composite-adjunction and
   lem-weil-pbc-conjugate-iso-unit-equation to identify a with scalar association.
   Both tensor routes then insert the same units and multiply the same scalars.
6. The compatible coefficient square makes kappa balanced. On generalized pure
   tensors the first equation sends s' tensor ((x tensor y) tensor 1) to
   ((1 tensor x) tensor s') tensor ((1 tensor y) tensor 1) by either route.
   For the second, both routes send s tensor (x tensor y) to
   (bar(s) tensor (x tensor 1)) tensor (1 tensor (y tensor 1)). Sheafification
   extends equality; tau is S-linear only after restriction of scalars as displayed.
7. These are degreewise calculations on the full coproduct, with no boundedness
   or flatness restriction. Apply the transition equation at each m >= n of a
   quotient tower; it asserts commutation with transitions, with no inverse claimed.
-/
theorem cochainPullbackTensorCoherence (f : RingedPullback R S) (k : Comparison f) :
    HasTensorCoherence.{w, uC, vC, uD, vD, uE, vE} f k := sorry

end CategoryTheory.CochainPullback

universe r m t
namespace CategoryTheory.CochainPullback

/-- The common theorem `cochainPullbackTensorCoherence` at the sectionwise ULift
coefficient rings of `SheafOfModules.CochainUniverseTransport.ring`, for ring sheaves
given in a universe r and the ambient universe max r m t. The ambient universe may be
enlarged by t to make either site essentially small; neither site object universe nor
either Hom universe is identified with it. This statement concerns modules over the
lifted rings only. Modules in their original size are compared with these through the
transport functor of def-pur-cochain-coefficient-universe-transport, which is not
part of this statement.
Source: Stacks 03DA, 03EL, 07A4 and 0D6D
(blueprint: lem-pur-cochain-pullback-tensor-coherence).
Proof: this is `cochainPullbackTensorCoherence` with w = max r m t, the sites C₀, D₀
and the lifted rings; the seven proof steps above apply verbatim. -/
theorem cochainPullbackTensorCoherenceOfUniverses
    {C₀ : Type uC} [Category.{vC} C₀] [EssentiallySmall.{max r m t} C₀]
    {D₀ : Type uD} [Category.{vD} D₀] [EssentiallySmall.{max r m t} D₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    (R₀ : Sheaf J₀ CommRingCat.{r}) (S₀ : Sheaf K₀ CommRingCat.{r})
    (f : RingedPullback.{max r m t, uC, vC, uD, vD}
      (SheafOfModules.CochainUniverseTransport.ring.{uC, vC, r, m, t} R₀)
      (SheafOfModules.CochainUniverseTransport.ring.{uD, vD, r, m, t} S₀))
    (k : Comparison.{max r m t, uC, vC, uD, vD} f) :
    HasTensorCoherence.{max r m t, uC, vC, uD, vD, uE, vE} f k := sorry

end CategoryTheory.CochainPullback
