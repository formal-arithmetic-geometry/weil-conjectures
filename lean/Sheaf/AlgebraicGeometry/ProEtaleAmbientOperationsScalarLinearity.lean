/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Scalar linearity of ordinary unbounded pro-etale operations

Source: Stacks Project, dga.tex, Tag 09MK, definition-functor-linear-categories;
sites-modules.tex, Tags 03D3 and 04JC; derived.tex, Tag 070I.
The combined scalar refinement is agent supplied
(blueprint: lem-sbc-ambient-operations-scalar-linearity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Ordinary unbounded ringed operations are additive and linear over compatible scalars.
The existential linear structures are specified by their sectionwise action on every
module-sheaf morphism; the derived structures are exactly Mathlib's induced localization
structures. Thus no arbitrary scalar action on the derived categories is allowed.

Source: Stacks Project, Tag 09MK, definition-functor-linear-categories, with the
agent-supplied scalar refinement of Tags 03D3, 04JC and 070I
(blueprint: lem-sbc-ambient-operations-scalar-linearity).

Proof:
1. On every site object W, direct image evaluates a module at its base change W_U.
The compatibility equation identifies the two scalar actions there. Hence direct image
preserves sums and A-scalars sectionwise. Module-sheaf Hom groups carry the sectionwise
A-module structures obtained by restricting SheafOfModules.homLinear along aU and aV;
composition is bilinear (def-weil-linear-category).
2. For the underived adjunction P ⊣ G of def-weil-pbc-proetale-operations, the bijection
Phi(h) = G(h) composed with the unit is additive and A-linear by step 1. Unit naturality
identifies Phi(P(s)) with the unit composed with s. Apply injectivity of Phi to sums and
scalar multiples to prove P additive and A-linear.
3. Identified coefficients make P exact. The functor Lu* is its termwise derived functor.
Apply lem-cbc-exact-linear-derived-functor to P with the induced derived structures of
lem-weil-linear-abelian-derived-category. This proves both identities for Lu*.
4. In the ordinary unbounded derived adjunction L ⊣ D, the bijection
Psi(h) = L(h) followed by the counit is additive and A-linear by step 3 and bilinearity.
Counit naturality identifies Psi(D(s)) with s after the counit. Injectivity of Psi proves
both identities for Ru*. These are precisely def-weil-linear-functor. All objects and
morphisms lie in the full ordinary unbounded categories, with no completeness or
constructibility restriction and no linearity assumption on a choice of resolutions. -/
theorem proEtaleRingDerivedOperations_scalarLinearity
    (A : Type v) [CommRing A] {U V : Scheme.{u}} (f : U ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
    (aV : A →+* RingCat.sectionsSubring (RV.obj ⋙ forget₂ CommRingCat RingCat))
    (aU : A →+* RingCat.sectionsSubring (RU.obj ⋙ forget₂ CommRingCat RingCat))
    (hc : ∀ (a : A) (W : V.ProEt),
      (proEtaleRingDirectImageMap f RV RU c).hom.app (op W) ((aV a).val (op W)) =
        (aU a).val (op ((proEtaleBaseChange f).obj W))) :
    ∃ (lU : Linear A (proEtaleRingModules U RU))
      (lV : Linear A (proEtaleRingModules V RV)),
      (fun [_iU : Linear A (proEtaleRingModules U RU)]
        [_iV : Linear A (proEtaleRingModules V RV)] ↦
        (∀ (M N : proEtaleRingModules U RU) (h : M ⟶ N) (a : A)
          (W : U.ProEtᵒᵖ) (x : M.val.obj W),
          (a • h).val.app W x = (aU a).val W • h.val.app W x) ∧
        (∀ (M N : proEtaleRingModules V RV) (h : M ⟶ N) (a : A)
          (W : V.ProEtᵒᵖ) (x : M.val.obj W),
          (a • h).val.app W x = (aV a).val W • h.val.app W x) ∧
        (proEtaleRingDerivedPullback f RV RU c).Additive ∧
        Functor.Linear A (proEtaleRingDerivedPullback f RV RU c) ∧
        (proEtaleRingDerivedDirectImage f RV RU c).Additive ∧
        Functor.Linear A (proEtaleRingDerivedDirectImage f RV RU c))
        (_iU := lU) (_iV := lV) := by
  sorry

end AlgebraicGeometry.Scheme
