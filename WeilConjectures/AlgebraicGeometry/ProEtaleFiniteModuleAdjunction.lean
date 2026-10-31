/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExact

/-!
# The normalized finite-ring module adjunction

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
blueprint smooth purity, inverse image on the small pro-etale site
(blueprint: def-weil-proetale-inverse-image).

The existing inverse-image module and all its previous interfaces are reexported.
The additional adjunction uses the transported action for arbitrary finite rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1))
  [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]

/-- Direct image through the canonical coefficient map, also for noncommutative rings.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev finiteModulePushforward :
    FiniteCoefficientModules X A ⥤ FiniteCoefficientModules Y A :=
  SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (finiteCoefficientDirectImageMap f A)

set_option backward.isDefEq.respectTransparency.types false in
/-- The unique adjunction with the actual small-model module Kan-extension transpose.
The intermediate map g merely undoes scalar transport: it has exactly h's section maps.
The final formula is the specified model-site adjunction, evaluated on the original site.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-proetale-inverse-image).

Proof: first undo restriction along the inverse of the coefficient isomorphism c_f.
This changes no abelian groups or maps; a map linear for the transported action is linear
for the original action after restricting the target along c_f. Transport to the small
model and use the module pullback/pushforward adjunction there. Its coefficient map is
the ring inverse-image unit. Composing with c_f gives the original coefficient map,
by its definition as the ring adjunct. Hence the resulting target is the displayed
sectionwise direct image. The small-model equivalence preserves sections and maps.
These operations give natural inverse Hom bijections and thus the asserted adjunction.
The section formulas determine g uniquely and then determine every transpose, so they
determine the adjunction uniquely. No commutativity is used. -/
theorem finiteModuleAdjunction_existsUnique :
    ∃! adj : finiteCoefficientModulePullback f A ⊣ finiteModulePushforward f A,
      ∀ (M : FiniteCoefficientModules Y A) (N : FiniteCoefficientModules X A)
        (h : (finiteCoefficientModulePullback f A).obj M ⟶ N),
      ∃ g : (SheafOfModules.pullback.{u + 1} (finiteCoefficientModelRingUnit f A)).obj
          ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf Y A)).obj M) ⟶
          (Scheme.proEtaleModuleToModel (finiteCoefficientInverseRing f A)).obj
            ((SheafOfModules.restrictScalars (finiteCoefficientInverseImageMap f A)).obj N),
        (∀ (W : (Scheme.proEtaleSiteModel X)ᵒᵖ)
          (m : ((SheafOfModules.pullback.{u + 1} (finiteCoefficientModelRingUnit f A)).obj
            ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf Y A)).obj M)).val.obj W),
          g.val.app W m = h.val.app (AsSmall.down.op.obj W) m) ∧
        ∀ (W : Y.ProEtᵒᵖ) (m : M.val.obj W),
          (adj.homEquiv M N h).val.app W m =
            (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
              (finiteCoefficientModelRingUnit f A)).homEquiv _ _ g).val.app
                (AsSmall.up.op.obj W)) m := by
  sorry

/-- The canonical adjunction, determined uniquely by its small-model transpose.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-proetale-inverse-image). -/
noncomputable def finiteModuleAdjunction :
    finiteCoefficientModulePullback f A ⊣ finiteModulePushforward f A :=
  (finiteModuleAdjunction_existsUnique f A).choose

/-- Direct image is additive since its maps are precomposition of sectionwise linear maps.
Source: Stacks, Modules on Sites (blueprint: def-weil-proetale-inverse-image).
Proof: pushforward precomposes each sectionwise linear map with base change.
Addition of morphisms is sectionwise, and restriction of scalars changes no maps,
so pushforward preserves the sum of any two morphisms. -/
theorem finiteModulePushforward_additive : (finiteModulePushforward f A).Additive := by
  sorry

attribute [instance] finiteModulePushforward_additive

end AlgebraicGeometry.ProEtale
