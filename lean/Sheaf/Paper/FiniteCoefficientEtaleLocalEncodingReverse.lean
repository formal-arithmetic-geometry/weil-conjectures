/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.FiniteCoefficientSliceRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison

/-! # Reverse transport from fixed-scalar pro-etale models to etale finite models

Source: Stacks Project, proetale.tex, Tag 099Y; sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse).

This is the reverse direction of the local-model comparison. It is split from
`finiteCoefficient_etaleLocal_encoding` so that the descent from pro-etale
constant charts to etale charts can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Fixed-scalar pro-etale finite local models give etale finite local models.

Source: Stacks Project, proetale.tex, Tag 099Y, and sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse).

Proof: Restrict fixed-scalar charts to etale objects and use finite presentation
over the finite coefficient ring. Apply the coefficient-sized etale-cover theorem,
then transport the resulting charts through the normalized constant-module and
ringed-slice comparisons. -/
theorem finiteCoefficient_etaleLocal_encoding_reverse
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (V : X.Etale)
    (F : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    ProFiniteModels.fixedModels (ProEt.topology V.left) (ULift.{t + 1} B)
      ((finiteCoefficientSliceRestriction X B R φ V).obj F) → P F := by sorry

end AlgebraicGeometry.Scheme
