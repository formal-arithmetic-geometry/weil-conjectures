/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite-presentation local systems and the pro-etale twist

Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- A pro-etale local system with finitely presented constant models.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`
(blueprint: det-pe-finite-local-systems-twist). -/
def IsFinitePresentationProEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  Scheme.IsLocallyConstantProEtaleFixedModuleSheaf X (ULift.{u + 1, u} Λ) F ∧
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
        ∀ i : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
            Nonempty (F.over (U i) ≅
              (constantSheaf ((Scheme.ProEt.topology X).over (U i))
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- An etale local system with finitely presented constant models.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`
(blueprint: det-pe-finite-local-systems-twist). -/
def IsFinitePresentationEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Module.FinitePresentation (ULift.{u + 1, u} Λ) M ∧
        Nonempty (G.over (𝒰.etalePrecoverageToEtale i) ≅
          (constantSheaf
            (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- A pro-etale local system whose displayed constant models are finite as sets.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`. -/
def IsFiniteModelProEtaleLocalSystem (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  Scheme.IsLocallyConstantProEtaleFixedModuleSheaf X (ULift.{u + 1, u} Λ) F ∧
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 X)),
      Presieve.ofArrows U f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
        ∀ i : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
          Finite M ∧
            Nonempty (F.over (U i) ≅
              (constantSheaf ((Scheme.ProEt.topology X).over (U i))
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-- An etale covering that trivializes a pro-etale sheaf after comparison.
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`. -/
def HasEtaleTrivializingCover (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ),
      Nonempty (F.over ((Scheme.toProEt X).obj (𝒰.etalePrecoverageToEtale i)) ≅
        (constantSheaf ((Scheme.ProEt.topology X).over
          ((Scheme.toProEt X).obj (𝒰.etalePrecoverageToEtale i)))
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))).obj M)

/-!
The twisting/descent statement. The final two conjunctions spell out the restriction
of the comparison adjunction to the two predicates: preservation in both directions,
full faithfulness on the etale objects, and invertible unit and counit.
-/
/--
Source: Stacks Project, Tag 099Y, `lemma-compare-locally-constant`; blueprint
`det-pe-finite-local-systems-twist`.

Proof sketch (for stage 3), following the node's proof steps. (1) Apply
`det-pe-finite-local-systems-type` and decompose `X` into open-and-closed pieces
on which one finitely presented model occurs; identify the pro-etale and etale
constant-model conventions using `det-pe-finite-local-systems-hom`,
`det-pe-classical-sheaves-modules`, `def-weil-pbc-sheafification`, and
`def-weil-pbc-constant-sheaf`. (2) On each piece form the sheaf of isomorphisms
from the constant model to `F`; verify the equalizer condition and its simply
transitive automorphism action, giving the torsor clauses of
`def-constructible-torsor`. (3) Use `det-pe-finite-local-systems-hom` to identify
the automorphism sheaf with the comparison inverse image of its etale version,
then apply `det-pe-torsor-comparison-glue` to obtain etale trivializations.
(4) Transport those trivializations to `X`, use
`lem-weil-pbc-slice-site-localization`,
`lem-weil-pbc-etale-site-localization-open`,
`lem-weil-proetale-weakly-etale-localization`, and
`lem-weil-pbc-site-constant-restriction` to lift overlap maps uniquely and prove
the cocycle. (5) Apply `lem-weil-pbc-site-module-sheaf-gluing` to glue the etale
models. (6) Pull the glued maps back, use the slice-localization identities, and
glue the local maps and inverses to obtain `comparisonUpperStar F₀ ≅ F`.
(7) Apply `det-pe-classical-sheaves-modules` and the comparison restriction
properties to obtain classicality, the etale trivializing cover, preservation in
both directions, full faithfulness, and the restricted unit/counit equivalence.
(8) For finite `Λ` and finite local models, present each model by the finite free
module on its underlying finite set; its kernel is finite, so the resulting
finite presentation proves the final implication using
`def-sc-finitely-presented-module`.
(blueprint: det-pe-finite-local-systems-twist)
-/
theorem finiteLocalSystemsTwist (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) :
    IsFinitePresentationProEtaleLocalSystem X Λ F →
      (∃ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G ∧
          Nonempty ((comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).obj G ≅ F)) ∧
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).obj F) ∧
      HasEtaleTrivializingCover X Λ F ∧
      (∀ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsFinitePresentationProEtaleLocalSystem X Λ
            ((comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).obj G)) ∧
      (∀ F' : Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationProEtaleLocalSystem X Λ F' →
          IsFinitePresentationEtaleLocalSystem X Λ
            ((comparisonLowerStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).obj F')) ∧
      (∀ G H : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsFinitePresentationEtaleLocalSystem X Λ H →
          Function.Bijective (fun φ : G ⟶ H ↦
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} Λ)) X).map φ)) ∧
      (∀ G : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationEtaleLocalSystem X Λ G →
          IsIso ((comparisonAdjunction (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).unit.app G)) ∧
      (∀ F' : Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
        IsFinitePresentationProEtaleLocalSystem X Λ F' →
          IsIso ((comparisonAdjunction (ModuleCat.{u + 1}
            (ULift.{u + 1, u} Λ)) X).counit.app F')) ∧
      (Finite Λ →
        ∀ F' : Sheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
          IsFiniteModelProEtaleLocalSystem X Λ F' →
            IsFinitePresentationProEtaleLocalSystem X Λ F') := by
  sorry

end AlgebraicGeometry.ProEtale
