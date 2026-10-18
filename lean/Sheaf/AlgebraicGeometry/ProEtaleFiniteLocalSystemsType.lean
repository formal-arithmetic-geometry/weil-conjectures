/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Clopen decomposition by the module model of a pro-etale local system

Source: Weil blueprint, main-20261015, sec-proetale-coefficients,
`sk-prop-pe-finite-local-systems/sk-prop-pe-finite-local-systems-type.md`
(blueprint: det-pe-finite-local-systems-type).

The models are modules over the universe lift of the discrete coefficient ring.
Restriction to a piece is expressed on covering objects over that open in the
original small pro-etale site, using the recorded localized module construction.
-/

@[expose] public section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite-presentation local system decomposes its base by its constant module model.
Source: Weil blueprint, main-20261015, sec-proetale-coefficients,
`sk-prop-pe-finite-local-systems-type.md`
(blueprint: det-pe-finite-local-systems-type).

Proof, following the node's eight steps:
1. The comparison adjunction and the constant-sheaf adjunction identify comparison
pullback of a constant set sheaf with the pro-etale constant sheaf, normalized on
coefficient sections (`def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-constant-sheaf-maps-global-sections`).
2. The comparison section formula and constant-sheaf pullback identify its sections
on V with etale constant-sheaf sections on V, naturally under restriction
(`lem-cbc-comparison-pullback-sections`,
`lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`).
3. Represent constants by the coproduct of copies of V. Its morphisms are locally
constant functions on V; restriction is composition with the underlying map.
Module operations are pointwise (`lem-galois-constant-sheaf-sets-representable`,
`lem-galois-coproduct-copies-morphisms-clopen`).
4. Choose the finite-presentation trivializing cover and replace each model by its
unique representative. Restrict its actual isomorphisms on overlaps
(`def-weil-proetale-locally-constant-sheaf`, `def-pur-localized-ringed-site`).
5. On a nonempty overlap, the composition-compatible constant Hom identification
in `det-pe-finite-local-systems-hom` evaluates inverse sheaf maps to inverse
module maps. Thus two representative labels coincide.
6. Glue the labels as sections of the constant representative sheaf, using the
sheaf equalizer. On an empty overlap there is a unique section, because its empty
cover is fpqc (`def-weil-pbc-sites-and-cohomology`, `sk-def-pe-site`,
`def-weil-pbc-fpqc-covering`).
7. The resulting locally constant function has disjoint clopen fibres covering X.
Give them the open subscheme structures. Their inclusions exhibit X as their
scheme coproduct (`def-weil-open-immersion`,
`lem-galois-coproduct-copies-morphisms-clopen`, `lem-weil-pbc-scheme-coproduct-family`).
8. Base change the original cover to each fibre. On nonempty members the model
label equals that fibre's label. Empty members have the unique module sheaf, so
also admit the required trivialization. Restricting the actual isomorphisms gives
the displayed cover and localized constant-model isomorphisms
(`def-weil-pbc-sites-and-cohomology`, `def-pur-localized-ringed-site`,
`def-weil-proetale-locally-constant-sheaf`). -/
theorem finiteLocalSystemsType (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))))
    (hF : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X Λ
      (fun M ↦ Module.FinitePresentation (ULift.{t + 1, u} Λ) M) F)
    (R : Type v) (model : R → ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ))
    (hmodel : ∀ r : R, Module.FinitePresentation (ULift.{t + 1, u} Λ) (model r))
    (hrep : ∀ M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ),
      Module.FinitePresentation (ULift.{t + 1, u} Λ) M →
        ∃! r : R, Nonempty (M ≅ model r)) :
    ∃ U : R → X.Opens,
      IsClopenDecomposition X R U ∧
      Nonempty (IsColimit (Cofan.mk X (fun r : R ↦ (U r).ι))) ∧
      ∀ r : R, ∃ (I : Type (t + 1)) (V : I → X.ProEt)
        (f : ∀ i : I, V i ⟶ ProEt.mk (U r).ι),
        Presieve.ofArrows V f ∈ (ProEt.precoverage X).coverings _ ∧
          ∀ i : I,
            Nonempty (F.over (V i) ≅
              proEtaleConstantModuleSheafOverOfUniverses X Λ (V i) (model r)) := by
  sorry

end AlgebraicGeometry.Scheme
