/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHomSpecified
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-!
# Support cohomology as exceptional Hom for the zero section

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
lem-pur-gysin-structure.proof.md, second paragraph (blueprint: lem-pur-gysin-support-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The supported-Hom map followed by the closed exceptional adjunction is bijective,
and degree-zero concentration identifies the resulting Hom with zeroth cohomology and
with global sections.

Proof, following the two DAG steps:

1. Apply [lem-pur-supported-hom], whose specified map is `supportedCohomologyHom`,
to the closed zero section, the degree-zero twisted coefficient, and degree two.
This identifies supported cohomology with maps from `s_*` of the coefficient unit.
By [lem-pur-closed-finite-adjoint-counit-transport], the proper compactification
`(id, s)` identifies this direct image with `Rs_!` with the transported counit.
The adjunction of [def-weil-exceptional-inverse-image] therefore identifies these
maps with maps from the unit to `Rs^!` of the shifted twist. The source has bounded
etale origin and the target is bounded below, as required by that adjunction.
The remaining shift and exact site-comparison isomorphisms give precisely
`gysinSupportToHom`; all factors are bijections, so their composite is bijective.

2. If `F` has no cohomology outside degree zero, canonical truncation gives
`F ≅ H^0(F)[0]` inducing the identity on `H^0`, by
[lem-sf-derived-concentrated-single]. Full faithfulness of the single-complex
embedding, [lem-weil-pbc-derived-single-fully-faithful], identifies morphisms to
this object with morphisms to `H^0(F)`. The inverse comparison
`singleFunctorCompHomologyFunctorIso.inv` identifies the source with the actual
coefficient unit, so this bijection is exactly the displayed map induced by `H^0`.
Evaluation on one identifies unit morphisms with global sections, by
[lem-pur-unit-hom-sections], with inverse sending a section `m` to `a ↦ a m`.
Specialize to `F = gysinValue` to obtain the bijectivity of `gysinHomToSections`.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/lem-pur-gysin-structure.proof.md, second paragraph (blueprint:
lem-pur-gysin-support-hom). -/
theorem gysin_support_hom (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    Function.Bijective (P.gysinSupportToHom h Y a) ∧
      (∀ (F : DerivedCategory (ProSheaves P Y)),
        (∀ r : ℤ, r ≠ 0 →
          IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) r).obj F)) →
        Function.Bijective (fun f :
            ((DerivedCategory.singleFunctor (ProSheaves P Y) 0).obj (P.constant Y) ⟶ F) =>
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ProSheaves P Y) 0).inv.app (P.constant Y) ≫
            (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).map f)) ∧
          ((∀ r : ℤ, r ≠ 0 →
              IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) r).obj
                (P.gysinValue h Y))) →
            Function.Bijective (P.gysinHomToSections h Y)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
