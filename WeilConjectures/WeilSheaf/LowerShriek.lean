/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Direct images with compact support of Weil sheaves and Weil complexes

Let `f : X ⟶ Y` be a separated quasi-compact morphism locally of finite type of `k₀`-schemes,
with `Y` of finite type and quasi-separated over `k₀`, and `f̄ : X̄ ⟶ Ȳ` its base change to
`k̄`. The direct image with compact support `Rf₀!` of a Weil complex `(K, φ : Fr_X^* K ≅ K)` is
the étale `Rf̄_! K` (`AlgebraicGeometry.Etale.rightDerivedLowerShriek`, available by the Nagata
instance) with the Weil structure

`Fr_Y^* Rf̄_!(c) K ≅ Fr_Y^* Rf̄_!(c') K ≅ Rf̄_!(c) Fr_X^* K ≅ Rf̄_!(c) K`.

Here `c` is the chosen compactification of `f̄`. The Frobenii do not act on it, so the middle
isomorphism goes through the transported compactification `c'`
(`AlgebraicGeometry.Compactification.transport`), and the first one is the independence of
`Rf̄_!` of the compactification. That `Rf̄_! K` is again bounded constructible is the
finiteness theorem
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_padicAlgCl`.
The higher direct images `Rʳf₀!` of Weil sheaves are the cohomology sheaves of `Rf₀!`.

Compactly supported cohomology is still a placeholder with a `sorry` body; see
`WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.WeilComplex.rightDerivedLowerShriekFrobeniusIso`:
  `Rf̄_! ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rf̄_!`.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`: the higher direct images with compact
  support `Rʳf₀!` and the total derived one `Rf₀!`.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

section LowerShriek

open Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The derived lower shriek `Rf̄_!` along the base change `f̄ : X̄ ⟶ Ȳ` of a morphism of
`k₀`-schemes commutes with the derived pullbacks along the geometric Galois Frobenii:
```
D(X̄) --Rf̄_!--> D(Ȳ)
  |               |
D(Fr_X^*)       D(Fr_Y^*)
  v               v
D(X̄) --Rf̄_!--> D(Ȳ)
```
-/
noncomputable def WeilComplex.rightDerivedLowerShriekFrobeniusIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    R(Scheme.Hom.geometricFiberMap f (comp_over f _))_![WeilCoefficients.{u} l] ⋙
        WeilComplex.frobeniusPullback k₀ l Y ≅
      WeilComplex.frobeniusPullback k₀ l X ⋙
        R(Scheme.Hom.geometricFiberMap f (comp_over f _))_![WeilCoefficients.{u} l] :=
  -- the independence isomorphism `Rf̄_!(c) ≅ Rf̄_!(c')` for the transported compactification
  -- `c' = (X̄ ⟶[Fr_X⁻¹ ≫ i] Z ⟶[g ≫ Fr_Y] Ȳ)`, followed by the transport isomorphism
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso _ _
        ((HasCompactification.compactification _).transport _ _
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius f (comp_over f _))))
      _ ≪≫
    rightDerivedLowerShriekOfCompactificationTransportIso _ _ _ _ _

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The total derived direct image with compact support `Rf₀!` along a separated quasi-compact
morphism `f : X ⟶ Y` locally of finite type of `k₀`-schemes, with `Y` of finite type and
quasi-separated over `k₀`: the derived lower shriek `Rf̄_!` along the base change
`f̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`WeilComplex.rightDerivedLowerShriekFrobeniusIso`. -/
noncomputable def WeilComplex.derivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (WeilComplex.rightDerivedLowerShriekFrobeniusIso k₀ l f))
    fun K ↦
      have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
        rw [← comp_over f]
        infer_instance
      boundedConstructible_rightDerivedLowerShriek_padicAlgCl l
        (by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]; exact Fact.out) _ _ _
        (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _) _ K.property

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The `r`-th higher direct image with compact support `Rʳf₀!` along a separated quasi-compact
morphism locally of finite type of `k₀`-schemes, with target of finite type and
quasi-separated over `k₀`: the `r`-th cohomology sheaf of `Rf₀!`, in cohomological
indexing. -/
noncomputable def WeilSheaf.higherLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.homologySheaf r

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerShriek k₀ l f).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l X)
    (Q := WeilComplex.objectProperty k₀ l Y) _ _

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) :
    (WeilSheaf.higherLowerShriek k₀ l f r).Additive :=
  inferInstanceAs (WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek k₀ l f ⋙
    WeilComplex.homologySheaf r).Additive

end LowerShriek

section Cohomology

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-global-duality
-- TODO: define this as the stalk over `Spec k̄` of the `r`-th cohomology of `Rf₀!` along the
-- structure morphism `X ⟶ Spec k₀` (`WeilComplex.derivedLowerShriek`).
/-- The compactly supported cohomology `H_c^r(X ⊗ k, K)` of a Weil complex, with its geometric
Frobenius. -/
noncomputable def WeilComplex.compactlySupportedCohomology (r : ℤ) (K : WeilComplex k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) := sorry

/-- The compactly supported cohomology `H_c^r(X ⊗ k, F)` of a Weil sheaf. -/
noncomputable def WeilSheaf.compactlySupportedCohomology (r : ℤ) (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (WeilSheaf.toComplex.obj F).compactlySupportedCohomology r

end Cohomology

end AlgebraicGeometry
