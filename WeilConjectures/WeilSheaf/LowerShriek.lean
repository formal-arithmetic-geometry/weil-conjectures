/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Direct images with compact support of Weil sheaves and Weil complexes

Let `f : X ⟶ Y` be a separated quasi-compact morphism of `k₀`-schemes locally of finite type,
over a quasi-compact quasi-separated target, and `f̄ : X̄ ⟶ Ȳ` its base change to `k̄`. The
direct image with compact support `Rf₀!` of a Weil complex `(K, φ : Fr_X^* K ≅ K)` is the étale
`Rf̄_! K` (`AlgebraicGeometry.Etale.rightDerivedLowerShriek`, available by the Nagata
instance) with the Weil structure

`Fr_Y^* Rf̄_!(c) K ≅ Fr_Y^* Rf̄_!(c') K ≅ Rf̄_!(c) Fr_X^* K ≅ Rf̄_!(c) K`.

Here `c` is the chosen compactification of `f̄`. The Frobenii do not act on it, so the middle
isomorphism goes through the transported compactification `c'`
(`AlgebraicGeometry.Compactification.transport`), and the first one is the independence of
`Rf̄_!` of the compactification. The higher direct images `Rʳf₀!` of Weil sheaves are the
cohomology sheaves of `Rf₀!`.

That `Rf̄_!` preserves bounded constructible complexes is left as `sorry` in
`AlgebraicGeometry.WeilComplex.derivedLowerShriek`. Compactly supported cohomology is still a
placeholder with a `sorry` body; see `WeilConjectures.WeilSheaf.Defs`.

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

section GeometricFiber

namespace Scheme.Hom

variable {k : Type u} [Field k] {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of k))

/-- The projection of the geometric fiber to the model is affine, being the base change of
`Spec k̄ ⟶ Spec k`. -/
instance : IsAffineHom g.geometricFiberProj :=
  MorphismProperty.pullback_fst _ _
    (inferInstanceAs
      (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))

/-- The geometric fiber of a quasi-compact scheme is quasi-compact. -/
instance [CompactSpace Y₀] : CompactSpace g.geometricFiber :=
  QuasiCompact.compactSpace_of_compactSpace g.geometricFiberProj

/-- The geometric fiber of a quasi-separated scheme is quasi-separated. -/
instance [QuasiSeparatedSpace Y₀] : QuasiSeparatedSpace g.geometricFiber :=
  quasiSeparatedSpace_of_quasiSeparated g.geometricFiberProj

end Scheme.Hom

end GeometricFiber

section LowerShriek

open Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The derived lower shriek `Rf̄_!` along the base change `f̄ : X̄ ⟶ Ȳ` of a morphism of
`k₀`-schemes commutes with the derived pullbacks along the geometric Galois Frobenii:

`Rf̄_! ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rf̄_!`.

The Frobenii do not act on the chosen compactification `c` of `f̄`, so this passes through the
transported compactification `c' = (X̄ ⟶[Fr_X⁻¹ ≫ i] Z ⟶[g ≫ Fr_Y] Ȳ)`: it is the independence
isomorphism `Rf̄_!(c) ≅ Rf̄_!(c')` followed by
`Etale.rightDerivedLowerShriekOfCompactificationTransportIso`. -/
noncomputable def WeilComplex.rightDerivedLowerShriekFrobeniusIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    R(Scheme.Hom.geometricFiberMap f (comp_over f _))_![WeilCoefficients.{u} l] ⋙
        WeilComplex.frobeniusPullback k₀ l Y ≅
      WeilComplex.frobeniusPullback k₀ l X ⋙
        R(Scheme.Hom.geometricFiberMap f (comp_over f _))_![WeilCoefficients.{u} l] :=
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationIso _ _
        ((HasCompactification.compactification _).transport _ _
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius f (comp_over f _))))
      _ ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationTransportIso _ _ _ _ _

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The total derived direct image with compact support `Rf₀!` along a separated quasi-compact
morphism `f : X ⟶ Y` of `k₀`-schemes locally of finite type, over a quasi-compact
quasi-separated target: the derived lower shriek `Rf̄_!` along the base change
`f̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`WeilComplex.rightDerivedLowerShriekFrobeniusIso`.

That `Rf̄_!` preserves bounded constructible complexes is not proved yet: it is the
finiteness theorem (`sk-prop-sf-finiteness`), which the repository states for finite
coefficient rings only (`Etale.boundedConstructible_rightDerivedLowerShriek`). -/
noncomputable def WeilComplex.derivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (WeilComplex.rightDerivedLowerShriekFrobeniusIso k₀ l f))
    fun _ ↦ sorry

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The `r`-th higher direct image with compact support `Rʳf₀!` along a separated quasi-compact
morphism of `k₀`-schemes locally of finite type, over a quasi-compact quasi-separated target:
the `r`-th cohomology sheaf of `Rf₀!`, in cohomological indexing. -/
noncomputable def WeilSheaf.higherLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] (r : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.homologySheaf r

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (WeilComplex.derivedLowerShriek k₀ l f).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l X)
    (Q := WeilComplex.objectProperty k₀ l Y) _ _

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] (r : ℕ) :
    (WeilSheaf.higherLowerShriek k₀ l f r).Additive := by
  unfold WeilSheaf.higherLowerShriek
  infer_instance

end LowerShriek

section Cohomology

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-global-duality
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
