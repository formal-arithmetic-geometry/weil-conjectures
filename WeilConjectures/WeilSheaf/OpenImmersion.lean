/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Direct images of Weil sheaves along an open immersion

The ordinary direct image `j_*`, the higher direct images `Rⁱj_*`, the extension by zero `j_!`
and the canonical map `j_! ⟶ j_*` along an open immersion. Each is the corresponding functor on
étale sheaves along the base change `j̄ : Ū ⟶ X̄`, with the Weil structures transported along
the base change isomorphisms for the cartesian square of `j̄` and the geometric Frobenii
(`WeilConjectures.SixFunctors.BaseChange.GeometricFrobenius`). The higher direct images are
the cohomology sheaves of the derived pushforward `WeilComplex.rightDerivedLowerStar`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.higherDirectImage`: the higher direct images `Rⁱj_*`.
- `AlgebraicGeometry.WeilSheaf.directImage`, `AlgebraicGeometry.WeilSheaf.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.extensionByZeroToDirectImage`: the two extensions along an open
  immersion and the canonical map between them.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

open Etale

variable (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-boundary
/-- The *ordinary* sheaf direct image `j_*` along an open immersion `j`: the pushforward along
the base change `j̄ : Ū ⟶ X̄`, with the Weil structure transported along the base change
isomorphism `Etale.lowerStarGeometricFiberMapCompFrobeniusIso`. Its stalks at the missing
points are the inertia invariants. -/
noncomputable def directImage : WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.lowerStarGeometricFiberMapCompFrobeniusIso _ j (comp_over j _)))
    fun _ ↦ sorry

-- TODO(unify): sk-d-real-boundary
/-- The higher direct image `Rⁱj_*` along an open immersion `j`: the `i`-th cohomology sheaf
of the derived pushforward `Rj_*` of a Weil sheaf placed in degree zero. -/
noncomputable def higherDirectImage (i : ℕ) : WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  toComplex ⋙ WeilComplex.rightDerivedLowerStar j ⋙ WeilComplex.homologySheaf i

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- Extension by zero `j_!` along an open immersion `j`: the extension by zero along the base
change `j̄ : Ū ⟶ X̄`, with the Weil structure transported along the base change isomorphism
`Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def extensionByZero : WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso _ j (comp_over j _)))
    fun _ ↦ sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance : (directImage (k₀ := k₀) (l := l) j).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilSheaf.objectProperty k₀ l U)
    (Q := WeilSheaf.objectProperty k₀ l X) _ _

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance : (extensionByZero (k₀ := k₀) (l := l) j).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilSheaf.objectProperty k₀ l U)
    (Q := WeilSheaf.objectProperty k₀ l X) _ _

-- TODO(unify): sk-prop-sf-open-closed-triangle
/--
The canonical map `j_! ⟶ j_*`, whose cokernel is the boundary sheaf `B` supported on the
complement of `U`:

```
  j_! F ──────▶ j_* F ──────▶ B ──────▶ 0
    │             │
    │ j_! α       │ j_* α
    ▼             ▼
  j_! G ──────▶ j_* G
```

Its components are those of the comparison `Etale.openImmersionLowerShriekToLowerStar` along
the base change `j̄ : Ū ⟶ X̄`.
-/
noncomputable def extensionByZeroToDirectImage :
    extensionByZero (k₀ := k₀) (l := l) j ⟶ directImage j where
  app F := ObjectProperty.homMk (ObjectProperty.homMk
    { f := (Etale.openImmersionLowerShriekToLowerStar _
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).app F.obj.carrier
      h := by
        have hc := Etale.openImmersionLowerShriekToLowerStar_geometricFiberMap_comm
          (WeilCoefficients.{u} l) j (comp_over j _) F.obj.carrier
        have hnat := (Etale.openImmersionLowerShriekToLowerStar (WeilCoefficients.{u} l)
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).naturality F.obj.obj.str
        exact (by rw [reassoc_of% hc, Category.assoc, hnat] :
          (WeilSheaf.frobeniusPullback k₀ l X).map
              ((Etale.openImmersionLowerShriekToLowerStar _
                (Scheme.Hom.geometricFiberMap j (comp_over j _))).app F.obj.carrier) ≫
            (Etale.lowerStarGeometricFiberMapCompFrobeniusIso _ j (comp_over j _)).hom.app
                F.obj.carrier ≫
              (Scheme.Hom.geometricFiberMap j (comp_over j _))_*[_].map F.obj.obj.str =
          ((Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso _ j
                (comp_over j _)).hom.app F.obj.carrier ≫
              (Scheme.Hom.geometricFiberMap j (comp_over j _))_!open[_].map F.obj.obj.str) ≫
            (Etale.openImmersionLowerShriekToLowerStar _
              (Scheme.Hom.geometricFiberMap j (comp_over j _))).app F.obj.carrier) })
  naturality F G α :=
    ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Endofunctor.Algebra.ext
      ((Etale.openImmersionLowerShriekToLowerStar _ _).naturality α.hom.hom.f)))

end WeilSheaf

end AlgebraicGeometry
