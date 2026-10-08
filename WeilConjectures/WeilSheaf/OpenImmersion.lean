/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Direct images of Weil sheaves along an open immersion

The ordinary direct image `j_*`, the higher direct images `Rⁱj_*`, the extension by zero `j_!`
and the canonical map `j_! ⟶ j_*` along an open immersion `j`. The direct images are the
pushforwards `LAdicWeilSheaf.lowerStar` and `LAdicWeilSheaf.higherLowerStar` along `j`. The
extension by zero is the extension by zero along the base change `j̄ : Ū ⟶ X̄`, with the Weil
structure transported along the base change isomorphism for the cartesian square of `j̄` and the
geometric Frobenii (`WeilConjectures.SixFunctors.Etale.GeometricFrobenius`). The map `j_! ⟶ j_*` is
the comparison `j̄_! ⟶ j̄_*` of étale sheaves, which is compatible with these Weil structures.

## Main declarations

- `AlgebraicGeometry.LAdicWeilSheaf.higherDirectImage`: the higher direct images `Rⁱj_*`.
- `AlgebraicGeometry.LAdicWeilSheaf.directImage`, `AlgebraicGeometry.LAdicWeilSheaf.extensionByZero`
  and `AlgebraicGeometry.LAdicWeilSheaf.extensionByZeroToDirectImage`: the two extensions along an
  open immersion and the canonical map between them.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace LAdicWeilSheaf

open Etale

-- TODO(unify): sk-d-real-boundary
/-- The *ordinary* sheaf direct image `j_*` along a quasi-compact open immersion `j`: the
pushforward `LAdicWeilSheaf.lowerStar j`. Its stalks at the missing points are the inertia
invariants. -/
noncomputable abbrev directImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    LAdicWeilSheaf k₀ l U ⥤ LAdicWeilSheaf k₀ l X :=
  lowerStar j

-- TODO(unify): sk-d-real-boundary
-- TODO: the isomorphism `higherDirectImage j 0 ≅ directImage j` (`R⁰j_* = j_*`), from
-- `H⁰ ∘ Rf_* ∘ single 0 ≅ f_*` for étale sheaves along an arbitrary `f`.
/-- The higher direct image `Rⁱj_*` along a quasi-compact open immersion `j`: the higher direct
image `LAdicWeilSheaf.higherLowerStar j i`, the cohomology sheaf `𝓗ⁱ` (indexed by `ℤ`, with
`i : ℕ` coerced) of the derived pushforward `Rj_*` of a Weil sheaf placed in degree zero. -/
noncomputable abbrev higherDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : ℕ) :
    LAdicWeilSheaf k₀ l U ⥤ LAdicWeilSheaf k₀ l X :=
  higherLowerStar j i

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- Extension by zero `j_!` along an open immersion `j`: the extension by zero along the base
change `j̄ : Ū ⟶ X̄`, with the Weil structure transported along
`Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    LAdicWeilSheaf k₀ l U ⥤ LAdicWeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso _ j (comp_over j _)))
    fun F ↦
      have : Scheme.IsConstructibleSheaf F.obj.carrier := F.property
      Scheme.IsConstructibleSheaf.openImmersionLowerShriek _
        (Scheme.Hom.geometricFiberMap j (comp_over j _)).closedComplement
        (Scheme.Hom.range_closedComplement _) F.obj.carrier

section ExtensionByZero

variable (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]

@[simp]
lemma extensionByZero_obj_obj_carrier (F : LAdicWeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap j (comp_over j _))_!open[_].obj F.obj.carrier :=
  rfl

@[simp]
lemma extensionByZero_obj_obj_str (F : LAdicWeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.str =
      (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso _ j (comp_over j _)).app
          F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap j (comp_over j _))_!open[_].mapIso F.obj.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ _

@[simp]
lemma extensionByZero_map_hom_hom_f {F G : LAdicWeilSheaf k₀ l U} (α : F ⟶ G) :
    ((extensionByZero j).map α).hom.hom.f =
      (Scheme.Hom.geometricFiberMap j (comp_over j _))_!open[_].map α.hom.hom.f :=
  rfl

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance : (extensionByZero (k₀ := k₀) (l := l) j).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := LAdicWeilSheaf.objectProperty k₀ l U)
    (Q := LAdicWeilSheaf.objectProperty k₀ l X) _ _

end ExtensionByZero

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
noncomputable def extensionByZeroToDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionByZero (k₀ := k₀) (l := l) j ⟶ directImage j where
  app F := ObjectProperty.homMk ((IsoAlgebra.mapOfNatIsoHom
    (Etale.openImmersionLowerShriekToLowerStar _ (Scheme.Hom.geometricFiberMap j (comp_over j _)))
    (Etale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso _ j
      (comp_over j _))).app F.obj)
  naturality _ _ α := ObjectProperty.hom_ext _ ((IsoAlgebra.mapOfNatIsoHom _
    (Etale.openImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso _ j
      (comp_over j _))).naturality α.hom)

@[simp]
lemma extensionByZeroToDirectImage_app_hom_hom_f (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : LAdicWeilSheaf k₀ l U) :
    ((extensionByZeroToDirectImage j).app F).hom.hom.f =
      (Etale.openImmersionLowerShriekToLowerStar _
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).app F.obj.carrier :=
  rfl

end LAdicWeilSheaf

end AlgebraicGeometry
