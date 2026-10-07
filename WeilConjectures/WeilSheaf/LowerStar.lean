/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.WeilSheaf.Category

/-!
# The pushforward of Weil sheaves and Weil complexes

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pushforward `φ̄_*` of pro-étale sheaves along
its base change `φ̄ : X̄ ⟶ Ȳ` to the geometric fibers commutes with the Frobenius pullbacks
(`ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`), so it induces a functor
`ProEtaleWeilSheaf.lowerStar φ` on pro-étale Weil sheaves. Its total right derived functor
`Rφ_*`, taken in the derived categories of pro-étale Weil sheaves, carries Weil complexes on `X`
to Weil complexes on `Y`. This mirrors the pullbacks `WeilSheaf.upperStar` and
`WeilComplex.upperStar`. No compactification is involved.

That the results are again constructible, respectively bounded with constructible
cohomology, is the finiteness theorem (SGA 4½, *Th. finitude*), for `φ` quasi-compact,
quasi-separated and of finite type and `Y` locally of finite type over `k₀`; these are
hypotheses of the definitions below, and the finiteness statements
`AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_lowerStar` and
`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar` are stated with `sorry`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`: `φ_*` on pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.lowerStar`: `φ_*` on Weil sheaves.
- `AlgebraicGeometry.WeilComplex.derivedLowerStar`: `Rφ_*` on Weil complexes.
- `AlgebraicGeometry.WeilSheaf.higherLowerStar`: the higher direct images `Rⁱφ_*` of Weil
  sheaves, the cohomology sheaves of `Rφ_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The pushforward `φ_*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure
transported along `ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtaleWeilSheaf.lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l Y :=
  IsoAlgebra.mapOfNatIso
    (ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _))

instance (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l φ).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (ProEtaleWeilSheaf.lowerStar k₀ l φ) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

/-- **Finiteness for the pushforward of Weil sheaves** (SGA 4½, *Th. finitude*): the
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism of
finite type with target locally of finite type over `k₀` is constructible. -/
theorem WeilSheaf.isAdicConstructibleSheaf_lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (F : ProEtaleWeilSheaf k₀ l X) (hF : WeilSheaf.objectProperty k₀ l X F) :
    WeilSheaf.objectProperty k₀ l Y ((ProEtaleWeilSheaf.lowerStar k₀ l φ).obj F) :=
  sorry

/-- **Finiteness for the derived pushforward of Weil complexes** (SGA 4½, *Th. finitude*): the
derived pushforward of a Weil complex along a quasi-compact quasi-separated morphism of finite
type with target locally of finite type over `k₀` is bounded with constructible cohomology;
the cohomology sheaves are those of the derived pushforward of the underlying complex, the
forgetful functor preserving K-injective complexes. -/
theorem WeilComplex.objectProperty_rightDerivedLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (hK : WeilComplex.objectProperty k₀ l X K) :
    WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj K) :=
  sorry

/-- The pushforward `φ_*` of Weil sheaves along a quasi-compact quasi-separated morphism
`φ : X ⟶ Y` of finite type of `k₀`-schemes, with `Y` locally of finite type over `k₀`: the
pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the transported Weil structure. -/
noncomputable def WeilSheaf.lowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  (WeilSheaf.objectProperty k₀ l X).liftFullSubcategory (WeilSheaf.objectProperty k₀ l Y)
    (ProEtaleWeilSheaf.lowerStar k₀ l φ) (WeilSheaf.isAdicConstructibleSheaf_lowerStar φ)

/-- The derived pushforward `Rφ_*` of Weil complexes along a quasi-compact quasi-separated
morphism `φ : X ⟶ Y` of finite type of `k₀`-schemes, with `Y` locally of finite type over
`k₀`: the total right derived functor of the pushforward of pro-étale Weil sheaves, restricted
to Weil complexes. -/
noncomputable def WeilComplex.derivedLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l Y)
    (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor
    (WeilComplex.objectProperty_rightDerivedLowerStar φ)

/-- The higher direct image `Rⁱφ_*` of Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes as above: the cohomology sheaf `𝓗ⁱ` (indexed by `ℤ`, with `i : ℕ` coerced) of the
derived pushforward `Rφ_*` of a Weil sheaf placed in degree zero. -/
noncomputable def WeilSheaf.higherLowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerStar φ ⋙ WeilComplex.homologySheaf i

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

namespace WeilSheaf

@[simp]
lemma lowerStar_obj_obj_carrier (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj F.obj.carrier :=
  rfl

@[simp]
lemma lowerStar_obj_obj_str (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.str =
      (ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)).app
          F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].mapIso F.obj.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F.obj

@[simp]
lemma lowerStar_map_hom_hom_f {F G : WeilSheaf k₀ l X} (α : F ⟶ G) :
    ((lowerStar φ).map α).hom.hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map α.hom.hom.f :=
  rfl

instance : (lowerStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

end WeilSheaf

instance : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

instance (i : ℕ) : (WeilSheaf.higherLowerStar (k₀ := k₀) (l := l) φ i).Additive := by
  unfold WeilSheaf.higherLowerStar
  infer_instance

end AlgebraicGeometry
