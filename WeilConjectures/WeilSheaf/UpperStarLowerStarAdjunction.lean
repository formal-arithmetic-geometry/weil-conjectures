/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarLowerStarMate
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# The adjunction `φ^* ⊣ φ_*` of Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback and the pushforward of Weil sheaves
are the pullback `φ̄^*` and the pushforward `φ̄_*` of `ℓ`-adic sheaves along the base change
`φ̄ : X̄ ⟶ Ȳ`, with Weil structures transported along the Frobenius exchange isomorphisms. These
exchange isomorphisms are mates under `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`), so
the unit and the counit of `φ̄^* ⊣ φ̄_*` are morphisms of Weil sheaves and `φ^* ⊣ φ_*`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`: `φ^* ⊣ φ_*` on pro-étale
  Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction`: `φ^* ⊣ φ_*` on Weil sheaves; its
  unit and counit have the underlying morphisms of `ℓ`-adic sheaves of
  `AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction`
  (`AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_hom_f`,
  `AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_hom_f`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.isIso_of_isIso_hom_hom_f`: a morphism of Weil sheaves is an
  isomorphism if its underlying morphism of `ℓ`-adic sheaves is.
- `AlgebraicGeometry.WeilSheaf.isIso_upperStarLowerStarAdjunction_counit`: for a quasi-compact
  open immersion `j`, the counit `j^* j_* ⟶ 𝟭` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

section ProEtale

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves: the adjunction `φ̄^* ⊣ φ̄_*` of
`ℓ`-adic sheaves, whose unit and counit respect the Weil structures since the Frobenius exchange
isomorphisms of `φ̄^*` and `φ̄_*` are mates. -/
noncomputable def ProEtaleWeilSheaf.upperStarLowerStarAdjunction :
    ProEtaleWeilSheaf.upperStar k₀ l φ ⊣ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  IsoAlgebra.mapOfNatIsoAdjunction
    (ProEtale.adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))
    (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv φ (comp_over φ _))

@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f
    (F : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).unit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app F.carrier :=
  rfl

@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f
    (F : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.carrier :=
  rfl

end ProEtale

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

/-- A morphism of Weil sheaves is an isomorphism as soon as its underlying morphism of `ℓ`-adic
sheaves is: the forgetful functors reflect isomorphisms. -/
lemma isIso_of_isIso_hom_hom_f {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [IsIso f.hom.hom.f] :
    IsIso f := by
  have : IsIso ((IsoAlgebra.forget _).map f.hom) := inferInstanceAs (IsIso f.hom.hom.f)
  have : IsIso f.hom := isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  exact ⟨⟨ObjectProperty.homMk (inv f.hom), ObjectProperty.hom_ext _ (IsIso.hom_inv_id f.hom),
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id f.hom)⟩⟩

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The adjunction `φ^* ⊣ φ_*` of Weil sheaves: the adjunction `φ̄^* ⊣ φ̄_*` of `ℓ`-adic sheaves
on the geometric fibres, whose unit and counit respect the Weil structures. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar (k₀ := k₀) (l := l) φ ⊣ lowerStar φ :=
  ObjectProperty.liftFullSubcategoryAdjunction
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ) _ _

/-- The unit `F ⟶ φ_* φ^* F` of Weil sheaves is the unit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma upperStarLowerStarAdjunction_unit_app_hom_hom_f (F : WeilSheaf k₀ l Y) :
    ((upperStarLowerStarAdjunction φ).unit.app F).hom.hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app F.obj.carrier :=
  rfl

/-- The counit `φ^* φ_* F ⟶ F` of Weil sheaves is the counit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma upperStarLowerStarAdjunction_counit_app_hom_hom_f (F : WeilSheaf k₀ l X) :
    ((upperStarLowerStarAdjunction φ).counit.app F).hom.hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.obj.carrier :=
  rfl

/-- For a quasi-compact open immersion `j`, the counit `j^* j_* F ⟶ F` of Weil sheaves is an
isomorphism, since the counit of `j̄^* ⊣ j̄_*` is. -/
instance isIso_upperStarLowerStarAdjunction_counit_app {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) :
    IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app F) := by
  have : IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app F).hom.hom.f := by
    rw [upperStarLowerStarAdjunction_counit_app_hom_hom_f]
    infer_instance
  exact isIso_of_isIso_hom_hom_f _

/-- For a quasi-compact open immersion `j`, the counit `j^* j_* ⟶ 𝟭` of Weil sheaves is an
isomorphism. -/
instance isIso_upperStarLowerStarAdjunction_counit {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsIso (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit :=
  NatIso.isIso_of_isIso_app _

end WeilSheaf

end AlgebraicGeometry
