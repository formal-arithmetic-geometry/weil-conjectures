/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Targets.PoincareTateBoundedConstructible
import Sheaf.Paper.CondensedTateIntegralTower
import Sheaf.Paper.FinitePuritySourceUnitReduction
import Sheaf.SmoothPurity.OpenDimensionObstruction
import Sheaf.SmoothPurity.PointUnitNonzero
import Sheaf.SmoothPurity.TraceExistence
import Sheaf.SmoothPurity.TraceNonuniqueness
import Sheaf.Paper.CoefficientEvaluationModels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility of the Tate
twists need not be recorded.

## Sorried data

The orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`, blueprint `def-pur-smooth-trace`)
is a `@[no_expose]` definition with value `sorry`: its construction (the finite orientations
transported through the integral tower, normalized by integration on the affine line) is not
formalized. The trace map `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is the blueprint composite of `Rf_! γ_f`
and the counit of `Rf_! ⊣ Rf^!`. The purity isomorphism
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is *defined* from it, as the inverse
of its adjoint `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` for `Rf_! ⊣ Rf^!`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap`, equal to `γ_f`). The following
properties of the trace are `sorry`ed:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`: smooth purity proper, the
  adjoint of the trace is an isomorphism;
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`: in
  relative dimension zero, for an open immersion `j`, the purity isomorphism is the canonical
  identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`);
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`: compatibility
  with composition with an open immersion `j` on the target, through the composition
  isomorphism `R(f ≫ j)^! ≅ Rj^! ⋙ Rf^!`.

These normalizations pin the trace down far more than an arbitrary isomorphism
`Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`, but not completely: the compatibility with general composition and
with base change, and the identification of the trace of a smooth curve with the classical
trace on `H²_c`, need the comparison isomorphisms of Tate twists along pullbacks and tensor
products, which are not available yet.

-/

@[expose] public section


set_option Elab.async false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Constructibility of the Tate twists -/

section TateTwist

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]` of a separated `k`-scheme of finite type, on which `ℓ`
is invertible, is bounded constructible. -/
lemma boundedConstructible_tateTwistDerived (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      ((shiftFunctor _ n).obj (tateTwistDerived X.left ℓ d)) := by
  have _ := (inferInstance : LocallyOfFiniteType X.hom)
  have _ := (inferInstance : QuasiCompact X.hom)
  have _ := (inferInstance : IsSeparated X.hom)
  have _ := (inferInstance : Fact (ringChar k).Prime)
  have hbase : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ)).isUnit
  have : ∀ x : X.left, Invertible (ℓ : X.left.residueField x) := fun x ↦
    (show IsUnit (ℓ : X.left.residueField x) by
      simpa using hbase.map
        ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom).invertible
  exact boundedConstructible_tateTwistDerived_of_invertible ℓ X.left d n

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]`, as a bounded constructible complex. -/
noncomputable def boundedConstructibleTateTwist (d n : ℤ) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X.left ℓ d),
    boundedConstructible_tateTwistDerived ℓ X d n⟩

end TateTwist

/-- The Tate twist `ℚ̄_ℓ,X(0)`, placed in degree `0`, is the unit of `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistDerivedZeroIso (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    tateTwistDerived T ℓ 0 ≅ 𝟙_ _ :=
  DerivedCategory.singleFunctorObjUnitIso _

/-! ### Smooth purity -/

section Purity

-- Keep abstract categorical calculations from expanding the sheaf-module models.
attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  Mod.monoidalCategory Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] Scheme.PurityIntegralTower.ReconstructionResult
  boundedConstructibleLowerShriek boundedConstructibleUpperShriek
  boundedConstructibleUpperShriekAdjunction

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- Blueprint `def-pur-smooth-trace` (`γ_{f,Λ_Y}`, `sk-prop-sp-orientation`): the **orientation**
`ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension `d`, the purity
isomorphism normalized by integration on the affine line (the canonical orientation of
`𝔸¹_Y ⟶ Y`). Its construction (from the finite orientations through the integral tower and
scalar extension) is not formalized; it is the datum the smooth trace is built from. -/
@[no_expose]
noncomputable def smoothOrientation :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  sorry

/-- Blueprint `def-pur-smooth-trace` (`sk-def-sp-trace`): the **trace map**
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of a morphism `f` smooth of pure relative dimension `d`
(SGA 4, Exposé XVIII, Théorème 2.9): the composite
`Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ Rf_! Rf^! ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,Y` of `Rf_!` of the orientation `γ_f`
(`smoothOrientation`) and the counit `Tr_f` of `Rf_! ⊣ Rf^!`. -/
@[no_expose]
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _

omit [SmoothOfRelativeDimension d f.left] in
/-- The smooth trace is the counit transpose of the orientation: `Tr^sm_f = Tr_f ∘ Rf_!(γ_f)`.
Source: def-pur-smooth-trace. -/
theorem smoothTrace_eq :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map (smoothOrientation ℓ f d) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _ := by
  unfold smoothTrace
  rfl

attribute [local irreducible] smoothTrace

/-- The **purity map** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`: the adjoint of the trace `Tr_f` for
`Rf_! ⊣ Rf^!`. -/
noncomputable def smoothPurityMap :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ (smoothTrace ℓ f d)

omit [SmoothOfRelativeDimension d f.left] in
/-- The purity map is the orientation: the adjunct of `Tr_f ∘ Rf_!(γ_f)` is `γ_f`.
Source: def-pur-smooth-trace (the purity map is recovered from the smooth trace). -/
theorem smoothPurityMap_eq_smoothOrientation :
    smoothPurityMap ℓ f d = smoothOrientation ℓ f d := by
  change (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _ (smoothTrace ℓ f d) = _
  rw [smoothTrace_eq]
  exact (congrArg ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _)
    ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv_counit _ _
      (smoothOrientation ℓ f d))).symm.trans
    (((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _)

omit [SmoothOfRelativeDimension d f.left] in
/-- The chosen trace is recovered from its adjoint by the actual exceptional counit.
This is the formal trace-identification step of `def-route-smooth-trace`; it uses
only the two inverse laws of the adjunction hom equivalence. -/
private theorem smoothTrace_eq_adjunct :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (smoothPurityMap ℓ f d) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _) := by
  calc
    smoothTrace ℓ f d =
        ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).symm
          (smoothPurityMap ℓ f d) :=
      (((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).symm_apply_apply
        (smoothTrace ℓ f d)).symm
    _ = _ := (boundedConstructibleUpperShriekAdjunction
      ℓ f).homEquiv_counit _ _ (smoothPurityMap ℓ f d)

omit [SmoothOfRelativeDimension d f.left] in
/-- The live open comparison preserves the two actual exceptional counits.
Source: `lem-route-smooth-purity-iso-zero-of-is-open-immersion`, Step 2.
The inverse right-adjoint comparison is the conjugate of the compactification
comparison on left adjoints. The mate-counit identity gives the equation directly. -/
private theorem smoothTrace_openComparison_counit
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ j).map
        ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app K).inv ≫
      (boundedConstructibleUpperShriekAdjunction
        ℓ j).counit.app K =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K := by
  exact conjugateEquiv_counit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom K

/-- Naturality carries a unit comparison to any preceding morphism.
Source: the formal counit calculations in the open-normalization and composition
nodes. Expand the mapped composite once and use naturality of the comparison. -/
private theorem smoothTrace_map_unit_square
    {C D : Type*} [Category C] [Category D] (F H : C ⥤ D) (b : F ⟶ H)
    {K U V : C} {L : D} (u : U ⟶ V) (c : F.obj V ⟶ L) (r : H.obj U ⟶ L)
    (hu : F.map u ≫ c = b.app U ≫ r) (t : K ⟶ U) :
    F.map (t ≫ u) ≫ c = b.app K ≫ H.map t ≫ r := by
  rw [Functor.map_comp, Category.assoc, hu, ← Category.assoc, b.naturality,
    Category.assoc]

omit [SmoothOfRelativeDimension d f.left] in
/-- Include the actual monoidal unit map in open counit normalization.
Source: `lem-route-smooth-purity-iso-zero-of-is-open-immersion`, Steps 2--3.
Expand the unit comparison, apply the preceding counit identity, then move the
monoidal unit map through the left compactification comparison by naturality. -/
private theorem smoothTrace_openUnit_counit (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (boundedConstructibleLowerShriek ℓ j).map
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperShriekAdjunction
        ℓ j).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
        (𝟙_ _) ≫
      (boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  change (boundedConstructibleLowerShriek ℓ j).map
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ j)).hom ≫
        ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app (𝟙_ _)).inv) ≫
      _ = _
  exact smoothTrace_map_unit_square _ _ _ _ _ _
    (smoothTrace_openComparison_counit ℓ j (𝟙_ _)) _

omit [SmoothOfRelativeDimension d f.left] in
/-- Rewrite an arbitrary trace followed by the open unit and exceptional counit
as the ordinary extension-by-zero trace. Source:
`lem-route-smooth-purity-iso-comp-open-immersion`, Steps 6--7.
Functoriality separates the trace and unit map; the actual open-unit counit
identity removes the exceptional unit factor; naturality moves the left
compactification comparison to the original trace source. -/
private theorem smoothTrace_openComposite_counit
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    {K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (t : K ⟶ 𝟙_ _) :
    (boundedConstructibleLowerShriek ℓ j).map
        (t ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
      (boundedConstructibleUpperShriekAdjunction
        ℓ j).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app K ≫
      (boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j).map t ≫
      (boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  exact smoothTrace_map_unit_square _ _ _ _ _ _
    (smoothTrace_openUnit_counit ℓ j) t

/-- The finite diagonal/deformation data and the normalized integral Tate and unit towers
needed to construct the smooth trace exist for the actual underlying map of `f`.
Source: `def-route-smooth-trace`, finite-purity and reconstruction inputs, and
`lem-route-is-iso-smooth-purity-map`, Step 1. This instantiates the declared reconstruction
lemma on the schemes over `Spec k`; all finiteness witnesses are conclusions. -/
private theorem smoothTrace_reconstructionInputs :
    ∃ (hfq : QuasiCompact f.left) (hfs : IsSeparated f.left)
      (c : Compactification f.left) (hX : IsNoetherian X.left) (hY : IsNoetherian Y.left),
      Scheme.PurityIntegralTower.ReconstructionResult ℓ f.left d hfq hfs c hX hY := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨Over.w f⟩
  let : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  exact Scheme.PurityIntegralTower.condensedTateIntegralTower ℓ k
    (Fact.out : (ringChar k).Prime).pos f.left d

section FiniteNative

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The finite orientations at the native map intertwine the actual root quotient
maps and the exceptional coefficient mates. Source:
`lem-route-is-iso-smooth-purity-map`, Step 1, and finite reduction in
`sk-thm-purity-transport`, Step 1. Apply the supplied coefficient-purity square,
use naturality for the actual coefficient-unit reduction, and cancel the source
unit comparison using finite root balancing. Equal levels are included. -/
private theorem smoothTrace_finiteQuotientSquare
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (b a : ℕ) (hab : a ≤ b)
    (sb : Etale.FiniteSmoothPurity.Level ℓ (b + 1) f.left d)
    (sa : Etale.FiniteSmoothPurity.Level ℓ (a + 1) f.left d)
    (r : Etale.FiniteSmoothPurity.ReductionData
      (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1))
      f.left d sb sa) :
    (Etale.FiniteSmoothPurity.proScalar
        (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1)) X.left).map
          (Scheme.PurityIntegralTower.gammaUnit ℓ b f.left d sb) ≫
        Scheme.PurityIntegralTower.exceptionalReduction ℓ f.left b a hab =
      Etale.FiniteSmoothPurity.proTwistMap d r.twist ≫
        Scheme.PurityIntegralTower.gammaUnit ℓ a f.left d sa := by
  have hp := (r.pro_purity (𝟙_ _) sb.unit_ctf.1).2
  have hn := sa.pro_natural _ _ (r.reduction_ctf Y.left _ sb.unit_ctf.1)
    sa.unit_ctf.1 (unitReduction Y.left ℓ b a hab).hom
  dsimp only [gammaUnit, exceptionalReduction]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ← hn]
  have hu := finitePuritySourceUnitReduction ℓ f.left d b a hab r.twist
  have h := congrArg (fun z ↦ z ≫ proGamma (coefficient ℓ (a + 1)) f.left
    (line (coefficient ℓ (a + 1)) (ℓ ^ (a + 1))
      (CharP.cast_eq_zero _ _) X.left d) sa.alpha (𝟙_ _)) hu
  simpa only [Category.assoc, finiteProSource] using h

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- Invertibility of the finite orientation at the coefficient unit.
Source: `lem-route-is-iso-smooth-purity-map`, Step 1. The pro-etale
finite-purity theorem applies to its supplied constructible unit. -/
private theorem smoothTrace_gammaUnit_isIso
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (n : ℕ) (s : Level ℓ (n + 1) f.left d) :
    IsIso (gammaUnit ℓ n f.left d s) := by
  have := (s.pro_purity (𝟙_ _) s.unit_ctf.1).2.2
  dsimp only [gammaUnit]
  infer_instance

attribute [local instance] smoothTrace_gammaUnit_isIso

-- The inverse-square calculations use only the named forward equations.
-- Retain the actual maps without unfolding their large reconstruction definitions.
attribute [local irreducible] Scheme.PurityIntegralTower.gammaUnit
  Scheme.PurityIntegralTower.reconstructedGamma Scheme.PurityIntegralTower.exceptionalReduction
  Etale.FiniteSmoothPurity.proTwistMap

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The inverse finite orientations respect the actual root quotient maps.
Source: `lem-route-is-iso-smooth-purity-map`, Steps 1--2.
Cancel the scalar image of the higher orientation, apply its forward quotient
square, and cancel the lower orientation with its inverse. This includes
identical levels and uses no assertion about the unconstructed smooth trace. -/
private theorem smoothTrace_finiteInverseQuotientSquare
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (b a : ℕ) (hab : a ≤ b)
    (sb : Level ℓ (b + 1) f.left d) (sa : Level ℓ (a + 1) f.left d)
    (r : ReductionData (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1))
      f.left d sb sa) :
    (proScalar (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1)) X.left).map
        (inv (gammaUnit ℓ b f.left d sb)) ≫ proTwistMap d r.twist =
      exceptionalReduction ℓ f.left b a hab ≫ inv (gammaUnit ℓ a f.left d sa) := by
  rw [Functor.map_inv]
  apply (IsIso.inv_comp_eq _).2
  apply (cancel_mono (gammaUnit ℓ a f.left d sa)).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
    (smoothTrace_finiteQuotientSquare ℓ f d b a hab sb sa r).symm

/-- Invert a coefficient-linear square without expanding its objects or functors.
Source: the inverse quotient step of `lem-route-is-iso-smooth-purity-map`.
Map the inverse, cancel the two invertible sides, and use the forward square. -/
private theorem smoothTrace_inverse_reduction_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {U V W : D} (a : A ⟶ B) [IsIso a] (b : V ⟶ U) [IsIso b]
    (x : F.obj B ⟶ W) (y : W ⟶ U) (z : F.obj A ⟶ V)
    (h : F.map a ≫ x ≫ y = z ≫ b) :
    F.map (inv a) ≫ z = x ≫ y ≫ inv b := by
  rw [Functor.map_inv]
  apply (IsIso.inv_comp_eq _).2
  apply (cancel_mono b).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h.symm

/-- Transpose a coefficient-linear square under scalar adjunction.
Source: `lem-route-is-iso-smooth-purity-map`, the semilinear transition step.
Apply the Hom equivalence and its two naturality identities to the same square. -/
private theorem smoothTrace_semilinear_square
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A B : C} {U V W : D} (a : A ⟶ B)
    (x : F.obj B ⟶ V) (y : F.obj A ⟶ W) (z : W ⟶ U) (b : U ⟶ V)
    (h : F.map a ≫ x = y ≫ z ≫ b) :
    a ≫ adj.homEquiv _ _ x = adj.homEquiv _ _ (y ≫ z) ≫ G.map b := by
  rw [← Category.assoc] at h
  have ht := congrArg (adj.homEquiv _ _) h
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at ht
  exact ht

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The reconstructed inverse orientations commute with the canonical reductions
of the actual derived limit. Source: `lem-route-is-iso-smooth-purity-map`, Step 2.
Use the invertibility supplied by IdentifiesExceptional, cancel the scalar image
of the higher reconstructed orientation, and apply the retained forward square.
Thus the inverse equations concern the actual reconstruction counits, not a
freely chosen family of inverse finite maps. -/
private theorem smoothTrace_reconstructedInverseQuotientSquare
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
    (M : AdicTower X.left (datum.{u} ℓ))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
    (h : IdentifiesExceptional ℓ f.left d s M e) (b a : ℕ) (hab : a ≤ b) :
    letI := h.1 b
    letI := h.1 a
    (pbcDerivedExtend (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)).map
        (inv (reconstructedGamma ℓ f.left d M e b (s b))) ≫
      (pbcReductionNormalization (pbcAdicProjection X.left (datum.{u} ℓ) b)
        (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)
        (pbcAdicProjection X.left (datum.{u} ℓ) a)
        (pbcAdicProjection_comp X.left (datum.{u} ℓ) b a hab)
        (uniformReconstructionLimit (datum.{u} ℓ) M)).hom =
      (scalarComparison X.left ℓ b a hab).hom.app
          ((exceptional (coefficient ℓ (b + 1)) f.left).obj (𝟙_ _)) ≫
        (derivedRealization X.left ℓ a).map (exceptionalReduction ℓ f.left b a hab) ≫
          inv (reconstructedGamma ℓ f.left d M e a (s a)) := by
  let := h.1 b
  let := h.1 a
  exact smoothTrace_inverse_reduction_square _ _ _ _ _ _ (h.2.1 b a hab)

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The inverse orientations also intertwine the semilinear quotient transitions.
Source: `lem-route-is-iso-smooth-purity-map`, Step 2, passing from coefficient-linear
reduction squares to maps of the actual exceptional systems. Apply the actual
scalar-extension/restriction Hom equivalence to the inverse quotient square.
Naturality on its source and target gives the two semilinear composites. No
lifting of an arbitrary diagram of derived maps is assumed. -/
private theorem smoothTrace_reconstructedInverseSemilinearSquare
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
    (M : AdicTower X.left (datum.{u} ℓ))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
    (h : IdentifiesExceptional ℓ f.left d s M e) (b a : ℕ) (hab : a ≤ b) :
    letI := h.1 b
    letI := h.1 a
    inv (reconstructedGamma ℓ f.left d M e b (s b)) ≫
        (pbcDerivedScalarAdjunction
          (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)).homEquiv _ _
          (pbcReductionNormalization (pbcAdicProjection X.left (datum.{u} ℓ) b)
            (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)
            (pbcAdicProjection X.left (datum.{u} ℓ) a)
            (pbcAdicProjection_comp X.left (datum.{u} ℓ) b a hab)
            (uniformReconstructionLimit (datum.{u} ℓ) M)).hom =
      (pbcDerivedScalarAdjunction
        (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)).homEquiv _ _
        ((scalarComparison X.left ℓ b a hab).hom.app
            ((exceptional (coefficient ℓ (b + 1)) f.left).obj (𝟙_ _)) ≫
          (derivedRealization X.left ℓ a).map (exceptionalReduction ℓ f.left b a hab)) ≫
        (pbcDerivedRestrict (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)).map
          (inv (reconstructedGamma ℓ f.left d M e a (s a))) := by
  let := h.1 b
  let := h.1 a
  exact smoothTrace_semilinear_square _ _ _ _ _ _
    (smoothTrace_reconstructedInverseQuotientSquare ℓ f d s M e h b a hab)

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The actual finite exceptional values lie in the single degree required by
reconstruction. Source: `lem-route-is-iso-smooth-purity-map`, Step 2, and
`lem-pur-condensed-exceptional-reconstruction`, case (b). The supplied exceptional
identification gives vanishing in every other degree. The standard t-structure
criteria convert it into both bounds, uniformly in the positive coefficient level.
This uses neither the chosen trace nor the disputed unconditional purity instance. -/
private theorem smoothTrace_exceptionalSingleDegree
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
    (M : AdicTower X.left (datum.{u} ℓ))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
    (h : IdentifiesExceptional ℓ f.left d s M e) (n : ℕ) :
    ((exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _)).IsGE
        (-(2 * (d : ℤ))) ∧
      ((exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _)).IsLE
        (-(2 * (d : ℤ))) := by
  constructor
  · exact (_root_.DerivedCategory.isGE_iff _ _).2
      (fun q hq ↦ h.2.2.2 n q (ne_of_lt hq))
  · exact (_root_.DerivedCategory.isLE_iff _ _).2
      (fun q hq ↦ h.2.2.2 n q (ne_of_gt hq))

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- Cohomology in the purity degree determines and lifts every map from an object
bounded above in that degree to the actual finite exceptional unit.
Source: `lem-route-is-iso-smooth-purity-map`, Step 2, the single-degree part of
`lem-pur-condensed-exceptional-reconstruction`. The preceding bounds supply the
lower bound on the exceptional value. Apply the existing truncation Hom bijection;
its injectivity is the needed comparison of derived maps, and its surjectivity
lifts a specified cohomology map. No arbitrary lift of a whole diagram is asserted. -/
private theorem smoothTrace_exceptionalHomology_bijective
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
    (M : AdicTower X.left (datum.{u} ℓ))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
    (h : IdentifiesExceptional ℓ f.left d s M e) (n : ℕ)
    (K : proCategory (coefficient ℓ (n + 1)) X.left) [K.IsLE (-(2 * (d : ℤ)))] :
    Function.Bijective (fun a : K ⟶
      (exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _) ↦
        (_root_.DerivedCategory.homologyFunctor _ (-(2 * (d : ℤ)))).map a) := by
  let := (smoothTrace_exceptionalSingleDegree ℓ f d s M e h n).1
  exact _root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE _

/-- Lift a specified cohomology isomorphism between two objects of the same shifted
heart, retaining its exact homology map and uniqueness. Source:
`lem-route-is-iso-smooth-purity-map`, Step 2, the good-truncation comparison.
Lift the hom and inverse using the truncation Hom bijections. Injectivity on
endomorphisms proves both inverse laws, and injectivity on maps proves uniqueness.
No evaluation on arbitrary derived morphisms is assumed faithful. -/
private theorem smoothTrace_singleDegree_lift_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P Q : _root_.DerivedCategory C} (r : ℤ)
    [P.IsGE r] [P.IsLE r] [Q.IsGE r] [Q.IsLE r]
    (e : (_root_.DerivedCategory.homologyFunctor C r).obj P ≅
      (_root_.DerivedCategory.homologyFunctor C r).obj Q) :
    ∃! a : P ≅ Q, (_root_.DerivedCategory.homologyFunctor C r).map a.hom = e.hom := by
  let H := _root_.DerivedCategory.homologyFunctor C r
  obtain ⟨a, ha⟩ :=
    (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
      (P := P) (Q := Q) r).2 e.hom
  obtain ⟨b, hb⟩ :=
    (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
      (P := Q) (Q := P) r).2 e.inv
  change H.map a = e.hom at ha
  change H.map b = e.inv at hb
  let a' : P ≅ Q := {
    hom := a
    inv := b
    hom_inv_id := by
      apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
        (P := P) (Q := P) r).1
      change H.map (a ≫ b) = H.map (𝟙 P)
      rw [Functor.map_comp, ha, hb, CategoryTheory.Functor.map_id]
      exact e.hom_inv_id
    inv_hom_id := by
      apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
        (P := Q) (Q := Q) r).1
      change H.map (b ≫ a) = H.map (𝟙 Q)
      rw [Functor.map_comp, ha, hb, CategoryTheory.Functor.map_id]
      exact e.inv_hom_id }
  refine ⟨a', ha, ?_⟩
  intro a'' ha''
  apply Iso.ext
  exact (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
    (P := P) (Q := Q) r).1 (ha''.trans ha.symm)

/-- Compatible cohomology isomorphisms lift to one natural isomorphism of diagrams
in a fixed shifted heart. Source: `lem-route-is-iso-smooth-purity-map`, Step 2,
strict-system comparison by good truncation. Lift each component with the preceding
lemma. Apply the injective homology map to each naturality square and use the
supplied cohomology naturality. Component uniqueness proves uniqueness of the
natural isomorphism. This concerns diagrams in an ordinary derived category;
transport from varying coefficient systems is a separate geometric step. -/
private theorem smoothTrace_singleDegree_diagram_iso
    {J C : Type*} [Category J] [Category C] [Abelian C] [HasDerivedCategory C]
    (P Q : J ⥤ _root_.DerivedCategory C) (r : ℤ)
    (hP : ∀ j : J, (P.obj j).IsGE r ∧ (P.obj j).IsLE r)
    (hQ : ∀ j : J, (Q.obj j).IsGE r ∧ (Q.obj j).IsLE r)
    (e : P ⋙ _root_.DerivedCategory.homologyFunctor C r ≅
      Q ⋙ _root_.DerivedCategory.homologyFunctor C r) :
    ∃! a : P ≅ Q, ∀ j : J,
      (_root_.DerivedCategory.homologyFunctor C r).map (a.hom.app j) = e.hom.app j := by
  classical
  let H := _root_.DerivedCategory.homologyFunctor C r
  have he (j : J) : ∃! a : P.obj j ≅ Q.obj j, H.map a.hom = e.hom.app j := by
    let := (hP j).1
    let := (hP j).2
    let := (hQ j).1
    let := (hQ j).2
    exact smoothTrace_singleDegree_lift_iso r (e.app j)
  let a (j : J) : P.obj j ≅ Q.obj j := (he j).choose
  have ha (j : J) : H.map (a j).hom = e.hom.app j := (he j).choose_spec.1
  let a' : P ≅ Q := NatIso.ofComponents a (by
    intro i j f
    let := (hP i).2
    let := (hQ j).1
    apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).1
    change H.map (P.map f ≫ (a j).hom) = H.map ((a i).hom ≫ Q.map f)
    rw [Functor.map_comp, Functor.map_comp, ha i, ha j]
    exact e.hom.naturality f)
  refine ⟨a', ha, ?_⟩
  intro a'' ha''
  apply Iso.ext
  ext j
  exact congrArg Iso.hom ((he j).unique (y₁ := a''.app j) (y₂ := a j)
    (ha'' j) (ha j))

/-- Compatible purity-degree cohomology isomorphisms form an actual strict-system
isomorphism. Source: `lem-route-is-iso-smooth-purity-map`, Step 2, the strict-system
part of the single-degree reconstruction. Use the prescribed component maps for
the forward morphism. Cancel the higher component isomorphism in each inverse
transition square and apply the forward square; scalar restriction preserves the
inverse identities. Both inverse laws and uniqueness hold componentwise.
Only successive transitions are needed, exactly as in CoefficientSystem. -/
private theorem smoothTrace_strictSystem_iso
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O)
    {M N : SheafOfModules.CoefficientSystem (J := Scheme.ProEt.topology T) O ell}
    (e : ∀ n, M.level n ≅ N.level n)
    (h : ∀ n, (e (n + 1)).hom ≫ N.transition n =
      M.transition n ≫
        (SheafOfModules.coefficientRestriction O ell (Nat.le_succ n)).map (e n).hom) :
    ∃! a : M ≅ N, ∀ n, a.hom.app n = (e n).hom := by
  have hext {A B : SheafOfModules.CoefficientSystem (J := Scheme.ProEt.topology T) O ell}
      (a b : A ⟶ B) (hab : ∀ n, a.app n = b.app n) : a = b := by
    change SheafOfModules.CoefficientSystem.Hom
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell) A B at a b
    cases a
    cases b
    congr 1
    funext n
    exact hab n
  let a : M ⟶ N :=
    SheafOfModules.CoefficientSystem.Hom.mk.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
      (M := M) (N := N) (fun n ↦ (e n).hom) h
  let b : N ⟶ M :=
    SheafOfModules.CoefficientSystem.Hom.mk.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
      (M := N) (N := M) (fun n ↦ (e n).inv) (by
        intro n
        apply (cancel_epi (e (n + 1)).hom).1
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        rw [h n, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id])
  let a' : M ≅ N := {
    hom := a
    inv := b
    hom_inv_id := hext _ _ (fun n ↦ (e n).hom_inv_id)
    inv_hom_id := hext _ _ (fun n ↦ (e n).inv_hom_id) }
  refine ⟨a', fun _ ↦ rfl, ?_⟩
  intro a'' ha''
  apply Iso.ext
  exact hext _ _ ha''

/-- Level evaluations detect derived maps from degree at most r to degree at least r.
Source: `lem-route-is-iso-smooth-purity-map`, Step 2, and the single-degree system
recognition step. Apply the injective degree-r cohomology map. Ordinary evaluations
jointly detect equality of cohomology maps; their specified cohomology comparison
isomorphisms translate equality of the derived evaluations to this equality.
No faithfulness of evaluation on general derived maps is asserted. -/
private theorem smoothTrace_singleDegree_evaluation_ext
    {I C : Type*} {D : I → Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [∀ i, Category (D i)] [∀ i, Abelian (D i)] [∀ i, HasDerivedCategory (D i)]
    (E : ∀ i, C ⥤ D i)
    (F : ∀ i, _root_.DerivedCategory C ⥤ _root_.DerivedCategory (D i))
    (r : ℤ) (χ : ∀ i, _root_.DerivedCategory.homologyFunctor C r ⋙ E i ≅
      F i ⋙ _root_.DerivedCategory.homologyFunctor (D i) r)
    (hE : JointlyFaithful E) {P Q : _root_.DerivedCategory C}
    [P.IsLE r] [Q.IsGE r] (a b : P ⟶ Q)
    (h : ∀ i, (F i).map a = (F i).map b) : a = b := by
  apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).1
  apply hE.map_injective
  intro i
  apply (cancel_mono ((χ i).hom.app Q)).1
  calc
    (E i).map ((_root_.DerivedCategory.homologyFunctor C r).map a) ≫
        (χ i).hom.app Q =
      (χ i).hom.app P ≫
        (_root_.DerivedCategory.homologyFunctor (D i) r).map ((F i).map a) :=
      (χ i).hom.naturality a
    _ = (χ i).hom.app P ≫
        (_root_.DerivedCategory.homologyFunctor (D i) r).map ((F i).map b) := by rw [h i]
    _ = (E i).map ((_root_.DerivedCategory.homologyFunctor C r).map b) ≫
        (χ i).hom.app Q := ((χ i).hom.naturality b).symm

/-- Single-degree concentration is detected by exact level evaluations with their
specified cohomology comparisons. Source: `lem-route-is-iso-smooth-purity-map`,
Step 2, componentwise detection of the bounds in strict-system recognition.
Away from degree r each evaluated cohomology object is zero. The comparison
isomorphisms identify it with evaluation of the whole cohomology object. Joint
faithfulness detects that its identity is zero, so this whole object is zero.
Apply the standard cohomology criteria for both t-structure bounds. -/
private theorem smoothTrace_singleDegree_evaluation_bounds
    {I C : Type*} {D : I → Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [∀ i, Category (D i)] [∀ i, Abelian (D i)] [∀ i, HasDerivedCategory (D i)]
    (E : ∀ i, C ⥤ D i) [∀ i, (E i).Additive]
    (F : ∀ i, _root_.DerivedCategory C ⥤ _root_.DerivedCategory (D i))
    (χ : ∀ i q, _root_.DerivedCategory.homologyFunctor C q ⋙ E i ≅
      F i ⋙ _root_.DerivedCategory.homologyFunctor (D i) q)
    (hE : JointlyFaithful E) (P : _root_.DerivedCategory C) (r : ℤ)
    (hP : ∀ i, ((F i).obj P).IsGE r ∧ ((F i).obj P).IsLE r) :
    P.IsGE r ∧ P.IsLE r := by
  have hz (q : ℤ) (hq : q ≠ r) :
      CategoryTheory.Limits.IsZero ((_root_.DerivedCategory.homologyFunctor C q).obj P) := by
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2
    apply hE.map_injective
    intro i
    have hi : CategoryTheory.Limits.IsZero
        ((_root_.DerivedCategory.homologyFunctor (D i) q).obj ((F i).obj P)) := by
      rcases lt_or_gt_of_ne hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff _ _).1 (hP i).1 q hq
      · exact (_root_.DerivedCategory.isLE_iff _ _).1 (hP i).2 q hq
    have hi' := hi.of_iso ((χ i q).app P)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact hi'.eq_of_src _ _
  constructor
  · exact (_root_.DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hz q (ne_of_lt hq))
  · exact (_root_.DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hz q (ne_of_gt hq))

/-- A compatible cohomology map lifts to a unique derived map with its prescribed
level evaluations. Source: `lem-route-is-iso-smooth-purity-map`, Step 2, the
single-degree system-map clause of exceptional reconstruction. Lift the whole
cohomology map using the truncation Hom bijection. Naturality of each specified
cohomology comparison then identifies its evaluation with the given level map.
Joint faithfulness of ordinary evaluation and the degree bounds prove uniqueness.
Only the upper bound on the source and lower bound on the target are needed;
no faithfulness or fullness on arbitrary derived maps is asserted. -/
private theorem smoothTrace_singleDegree_evaluation_lift
    {I C : Type*} {D : I → Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [∀ i, Category (D i)] [∀ i, Abelian (D i)] [∀ i, HasDerivedCategory (D i)]
    (E : ∀ i, C ⥤ D i)
    (F : ∀ i, _root_.DerivedCategory C ⥤ _root_.DerivedCategory (D i))
    (r : ℤ) (χ : ∀ i, _root_.DerivedCategory.homologyFunctor C r ⋙ E i ≅
      F i ⋙ _root_.DerivedCategory.homologyFunctor (D i) r)
    (hE : JointlyFaithful E) {P Q : _root_.DerivedCategory C}
    [P.IsLE r] [Q.IsGE r]
    (hP : ∀ i, ((F i).obj P).IsLE r) (hQ : ∀ i, ((F i).obj Q).IsGE r)
    (e : (_root_.DerivedCategory.homologyFunctor C r).obj P ⟶
      (_root_.DerivedCategory.homologyFunctor C r).obj Q)
    (δ : ∀ i, (F i).obj P ⟶ (F i).obj Q)
    (he : ∀ i, (E i).map e ≫ (χ i).hom.app Q =
      (χ i).hom.app P ≫
        (_root_.DerivedCategory.homologyFunctor (D i) r).map (δ i)) :
    ∃! a : P ⟶ Q, ∀ i, (F i).map a = δ i := by
  obtain ⟨a, ha⟩ :=
    (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).2 e
  change (_root_.DerivedCategory.homologyFunctor C r).map a = e at ha
  have hδ (i : I) : (F i).map a = δ i := by
    let := hP i
    let := hQ i
    apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).1
    apply (cancel_epi ((χ i).hom.app P)).1
    calc
      (χ i).hom.app P ≫
          (_root_.DerivedCategory.homologyFunctor (D i) r).map ((F i).map a) =
        (E i).map ((_root_.DerivedCategory.homologyFunctor C r).map a) ≫
          (χ i).hom.app Q := ((χ i).hom.naturality a).symm
      _ = (E i).map e ≫ (χ i).hom.app Q := by rw [ha]
      _ = _ := he i
  refine ⟨a, hδ, ?_⟩
  intro b hb
  exact smoothTrace_singleDegree_evaluation_ext E F r χ hE b a
    (fun i ↦ (hb i).trans (hδ i).symm)

/-- A cohomology-system isomorphism lifts with its prescribed derived evaluations.
Source: `lem-route-is-iso-smooth-purity-map`, Step 2, strict-system recognition.
Lift the whole cohomology isomorphism by the shifted-heart bijection. Naturality
of the specified evaluation/cohomology comparisons and the supplied component
normalizations show that each evaluation has the prescribed cohomology map.
The degree bounds at that level identify the derived maps. Joint faithfulness
on ordinary systems then proves uniqueness from the level equations alone.
The compatible whole cohomology isomorphism is essential input: unrelated level
isomorphisms do not suffice to construct a map of derived strict systems. -/
private theorem smoothTrace_singleDegree_evaluation_lift_iso
    {I C : Type*} {D : I → Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [∀ i, Category (D i)] [∀ i, Abelian (D i)] [∀ i, HasDerivedCategory (D i)]
    (E : ∀ i, C ⥤ D i)
    (F : ∀ i, _root_.DerivedCategory C ⥤ _root_.DerivedCategory (D i))
    (r : ℤ) (χ : ∀ i, _root_.DerivedCategory.homologyFunctor C r ⋙ E i ≅
      F i ⋙ _root_.DerivedCategory.homologyFunctor (D i) r)
    (hE : JointlyFaithful E) {P Q : _root_.DerivedCategory C}
    [P.IsGE r] [P.IsLE r] [Q.IsGE r] [Q.IsLE r]
    (hP : ∀ i, ((F i).obj P).IsLE r) (hQ : ∀ i, ((F i).obj Q).IsGE r)
    (e : (_root_.DerivedCategory.homologyFunctor C r).obj P ≅
      (_root_.DerivedCategory.homologyFunctor C r).obj Q)
    (δ : ∀ i, (F i).obj P ≅ (F i).obj Q)
    (he : ∀ i, (E i).map e.hom ≫ (χ i).hom.app Q =
      (χ i).hom.app P ≫
        (_root_.DerivedCategory.homologyFunctor (D i) r).map (δ i).hom) :
    ∃! a : P ≅ Q, ∀ i, (F i).map a.hom = (δ i).hom := by
  obtain ⟨a, ha, _⟩ := smoothTrace_singleDegree_evaluation_lift E F r χ hE hP hQ
    e.hom (fun i ↦ (δ i).hom) he
  have haH : (_root_.DerivedCategory.homologyFunctor C r).map a = e.hom := by
    apply hE.map_injective
    intro i
    apply (cancel_mono ((χ i).hom.app Q)).1
    calc
      (E i).map ((_root_.DerivedCategory.homologyFunctor C r).map a) ≫
          (χ i).hom.app Q =
        (χ i).hom.app P ≫
          (_root_.DerivedCategory.homologyFunctor (D i) r).map ((F i).map a) :=
        (χ i).hom.naturality a
      _ = _ := by rw [ha i]; exact (he i).symm
  obtain ⟨b, hb⟩ :=
    (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
      (X := Q) (Y := P) r).2 e.inv
  change (_root_.DerivedCategory.homologyFunctor C r).map b = e.inv at hb
  let a' : P ≅ Q := {
    hom := a
    inv := b
    hom_inv_id := by
      apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).1
      change (_root_.DerivedCategory.homologyFunctor C r).map (a ≫ b) =
        (_root_.DerivedCategory.homologyFunctor C r).map (𝟙 P)
      rw [Functor.map_comp, haH, hb, CategoryTheory.Functor.map_id, e.hom_inv_id]
    inv_hom_id := by
      apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE r).1
      change (_root_.DerivedCategory.homologyFunctor C r).map (b ≫ a) =
        (_root_.DerivedCategory.homologyFunctor C r).map (𝟙 Q)
      rw [Functor.map_comp, haH, hb, CategoryTheory.Functor.map_id, e.inv_hom_id] }
  refine ⟨a', ha, ?_⟩
  intro b hb
  apply Iso.ext
  exact smoothTrace_singleDegree_evaluation_ext E F r χ hE b.hom a
    (fun i ↦ (hb i).trans (ha i).symm)

section StrictSystemComparison

variable (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O)

/-- Ordinary coefficient evaluation preserves finite limits by its componentwise
exactness theorem. Source: the evaluation step of strict-system recognition. -/
private theorem smoothTrace_coefficientEvaluation_limits (n : ℕ) :
    CategoryTheory.Limits.PreservesFiniteLimits
      (SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n) :=
  (SheafOfModules.coefficientEvaluation_exact
    (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).1

/-- Ordinary coefficient evaluation preserves finite colimits by its componentwise
exactness theorem. Source: the evaluation step of strict-system recognition. -/
private theorem smoothTrace_coefficientEvaluation_colimits (n : ℕ) :
    CategoryTheory.Limits.PreservesFiniteColimits
      (SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n) :=
  (SheafOfModules.coefficientEvaluation_exact
    (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).2

attribute [local instance] smoothTrace_coefficientEvaluation_limits
  smoothTrace_coefficientEvaluation_colimits

open SheafOfModules in
/-- Compatible derived level isomorphisms determine the actual derived strict-system
isomorphism without a separately supplied cohomology orientation. Source:
`lem-route-is-iso-smooth-purity-map`, Step 2, good-truncation recognition.
Conjugate each level cohomology isomorphism by the canonical exact-evaluation
comparisons. The supplied successor squares make these maps a genuine ordinary
cohomology-system isomorphism. Detect both degree bounds by exact evaluations,
then lift that whole system isomorphism. The comparison inverse laws prove the
prescribed evaluations; level detection in the shifted heart proves uniqueness.
The only compatibility assumed is the displayed square for these canonical maps. -/
private theorem smoothTrace_singleDegree_strictSystem_iso_of_levels
    [HasDerivedCategory.{u + 2}
    (SheafOfModules.CoefficientSystem (J := Scheme.ProEt.topology T) O ell)]
    [∀ n, HasDerivedCategory.{u + 2}
      (SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n)]
    (P Q : _root_.DerivedCategory
      (CoefficientSystem (J := Scheme.ProEt.topology T) O ell)) (r : ℤ)
    (hP : ∀ n, (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P).IsGE r ∧
      (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P).IsLE r)
    (hQ : ∀ n, (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q).IsGE r ∧
      (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q).IsLE r)
    (δ : ∀ n, ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P ≅
      ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q)
    (hδ :
      let χ := fun n ↦ (coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
          n).mapDerivedCategoryHomologyFunctorIso r
      let e := fun n ↦ (χ n).app P ≪≫
        (_root_.DerivedCategory.homologyFunctor
          (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) r).mapIso (δ n) ≪≫
        ((χ n).app Q).symm
      ∀ n, (e (n + 1)).hom ≫
          ((_root_.DerivedCategory.homologyFunctor
            (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj Q).transition n =
        ((_root_.DerivedCategory.homologyFunctor
            (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj P).transition n ≫
          (coefficientRestriction O ell (Nat.le_succ n)).map (e n).hom) :
    ∃! a : P ≅ Q, ∀ n, ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).map a.hom =
      (δ n).hom := by
  let E := coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
  let F := fun n ↦ (E n).mapDerivedCategory
  let χ := fun n q ↦ (E n).mapDerivedCategoryHomologyFunctorIso q
  let : ∀ n, (E n).Additive := fun n ↦
    coefficientEvaluation_additive (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n
  have hfaith : JointlyFaithful E := by
    constructor
    intro M N a b hab
    change CoefficientSystem.Hom
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell) M N at a b
    cases a
    cases b
    congr 1
    funext n
    exact hab n
  let e := fun n ↦ (χ n r).app P ≪≫
    (_root_.DerivedCategory.homologyFunctor
      (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) r).mapIso (δ n) ≪≫
    ((χ n r).app Q).symm
  obtain ⟨e', he', _⟩ := smoothTrace_strictSystem_iso T O ell e hδ
  have hP' := smoothTrace_singleDegree_evaluation_bounds E F χ hfaith P r hP
  have hQ' := smoothTrace_singleDegree_evaluation_bounds E F χ hfaith Q r hQ
  let := hP'.1
  let := hP'.2
  let := hQ'.1
  let := hQ'.2
  apply smoothTrace_singleDegree_evaluation_lift_iso E F r
    (fun n ↦ χ n r) hfaith (fun n ↦ (hP n).2) (fun n ↦ (hQ n).1) e' δ
  intro n
  change e'.hom.app n ≫ ((χ n r).app Q).hom =
    ((χ n r).app P).hom ≫ _
  rw [he' n]
  simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

open SheafOfModules in
/-- Compatible level cohomology orientations reconstruct one isomorphism of the
actual derived strict coefficient systems, with exactly the prescribed evaluations.
Source: `lem-route-is-iso-smooth-purity-map`, Step 2, the single-degree system step
of `lem-pur-condensed-exceptional-reconstruction`. First assemble the ordinary
cohomology systems using their semilinear transition equations. Joint faithfulness
of ordinary evaluation and its cohomology comparisons detect both global degree
bounds. Lift the assembled cohomology isomorphism, identify every derived
component by the single-degree Hom bijection, and use level detection for uniqueness.
This isolates the categorical reconstruction from the geometric task of supplying
the finite orientations and their normalization. The evaluation functors and all
cohomology comparisons are the canonical ones induced by exact ordinary evaluation. -/
private theorem smoothTrace_singleDegree_strictSystem_iso
    [HasDerivedCategory.{u + 2}
    (SheafOfModules.CoefficientSystem (J := Scheme.ProEt.topology T) O ell)]
    [∀ n, HasDerivedCategory.{u + 2}
      (SheafOfModules.coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n)]
    (P Q : _root_.DerivedCategory
      (CoefficientSystem (J := Scheme.ProEt.topology T) O ell)) (r : ℤ)
    (hP : ∀ n, (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P).IsGE r ∧
      (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P).IsLE r)
    (hQ : ∀ n, (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q).IsGE r ∧
      (((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q).IsLE r)
    (e : ∀ n,
      ((_root_.DerivedCategory.homologyFunctor
          (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj P).level n ≅
        ((_root_.DerivedCategory.homologyFunctor
          (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj Q).level n)
    (he : ∀ n, (e (n + 1)).hom ≫
        ((_root_.DerivedCategory.homologyFunctor
          (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj Q).transition n =
      ((_root_.DerivedCategory.homologyFunctor
          (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) r).obj P).transition n ≫
        (coefficientRestriction O ell (Nat.le_succ n)).map (e n).hom)
    (δ : ∀ n, ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj P ≅
      ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).obj Q)
    (hnorm : ∀ n, (e n).hom ≫ ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
          n).mapDerivedCategoryHomologyFunctorIso r).hom.app Q =
      ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
          n).mapDerivedCategoryHomologyFunctorIso r).hom.app P ≫
        (_root_.DerivedCategory.homologyFunctor
          (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) r).map (δ n).hom) :
    ∃! a : P ≅ Q, ∀ n, ((SheafOfModules.coefficientEvaluation
        (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).mapDerivedCategory).map a.hom =
      (δ n).hom := by
  apply smoothTrace_singleDegree_strictSystem_iso_of_levels T O ell P Q r hP hQ δ
  let χ := fun n ↦ (SheafOfModules.coefficientEvaluation
    (J := Scheme.ProEt.topology T) (O := O) (ell := ell)
      n).mapDerivedCategoryHomologyFunctorIso r
  have hcanon (n : ℕ) :
      ((χ n).app P ≪≫ (_root_.DerivedCategory.homologyFunctor
        (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) r).mapIso (δ n) ≪≫
        ((χ n).app Q).symm).hom = (e n).hom := by
    have hn := hnorm n
    change (e n).hom ≫ ((χ n).app Q).hom =
      ((χ n).app P).hom ≫
        (_root_.DerivedCategory.homologyFunctor
          (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) r).map
            (δ n).hom at hn
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q ↦ q ≫ ((χ n).app Q).inv) hn.symm
  dsimp only
  intro n
  change _ ≫ _ = _ ≫ _
  rw [hcanon, hcanon]
  exact he n

end StrictSystemComparison

omit [SmoothOfRelativeDimension d f.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- A specified isomorphism on the purity-degree cohomology lifts uniquely to an
isomorphism with the actual finite exceptional unit. Source:
`lem-route-is-iso-smooth-purity-map`, Step 2, the single-degree reconstruction.
Use IdentifiesExceptional to supply both bounds on the target, then lift the
isomorphism and its inverse by the preceding shifted-heart calculation.
The homology map of the resulting derived isomorphism is exactly the supplied map. -/
private theorem smoothTrace_exceptionalHomology_lift_iso
    [QuasiCompact f.left] [IsSeparated f.left] [HasCompactification f.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
    (M : AdicTower X.left (datum.{u} ℓ))
    (e : ∀ n : ℕ,
      M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
    (h : IdentifiesExceptional ℓ f.left d s M e) (n : ℕ)
    (K : proCategory (coefficient ℓ (n + 1)) X.left)
    [K.IsGE (-(2 * (d : ℤ)))] [K.IsLE (-(2 * (d : ℤ)))]
    (a : (_root_.DerivedCategory.homologyFunctor _ (-(2 * (d : ℤ)))).obj K ≅
      (_root_.DerivedCategory.homologyFunctor _ (-(2 * (d : ℤ)))).obj
        ((exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _))) :
    ∃! b : K ≅ (exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _),
      (_root_.DerivedCategory.homologyFunctor _ (-(2 * (d : ℤ)))).map b.hom = a.hom := by
  let := (smoothTrace_exceptionalSingleDegree ℓ f d s M e h n).1
  let := (smoothTrace_exceptionalSingleDegree ℓ f d s M e h n).2
  exact smoothTrace_singleDegree_lift_iso _ a

open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The native finite system can be chosen together with all root quotient squares
and the normalized integral reconstruction theorem for the same compactification.
Source: `lem-route-is-iso-smooth-purity-map`, Step 1, and
`sk-thm-purity-transport`, Steps 1--2. Extract the positive finite levels from the
supplied finite system, reindex them by n+1, and apply the preceding quotient
calculation for every comparable pair. Retain the original reconstruction result,
which reconstructs these same supplied levels and their actual root transitions.
This theorem extracts witnesses only in a proof, never as definition data. -/
private theorem smoothTrace_normalizedFiniteSystem :
    ∃ (hfq : QuasiCompact f.left) (hfs : IsSeparated f.left)
      (c : Compactification f.left) (hX : IsNoetherian X.left) (hY : IsNoetherian Y.left),
      let := hfq
      let := hfs
      let := c.hasCompactification
      let := hX
      let := hY
      ∃ (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
        (r : ∀ (b a : ℕ) (hab : a ≤ b),
          ReductionData (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1))
            f.left d (s b) (s a)),
        (∀ (b a : ℕ) (hab : a ≤ b),
          (proScalar (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1))
              X.left).map (gammaUnit ℓ b f.left d (s b)) ≫
              exceptionalReduction ℓ f.left b a hab =
            proTwistMap d (r b a hab).twist ≫ gammaUnit ℓ a f.left d (s a)) ∧
          ReconstructionResult ℓ f.left d hfq hfs c hX hY := by
  obtain ⟨hfq, hfs, c, hX, hY, hrec⟩ := smoothTrace_reconstructionInputs ℓ f d
  refine ⟨hfq, hfs, c, hX, hY, ?_⟩
  let := hfq
  let := hfs
  let := c.hasCompactification
  let := hX
  let := hY
  have hs : FiniteSmoothSystem ℓ f.left d := by
    unfold ReconstructionResult at hrec
    exact hrec.1
  obtain ⟨level, reduction, _⟩ := hs
  let s (n : ℕ) := level (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let r (b a : ℕ) (hab : a ≤ b) :=
    reduction (b + 1) (a + 1) (Nat.succ_le_succ (Nat.zero_le a))
      (Nat.add_le_add_right hab 1)
  refine ⟨s, r, ?_, hrec⟩
  intro b a hab
  exact smoothTrace_finiteQuotientSquare ℓ f d b a hab (s b) (s a) (r b a hab)


attribute [local irreducible] Scheme.PurityIntegralTower.Reconstructed
  Scheme.PurityIntegralTower.ProjectionNormalized

open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- Extract the actual normalized Tate and unit reconstructions for the native map,
together with both directions of their finite exceptional comparison. Source:
`lem-route-is-iso-smooth-purity-map`, Steps 1--2, and `sk-thm-purity-transport`,
Steps 1--2. Choose the native finite system in the proof, instantiate the retained
reconstruction theorem with exactly those levels and quotient comparisons, and
retain its strict-tower and projection-normalization equations. The preceding
inverse-square calculation supplies compatibility of the inverse comparisons.
Every witness is extracted inside this proof; no definition chooses these data. -/
private theorem smoothTrace_normalizedIntegralSystem :
    ∃ (hfq : QuasiCompact f.left) (hfs : IsSeparated f.left)
      (c : Compactification f.left) (hX : IsNoetherian X.left) (hY : IsNoetherian Y.left),
      let := hfq
      let := hfs
      let := c.hasCompactification
      let := hX
      let := hY
      ∃ (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
        (r : ∀ (b a : ℕ) (hab : a ≤ b),
          ReductionData (FiniteReduction.quotient.{u} ℓ (Nat.add_le_add_right hab 1))
            f.left d (s b) (s a))
        (hXT : IsUnit (ℓ : Γ(X.left, ⊤))) (hYT : IsUnit (ℓ : Γ(Y.left, ⊤)))
        (M : AdicTower X.left (datum.{u} ℓ)) (L : AdicTower Y.left (datum.{u} ℓ))
        (eM : ∀ n : ℕ,
          M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d))
        (eL : ∀ n : ℕ, L.level n ≅ (derivedRealization Y.left ℓ n).obj (𝟙_ _))
        (hM : M.tower = strictDerivedTower X.left ℓ d)
        (hL : L.tower = strictDerivedTower Y.left ℓ 0),
        ProjectionNormalized X.left ℓ hXT d M eM hM ∧
        ProjectionNormalized Y.left ℓ hYT 0 L
          (fun n ↦ eL n ≪≫
            (derivedRealization Y.left ℓ n).mapIso (finiteZeroIso Y.left ℓ n).symm) hL ∧
        Reconstructed X.left ℓ (fun n ↦ finiteTwist X.left ℓ n d)
          (fun b a hab ↦ proTwistMap d (r b a hab).twist) (-(2 * (d : ℤ))) M eM ∧
        Reconstructed Y.left ℓ (fun n ↦ (𝟙_ (proCategory (coefficient ℓ (n + 1)) Y.left)))
          (fun b a hab ↦ (unitReduction Y.left ℓ b a hab).hom) 0 L eL ∧
        ∃ hE : IdentifiesExceptional ℓ f.left d s M eM,
          ∀ (b a : ℕ) (hab : a ≤ b),
            letI := hE.1 b
            letI := hE.1 a
            (pbcDerivedExtend (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)).map
                (inv (reconstructedGamma ℓ f.left d M eM b (s b))) ≫
              (pbcReductionNormalization (pbcAdicProjection X.left (datum.{u} ℓ) b)
                (pbcAdicQuotient X.left (datum.{u} ℓ) b a hab)
                (pbcAdicProjection X.left (datum.{u} ℓ) a)
                (pbcAdicProjection_comp X.left (datum.{u} ℓ) b a hab)
                (uniformReconstructionLimit (datum.{u} ℓ) M)).hom =
              (scalarComparison X.left ℓ b a hab).hom.app
                  ((exceptional (coefficient ℓ (b + 1)) f.left).obj (𝟙_ _)) ≫
                (derivedRealization X.left ℓ a).map (exceptionalReduction ℓ f.left b a hab) ≫
                  inv (reconstructedGamma ℓ f.left d M eM a (s a)) := by
  obtain ⟨hfq, hfs, c, hX, hY, s, r, _, hrec⟩ :=
    smoothTrace_normalizedFiniteSystem ℓ f d
  let := hfq
  let := hfs
  let := c.hasCompactification
  let := hX
  let := hY
  unfold ReconstructionResult at hrec
  obtain ⟨hXT, hYT, M, L, eM, eL, hM, hL, hpM, hpL, hrM, hrL, hE⟩ := hrec.2 s r
  refine ⟨hfq, hfs, c, hX, hY, s, r, hXT, hYT, M, L, eM, eL, hM, hL,
    hpM, hpL, hrM, hrL, hE, ?_⟩
  intro b a hab
  exact smoothTrace_reconstructedInverseQuotientSquare ℓ f d s M eM hE b a hab

open Etale.FiniteSmoothPurity Scheme.PurityIntegralTower in
/-- The native normalized reconstruction supplies the finite single-degree Hom
bijections. Source: `lem-route-is-iso-smooth-purity-map`, Steps 1--2, and
`lem-pur-condensed-exceptional-reconstruction`, case (b). Extract the finite levels
and their actual reconstructed Tate object from the finite-system theorem and
its retained reconstruction result. Keep their exceptional identification and apply
the proved homology Hom
bijection at every positive level. Witnesses are extracted only in this proof.
This is the levelwise Hom calculation; strict-system transport is still required. -/
private theorem smoothTrace_nativeExceptionalHomology :
    ∃ (hfq : QuasiCompact f.left) (hfs : IsSeparated f.left)
      (c : Compactification f.left) (hX : IsNoetherian X.left) (hY : IsNoetherian Y.left),
      let := hfq
      let := hfs
      let := c.hasCompactification
      let := hX
      let := hY
      ∃ (s : ∀ n : ℕ, Level ℓ (n + 1) f.left d)
        (M : AdicTower X.left (datum.{u} ℓ))
        (e : ∀ n : ℕ,
          M.level n ≅ (derivedRealization X.left ℓ n).obj (finiteTwist X.left ℓ n d)),
        IdentifiesExceptional ℓ f.left d s M e ∧
        ∀ (n : ℕ) (K : proCategory (coefficient ℓ (n + 1)) X.left)
          [K.IsLE (-(2 * (d : ℤ)))],
          Function.Bijective (fun a : K ⟶
            (exceptional (coefficient ℓ (n + 1)) f.left).obj (𝟙_ _) ↦
              (_root_.DerivedCategory.homologyFunctor _ (-(2 * (d : ℤ)))).map a) := by
  obtain ⟨hfq, hfs, c, hX, hY, s, r, _, hrec⟩ :=
    smoothTrace_normalizedFiniteSystem ℓ f d
  let := hfq
  let := hfs
  let := c.hasCompactification
  let := hX
  let := hY
  unfold ReconstructionResult at hrec
  obtain ⟨_, _, M, _, e, _, _, _, _, _, _, _, hE⟩ := hrec.2 s r
  refine ⟨hfq, hfs, c, hX, hY, s, M, e, hE, ?_⟩
  intro n K hK
  exact smoothTrace_exceptionalHomology_bijective ℓ f d s M e hE n K

end FiniteNative

omit [SmoothOfRelativeDimension d f.left] in
/-- Taking the adjunct of the explicit counit composite recovers its input morphism.
Source: `lem-route-is-iso-smooth-purity-map`, Step 4. Apply the adjunction Hom equivalence
and its inverse law; this does not assume that the input is invertible. -/
private theorem smoothPurityMap_eq_of_trace_formula
    (a : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map a ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    smoothPurityMap ℓ f d = a := by
  change (boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _
    (smoothTrace ℓ f d) = a
  rw [htrace, ← (boundedConstructibleUpperShriekAdjunction
    ℓ f).homEquiv_counit _ _ a]
  exact ((boundedConstructibleUpperShriekAdjunction ℓ f).homEquiv _ _).apply_symm_apply _

/-- A realized pairing constructs its exceptional comparison, rather than merely
assuming that comparison is invertible. Source: `lem-route-is-iso-smooth-purity-map`,
Step 2, and exceptional reconstruction's representing Hom bijections. Naturality
identifies postcomposition with the transpose with the representing bijection
followed by the adjunction bijection. Yoneda proves invertibility. The generic
proof is instantiated with the actual chosen adjunction below, before the disputed
instance, without unfolding the large derived-category functors. -/
private theorem smoothTrace_representingTranspose_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M : C} {L : D} (t : F.obj M ⟶ L)
    (hrep : ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t)) :
    IsIso (adj.homEquiv M L t) := by
  apply isIso_of_yoneda_map_bijective
  intro K
  have he : (fun a : K ⟶ M ↦ a ≫ adj.homEquiv M L t) =
      fun a ↦ adj.homEquiv K L (F.map a ≫ t) := by
    funext a
    exact (adj.homEquiv_naturality_left a t).symm
  rw [he]
  exact (adj.homEquiv K L).bijective.comp (hrep K)

/-- A representing pairing determines its normalized comparison uniquely, including
specified changes of its source and target. Source: `def-route-smooth-trace` and
`lem-route-is-iso-smooth-purity-map`, Steps 2--4. Construct the comparison from the
actual transpose, then use injectivity of the inverse adjunction bijection to
prove uniqueness. This is uniqueness for a supplied pairing, not a choice of an
orientation from the assertion that some purity isomorphism exists. -/
private theorem smoothTrace_normalizedComparison_unique
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M T : C} {L U : D} (a : M ≅ T) (u : L ≅ U) (t : F.obj M ⟶ L)
    (hrep : ∀ K : C, Function.Bijective (fun b : K ⟶ M ↦ F.map b ≫ t)) :
    ∃! e : T ≅ G.obj U,
      F.map e.hom ≫ adj.counit.app U = F.map a.inv ≫ t ≫ u.hom := by
  have ht : IsIso (adj.homEquiv M L t) :=
    smoothTrace_representingTranspose_isIso adj t hrep
  let c : M ≅ G.obj L := @asIso _ _ _ _ (adj.homEquiv M L t) ht
  let e : T ≅ G.obj U := a.symm ≪≫ c ≪≫ G.mapIso u
  have he : F.map e.hom ≫ adj.counit.app U = F.map a.inv ≫ t ≫ u.hom := by
    change F.map (a.inv ≫ adj.homEquiv M L t ≫ G.map u.hom) ≫
      adj.counit.app U = F.map a.inv ≫ t ≫ u.hom
    rw [← adj.homEquiv_counit _ _
      (a.inv ≫ adj.homEquiv M L t ≫ G.map u.hom)]
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (adj.homEquiv T U).symm.injective
  simpa only [adj.homEquiv_counit] using he'.trans he.symm

omit [SmoothOfRelativeDimension d f.left] in
/-- Assemble a realized representing pairing with the actual Tate and target-unit
identifications. Source: `def-route-smooth-trace` and
`lem-route-is-iso-smooth-purity-map`, Steps 2--4. Lift the ambient Tate comparison
by full faithfulness and transpose the supplied pairing with the chosen adjunction.
The previous lemma proves this transpose invertible. Compose its isomorphism with
the inverse Tate comparison and the exceptional image of the target-unit map.
Naturality and the inverse adjunction law prove the stated trace formula. No data
is chosen from an existence theorem, and the representing pairing is an explicit
input. -/
private theorem smoothTrace_from_representing_pairing
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (u : L ≅ 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (t : (boundedConstructibleLowerShriek ℓ f).obj M ⟶ L)
    (hrep : ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Function.Bijective (fun b : K ⟶ M ↦
        (boundedConstructibleLowerShriek ℓ f).map b ≫ t)) :
    ∃ e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
        (boundedConstructibleUpperShriek ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)),
      (boundedConstructibleLowerShriek ℓ f).map e.hom ≫
          (boundedConstructibleUpperShriekAdjunction
            ℓ f).counit.app (𝟙_ _) =
        (boundedConstructibleLowerShriek ℓ f).map
            (((ObjectProperty.ι _).preimageIso
              (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv) ≫
          t ≫ u.hom := by
  let A : M ≅ boundedConstructibleTateTwist ℓ X d (2 * d) :=
    (ObjectProperty.ι _).preimageIso a
  obtain ⟨e, he, _⟩ := smoothTrace_normalizedComparison_unique
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    A u t hrep
  exact ⟨e, he⟩

omit [SmoothOfRelativeDimension d f.left] in
/-- The reconstructed Hom pairing suffices to prove invertibility of the actual
purity map once its actual trace formula has been established.
Source: `lem-route-is-iso-smooth-purity-map`, Steps 2--4. Construct the comparison
from the pairing, then use the defining counit transpose. Unlike the earlier
invertibility helper, this statement does not assume a comparison isomorphism. -/
private theorem isIso_smoothPurityMap_of_representing_pairing
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (u : L ≅ 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (t : (boundedConstructibleLowerShriek ℓ f).obj M ⟶ L)
    (hrep : ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Function.Bijective (fun b : K ⟶ M ↦
        (boundedConstructibleLowerShriek ℓ f).map b ≫ t))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv) ≫
        t ≫ u.hom) :
    IsIso (smoothPurityMap ℓ f d) := by
  obtain ⟨e, he⟩ := smoothTrace_from_representing_pairing ℓ f d a u t hrep
  rw [smoothPurityMap_eq_of_trace_formula ℓ f d e.hom (htrace.trans he.symm)]
  infer_instance

/-- Realization carries an integral trace-composition equation to the corresponding
equation for the actual realized left compositor. Source:
`lem-route-smooth-purity-iso-comp-open-immersion`, Steps 5--6. Cancel the source
comparison, use its compositor square, and use naturality of the second comparison
at the first integral trace. The two inverse comparisons then cancel. This works
with arbitrary categories and does not assume purity or uniqueness of a trace. -/
private theorem smoothTrace_realization_transitivity
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    (P : A ⥤ B) (Q : B ⥤ C) (R : A ⥤ C)
    (F : A' ⥤ B') (H : B' ⥤ C') (J : A' ⥤ C')
    (U : A ⥤ A') (V : B ⥤ B') (W : C ⥤ C')
    (a : P ⋙ V ≅ U ⋙ F) (b : Q ⋙ W ≅ V ⋙ H) (c : R ⋙ W ≅ U ⋙ J)
    (α : R ⟶ P ⋙ Q) (β : J ⟶ F ⋙ H)
    {M : A} {L : B} {N : C} (t : P.obj M ⟶ L)
    (s : R.obj M ⟶ N) (q : Q.obj L ⟶ N)
    (hs : α.app M ≫ Q.map t ≫ q = s)
    (hc : W.map (α.app M) ≫ b.hom.app (P.obj M) ≫ H.map (a.hom.app M) =
      c.hom.app M ≫ β.app (U.obj M)) :
    β.app (U.obj M) ≫ H.map (a.inv.app M ≫ V.map t) ≫
        b.inv.app L ≫ W.map q = c.inv.app M ≫ W.map s := by
  apply (cancel_epi (c.hom.app M)).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [← hc]
  simp only [Functor.map_comp, Category.assoc]
  have ha : H.map (a.hom.app M) ≫ H.map (a.inv.app M) = 𝟙 _ :=
    (H.mapIso (a.app M)).hom_inv_id
  rw [reassoc_of% ha]
  rw [← reassoc_of% (b.hom.naturality t)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← W.map_comp, ← W.map_comp, hs]

/-- The realized composition equation retains the canonical target-unit maps when
the common realized Tate source is replaced by its specified Tate identification.
Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Steps 6--7. Naturality
moves the common source comparison through the left compositor. The integral
trace equation and the open trace's unit normalization then give the result. -/
private theorem smoothTrace_unit_normalized_transitivity
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (H : D ⥤ E) (J : C ⥤ E) (β : F ⋙ H ⟶ J)
    {M T : C} {L U : D} {N V : E}
    (a : M ≅ T) (b : L ≅ U) (c : N ≅ V)
    (t : F.obj M ⟶ L) (s : J.obj M ⟶ N) (q : H.obj L ⟶ N)
    (ε : H.obj U ⟶ V)
    (hs : β.app M ≫ s = H.map t ≫ q)
    (hq : q ≫ c.hom = H.map b.hom ≫ ε) :
    β.app T ≫ J.map a.inv ≫ s ≫ c.hom =
      H.map (F.map a.inv ≫ t ≫ b.hom) ≫ ε := by
  rw [← Category.assoc (β.app T) (J.map a.inv), ← β.naturality a.inv]
  simp only [Functor.comp_map, Category.assoc]
  rw [reassoc_of% hs, hq]
  simp only [Functor.map_comp, Category.assoc]

omit [SmoothOfRelativeDimension d f.left] in
/-- Apply the preceding unit transport to the live chosen-compactification
compositor and open counit. Source:
`lem-route-smooth-purity-iso-comp-open-immersion`, Steps 6--7. The two trace
identifications and the reconstructed trace equation are explicit inputs.
The output is the native trace-transitivity equation needed by the existing
purity-map mate calculation. No trace is chosen from an existence theorem. -/
private theorem smoothTrace_transitivity_of_realized_traces
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M ≅ boundedConstructibleTateTwist ℓ X d (2 * d))
    (b : L ≅ 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (c : N ≅ 𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (t : (boundedConstructibleLowerShriek ℓ f).obj M ⟶ L)
    (s : (boundedConstructibleLowerShriek ℓ (f ≫ j)).obj M
      ⟶ N)
    (q : (boundedConstructibleLowerShriek ℓ j).obj L ⟶ N)
    (hs : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app M ≫ s =
      (boundedConstructibleLowerShriek ℓ j).map t ≫ q)
    (hq : q ≫ c.hom =
      (boundedConstructibleLowerShriek ℓ j).map
          (b.hom ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _))
    (ht : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map a.inv ≫
        t ≫ b.hom)
    (hu : smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ (f ≫ j)).map a.inv
        ≫ s ≫ c.hom) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ j).map
          (smoothTrace ℓ f d ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _) := by
  let H := boundedConstructibleLowerShriek ℓ j
  let ε := H.map (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
    (boundedConstructibleUpperShriekAdjunction
      ℓ j).counit.app (𝟙_ _)
  have hq' : q ≫ c.hom = H.map b.hom ≫ ε := by
    simpa only [H, ε, Functor.map_comp, Category.assoc] using hq
  have h := smoothTrace_unit_normalized_transitivity
    (boundedConstructibleLowerShriek ℓ f) H
    (boundedConstructibleLowerShriek ℓ (f ≫ j))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv a b c t s q ε hs hq'
  rw [ht, hu]
  simpa only [H, ε, Functor.map_comp, Category.assoc] using h

/-- Taking a mate transports the actual adjunction Hom bijection.
Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Step 7.
Apply the inverse Hom bijection, then use the mate-counit identity and naturality
of the left comparison. This uses no invertibility or purity assertion. -/
private theorem smoothTrace_conjugate_adjunct
    {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (b : F₂ ⟶ F₁)
    {M : C} {L : D} (t : F₁.obj M ⟶ L) :
    adj₂.homEquiv M L (b.app M ≫ t) =
      adj₁.homEquiv M L t ≫ (conjugateEquiv adj₁ adj₂ b).app L := by
  apply (adj₂.homEquiv M L).symm.injective
  rw [Equiv.symm_apply_apply, adj₂.homEquiv_counit, Functor.map_comp,
    Category.assoc, conjugateEquiv_counit, ← Category.assoc, b.naturality,
    Category.assoc, ← adj₁.homEquiv_counit, Equiv.symm_apply_apply]

/-- Compute the composite-adjunction square with abstract categorical data.
Source: `lem-route-smooth-purity-iso-comp-open-immersion`, the mate calculation.
Transport the left comparison under the adjunctions and apply the two Hom
naturality laws. Keeping the data abstract avoids unfolding geometric functors. -/
private theorem smoothTrace_composite_adjunct_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    {J : C ⥤ E} {K : E ⥤ C}
    (adjf : F ⊣ G) (adjj : H ⊣ I) (adjh : J ⊣ K) (c : J ≅ F ⋙ H)
    {M : C} {U : D} {V : E} (t : F.obj M ⟶ U) (s : J.obj M ⟶ V)
    (q : U ⟶ I.obj V)
    (h : c.inv.app M ≫ s = H.map (t ≫ q) ≫ adjj.counit.app V) :
    adjh.homEquiv _ _ s ≫
        (conjugateEquiv adjh (adjf.comp adjj) c.inv).app V =
      adjf.homEquiv _ _ t ≫ G.map q := by
  have ht := congrArg ((adjf.comp adjj).homEquiv M V) h
  rw [smoothTrace_conjugate_adjunct adjh (adjf.comp adjj)] at ht
  have hr : (adjf.comp adjj).homEquiv _ _
      (H.map (t ≫ q) ≫ adjj.counit.app V) = adjf.homEquiv _ _ t ≫ G.map q := by
    rw [Adjunction.comp_homEquiv]
    change adjf.homEquiv _ _ (adjj.homEquiv _ V _) = _
    rw [← adjj.homEquiv_counit _ _ (t ≫ q),
      (adjj.homEquiv _ V).apply_symm_apply (t ≫ q), adjf.homEquiv_naturality_right]
  exact ht.trans hr

omit [SmoothOfRelativeDimension d f.left] in
/-- A normalized trace transitivity equation gives the exceptional-compositor
square for the actual purity maps. Source:
`lem-route-smooth-purity-iso-comp-open-immersion`, Step 7. Use the mate of the live
compact-support compositor and the composite adjunction Hom equivalence. Its two
inverse laws and naturality retain the actual target-unit map q. No purity
isomorphism or disputed invertibility instance is used in this argument. -/
private theorem smoothPurityMap_comp_of_trace_transitivity
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z)
    (q : 𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleUpperShriek ℓ j).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ j).map
          (smoothTrace ℓ f d ≫ q) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _)) :
    smoothPurityMap ℓ (f ≫ j) d ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).hom.app (𝟙_ _) =
      smoothPurityMap ℓ f d ≫
        (boundedConstructibleUpperShriek ℓ f).map q := by
  exact smoothTrace_composite_adjunct_square
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ j))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j) _ _ q htrace

omit [SmoothOfRelativeDimension d f.left] in
/-- The formal last step of the normalized trace construction. Once the geometric
comparison is an isomorphism and the chosen trace is its counit transpose, the actual
purity map is that comparison and is invertible. No comparison is chosen here. -/
private theorem isIso_smoothPurityMap_of_trace_formula
    (e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map e.hom ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    IsIso (smoothPurityMap ℓ f d) := by
  rw [smoothPurityMap_eq_of_trace_formula ℓ f d e.hom htrace]
  infer_instance

omit [SmoothOfRelativeDimension d f.left] in
/-- Lift the specified ambient Tate realization through the full constructible inclusion,
then compose it with the reconstructed exceptional comparison. Its counit transpose
has exactly that adjunct, and its inverse is the ambient reconstruction formula.
Source: `lem-route-is-iso-smooth-purity-map`, Steps 3--5, and
`def-pur-condensed-smooth-purity-iso`. The reconstruction and trace formula are supplied
explicitly; no isomorphism or trace is selected by a mere existence theorem. -/
private theorem smoothPurityMap_of_reconstructed_trace
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (c : M ≅ (boundedConstructibleUpperShriek
      ℓ f).obj (𝟙_ _))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ c.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    ∃ e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
        (boundedConstructibleUpperShriek ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)),
      smoothPurityMap ℓ f d = e.hom ∧
        (ObjectProperty.ι _).mapIso e.symm = (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
  let A : M ≅ boundedConstructibleTateTwist ℓ X d (2 * d) :=
    (ObjectProperty.ι _).preimageIso a
  let e := A.symm ≪≫ c
  have he : smoothPurityMap ℓ f d = e.hom :=
    smoothPurityMap_eq_of_trace_formula ℓ f d e.hom htrace
  have hinv : (ObjectProperty.ι _).mapIso e.symm =
      (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
    apply Iso.ext
    simp only [e, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Functor.mapIso_hom,
      Iso.trans_hom, Functor.map_comp, A, Functor.preimageIso_hom, Functor.map_preimage]
  exact ⟨e, he, hinv⟩

omit [SmoothOfRelativeDimension d f.left] in
/-- A concrete obstruction to the missing smoothness hypothesis: on an open immersion
with positive proposed relative dimension and nonzero coefficient unit, no trace can
have an invertible adjoint. This is proved before the disputed instance is available;
the inverse below is formed only from the explicit hypothetical invertibility. -/
private theorem smoothPurityMap_not_isIso_of_open [IsOpenImmersion f.left]
    (hd : 0 < d)
    (hunit : ¬ CategoryTheory.Limits.IsZero
      (𝟙_ (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) :
    ¬ IsIso (smoothPurityMap ℓ f d) := by
  intro h
  exact hunit (isZero_unit_of_open_positive_purity ℓ f d hd
    ((ObjectProperty.ι _).mapIso
      (@asIso _ _ _ _ (smoothPurityMap ℓ f d) h).symm))

section PointObstruction

attribute [local irreducible] AlgebraicGeometry.Spec

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_locallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_quasiCompact :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_isSeparated :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))


attribute [local irreducible] CategoryTheory.Over.mk

attribute [local instance] pointObstruction_locallyOfFiniteType
  pointObstruction_quasiCompact pointObstruction_isSeparated

attribute [local semireducible] CategoryTheory.Over.mk

omit [SmoothOfRelativeDimension d f.left] in
/-- At a separably closed point, the identity map with proposed dimension one is a
counterexample to the elaborated, unconditionally quantified purity instance. This
proof is before that instance and uses only the nonvanishing of the native unit. -/
private theorem smoothPurityMap_point_dimension_one_not_isIso [IsSepClosed k] :
    ¬ IsIso (smoothPurityMap ℓ (𝟙 (Over.mk (𝟙 (Spec (.of k))))) 1) := by
  exact smoothPurityMap_not_isIso_of_open ℓ _ 1 (by decide)
    (not_isZero_unit_on_separablyClosed_point ℓ k)


/-- The actual geometric-point Hom pairing does not specify a unique trace.
Source: `def-route-smooth-trace`, the missing finite orientation normalization.
Apply the independent sign counterexample, which uses neither the chosen smooth
trace nor the disputed smooth-purity instance. -/
private theorem smoothTrace_representing_not_unique_at_point [IsSepClosed k] :
    ¬ ∃! t :
        (boundedConstructibleLowerShriek ℓ
          (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).obj
            (𝟙_ (Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦
              Profinite.padicAlgClRingObj ℓ⟧)) ⟶ 𝟙_ _,
      ∀ K : Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ 𝟙_ _ ↦
          (boundedConstructibleLowerShriek ℓ
            (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).map a ≫ t) := by
  exact not_existsUnique_representing_trace_at_point ℓ (k := k)

end PointObstruction

-- The smoothness hypothesis is a binder of the instance: an `instance` drops unused
-- instance-implicit section variables, even under `include`. The elaborated signature has it
-- once; the linter also counts the section variable in scope.
set_option linter.overlappingInstances false in
/-- Blueprint `sk-thm-sp-qbar`: **smooth purity** (SGA 4, Exposé XVIII, Théorème 3.2.5): the
adjoint of the trace, `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, is an isomorphism, for `f` smooth of
relative dimension `d`. -/
instance isIso_smoothPurityMap [SmoothOfRelativeDimension d f.left] :
    IsIso (smoothPurityMap ℓ f d) :=
  sorry

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. It is the inverse of
the adjoint of the trace (`smoothPurityMap`), after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ f d)).symm

/-- The normalized inverse formula for an explicitly reconstructed trace.
Source: `def-pur-condensed-smooth-purity-iso` and the last step of
`lem-route-smooth-purity-iso-comp-open-immersion`. The preceding helper constructs the
comparison before the disputed purity instance; here equality of its hom with the
actual adjunct identifies its inverse with the already defined purity isomorphism. -/
private theorem smoothPurityIso_eq_of_reconstructed_trace
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (c : M ≅ (boundedConstructibleUpperShriek
      ℓ f).obj (𝟙_ _))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ c.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ f d = (ObjectProperty.ι _).mapIso c.symm ≪≫ a := by
  obtain ⟨e, he, hinv⟩ := smoothPurityMap_of_reconstructed_trace ℓ f d a c htrace
  have h : asIso (smoothPurityMap ℓ f d) = e := Iso.ext he
  unfold smoothPurityIso
  rw [h]
  exact hinv

/-- Invert a common-source comparison square in an arbitrary category.
Source: the final inversion step of the open-composition node. Cancel the
common-source isomorphism and use its supplied comparison equation. -/
private theorem smoothTrace_inverse_comparison_square
    {C : Type*} [Category C] {M A B : C}
    (cf : M ≅ A) (ch : M ≅ B) (r : B ≅ A)
    (h : ch.hom ≫ r.hom = cf.hom) : ch.inv = r.hom ≫ cf.inv := by
  apply (cancel_epi ch.hom).1
  rw [ch.hom_inv_id, ← Category.assoc, h, cf.hom_inv_id]

/-- Map the inverse common-source comparison without unfolding the functor.
Source: the same final inversion step, after the constructible inclusion.
First invert the abstract square, then use functoriality of mapped isomorphisms. -/
private theorem smoothTrace_map_inverse_comparison_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {M A B : C}
    (cf : M ≅ A) (ch : M ≅ B) (r : B ≅ A)
    (h : ch.hom ≫ r.hom = cf.hom) :
    F.mapIso ch.symm = F.mapIso r ≪≫ F.mapIso cf.symm := by
  have he : ch.symm = r ≪≫ cf.symm :=
    Iso.ext (smoothTrace_inverse_comparison_square cf ch r h)
  rw [he, Functor.mapIso_trans]

/-- Cancel a mapped inverse unit comparison in an abstract square.
Source: the map-square to isomorphism-square step of the composition node.
Compose with the mapped forward unit comparison and use functoriality. -/
private theorem smoothTrace_comp_eq_of_map_inv
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {U V : C}
    (e : U ≅ V) {M N : D} (a : M ⟶ N) (b : N ⟶ F.obj U) (c : M ⟶ F.obj V)
    (h : a ≫ b = c ≫ F.map e.inv) : a ≫ b ≫ F.map e.hom = c := by
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp, e.inv_hom_id,
    F.map_id, Category.comp_id]

/-- Inverting a common-source comparison square gives the required open-composition
formula for purity. Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Step 8.
Apply the reconstructed trace formula to each map, cancel the two comparison
isomorphisms in the supplied square, and map the resulting inverse equation through
the inclusion. The equality of reconstructed comparisons is a geometric input. -/
private theorem smoothPurityIso_comp_of_reconstructed_traces
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z)
    [SmoothOfRelativeDimension d (f ≫ j).left]
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (cf : M ≅ (boundedConstructibleUpperShriek
      ℓ f).obj (𝟙_ _))
    (ch : M ≅ (boundedConstructibleUpperShriek
      ℓ (f ≫ j)).obj (𝟙_ _))
    (r : (boundedConstructibleUpperShriek
        ℓ (f ≫ j)).obj (𝟙_ _) ≅
      (boundedConstructibleUpperShriek
        ℓ f).obj (𝟙_ _))
    (hf : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ cf.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ f).counit.app (𝟙_ _))
    (hh : smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ (f ≫ j)).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ ch.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ (f ≫ j)).counit.app (𝟙_ _))
    (hcomp : ch.hom ≫ r.hom = cf.hom) :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso r ≪≫ smoothPurityIso ℓ f d := by
  let I := (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have hh' := smoothPurityIso_eq_of_reconstructed_trace ℓ (f ≫ j) d a ch hh
  have hf' := smoothPurityIso_eq_of_reconstructed_trace ℓ f d a cf hf
  calc
    smoothPurityIso ℓ (f ≫ j) d = I.mapIso ch.symm ≪≫ a := hh'
    _ = (I.mapIso r ≪≫ I.mapIso cf.symm) ≪≫ a :=
      congrArg (fun e ↦ e ≪≫ a) (smoothTrace_map_inverse_comparison_square I cf ch r hcomp)
    _ = I.mapIso r ≪≫ (I.mapIso cf.symm ≪≫ a) := Iso.trans_assoc _ _ _
    _ = I.mapIso r ≪≫ smoothPurityIso ℓ f d :=
      congrArg (fun e ↦ I.mapIso r ≪≫ e) hf'.symm

omit [SmoothOfRelativeDimension d f.left] in
/-- Complete the zero-dimensional normalization from its explicit trace formula.
Source: `lem-route-smooth-purity-iso-zero-of-is-open-immersion`, Step 3. Use the
coefficient unit as the realized object, the inverse live open-unit comparison as
c, and the canonical inverse zero-twist/zero-shift comparison as a. The general
reconstructed inverse formula then gives exactly the stated normalization. -/
private theorem smoothPurityIso_zero_of_trace_formula
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (htrace : smoothTrace ℓ j 0 =
      (boundedConstructibleLowerShriek ℓ j).map
          (((ObjectProperty.ι _).preimageIso
            (X := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
            (Y := boundedConstructibleTateTwist ℓ X 0 (2 * 0))
            ((tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
              ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)).inv ≫
            (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm := by
  have h := smoothPurityIso_eq_of_reconstructed_trace ℓ j 0
    (M := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    ((tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).symm htrace
  simpa only [Iso.symm_symm_eq] using h

/-- Blueprint `sk-thm-purity-transport`, étale case: **normalization of purity in relative
dimension zero**: for an open immersion `j`, the purity isomorphism `Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ(0)[0]` is
the canonical identification `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`); equivalently, the trace of `j` is the
counit `Rj_! Rj^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` read through it. -/
theorem smoothPurityIso_zero_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j.left] :
    smoothPurityIso ℓ j 0 =
      (ObjectProperty.ι _).mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j) ≪≫
        (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
        ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm :=
  sorry

/-- Invert the actual purity-map square obtained from trace transitivity.
Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Steps 7--8.
Use the canonical open-unit inverse as q in the preceding mate calculation,
compose with its inverse, and cancel the invertible actual purity map. Applying
the fully faithful inclusion gives the exact stated ambient composition formula.
Invertibility is supplied explicitly, rather than derived from the disputed
unconditional instance. The trace transitivity equation is the geometric input. -/
private theorem smoothPurityIso_comp_of_trace_transitivity
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left]
    (hf : IsIso (smoothPurityMap ℓ f d)) (hh : IsIso (smoothPurityMap ℓ (f ≫ j) d))
    (htrace : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek ℓ j).map
          (smoothTrace ℓ f d ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          ℓ j).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d := by
  let := hf
  let := hh
  let G := boundedConstructibleUpperShriek ℓ f
  let r := (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app (𝟙_ _) ≪≫
    G.mapIso (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)
  have hm := smoothPurityMap_comp_of_trace_transitivity ℓ f d j
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv htrace
  have hs : smoothPurityMap ℓ (f ≫ j) d ≫ r.hom = smoothPurityMap ℓ f d := by
    exact smoothTrace_comp_eq_of_map_inv G _ _ _ _ hm
  exact smoothTrace_map_inverse_comparison_square (ObjectProperty.ι _)
    (asIso (smoothPurityMap ℓ f d)) (asIso (smoothPurityMap ℓ (f ≫ j) d)) r hs

/-- Blueprint `sk-prop-sp-composition`, case of an open immersion: **compatibility of purity
with composition with an open immersion**: for `f` smooth of pure relative dimension `d` and an
open immersion `j` on its target, the purity isomorphism of `f ≫ j` is that of `f` precomposed with
`R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`, the composition isomorphism of the exceptional
inverse images followed by purity for `j` (`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
theorem smoothPurityIso_comp_openImmersion {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (j : Y ⟶ Z) [IsOpenImmersion j.left]
    [SmoothOfRelativeDimension d (f ≫ j).left] :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
