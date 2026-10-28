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

The trace map `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`) is a `@[no_expose]` definition with
value `sorry`: its construction (by reduction to relative curves and the cycle class of the
diagonal) is not formalized. The purity isomorphism
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is *defined* from it, as the inverse
of its adjoint `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y` for `Rf_! ⊣ Rf^!`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap`). The following properties of the
trace are `sorry`ed:

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

/-- Blueprint `sk-def-sp-trace`: the **trace map** `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of a
morphism `f` smooth of pure relative dimension `d` (SGA 4, Exposé XVIII, Théorème 2.9). Its
construction is not formalized: see the module docstring for the properties that are assumed. -/
-- STATEMENT-DISPUTED: the witness theorem used below omits the finite orientation
-- normalization. smoothTrace_representing_not_unique_at_point proves that its actual
-- representing-pair predicate has distinct witnesses, even for an identity map.
@[no_expose]
noncomputable def smoothTrace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) := by
  classical
  exact if h : Nonempty (SmoothOfRelativeDimension d f.left) then
    (existsUnique_smoothTrace ℓ f d h.some
      (boundedConstructibleTateTwist ℓ X d (2 * d)) (Iso.refl _)
      (MonoidalCategoryStruct.tensorUnit
        (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) rfl).choose
  else
    0

attribute [local irreducible] smoothTrace

/-- The **purity map** `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`: the adjoint of the trace `Tr_f` for
`Rf_! ⊣ Rf^!`. -/
noncomputable def smoothPurityMap :
    boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _ (smoothTrace ℓ f d)

omit [SmoothOfRelativeDimension d f.left] in
/-- The chosen trace is recovered from its adjoint by the actual exceptional counit.
This is the formal trace-identification step of `def-route-smooth-trace`; it uses
only the two inverse laws of the adjunction hom equivalence. -/
private theorem smoothTrace_eq_adjunct :
    smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (smoothPurityMap ℓ f d) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _) := by
  calc
    smoothTrace ℓ f d =
        ((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).symm
          (smoothPurityMap ℓ f d) :=
      (((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).symm_apply_apply
        (smoothTrace ℓ f d)).symm
    _ = _ := (boundedConstructibleUpperShriekAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f).homEquiv_counit _ _ (smoothPurityMap ℓ f d)

omit [SmoothOfRelativeDimension d f.left] in
/-- The live open comparison preserves the two actual exceptional counits.
Source: `lem-route-smooth-purity-iso-zero-of-is-open-immersion`, Step 2.
The inverse right-adjoint comparison is the conjugate of the compactification
comparison on left adjoints. The mate-counit identity gives the equation directly. -/
private theorem smoothTrace_openComparison_counit
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).app K).inv ≫
      (boundedConstructibleUpperShriekAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K := by
  exact conjugateEquiv_counit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleUpperShriekAdjunction _ ℓ j)
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
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperShriekAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
        (𝟙_ _) ≫
      (boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  change (boundedConstructibleLowerShriek _ ℓ j).map
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
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        (t ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
      (boundedConstructibleUpperShriekAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) =
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
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map a ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
    smoothPurityMap ℓ f d = a := by
  change (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _
    (smoothTrace ℓ f d) = a
  rw [htrace, ← (boundedConstructibleUpperShriekAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ f).homEquiv_counit _ _ a]
  exact ((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).apply_symm_apply _

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
    (t : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⟶ L)
    (hrep : ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Function.Bijective (fun b : K ⟶ M ↦
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map b ≫ t)) :
    ∃ e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
        (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)),
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map e.hom ≫
          (boundedConstructibleUpperShriekAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _) =
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
            (((ObjectProperty.ι _).preimageIso
              (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv) ≫
          t ≫ u.hom := by
  let A : M ≅ boundedConstructibleTateTwist ℓ X d (2 * d) :=
    (ObjectProperty.ι _).preimageIso a
  obtain ⟨e, he, _⟩ := smoothTrace_normalizedComparison_unique
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
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
    (t : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⟶ L)
    (hrep : ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      Function.Bijective (fun b : K ⟶ M ↦
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map b ≫ t))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
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
    (t : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⟶ L)
    (s : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).obj M
      ⟶ N)
    (q : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L ⟶ N)
    (hs : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app M ≫ s =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map t ≫ q)
    (hq : q ≫ c.hom =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (b.hom ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _))
    (ht : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map a.inv ≫
        t ≫ b.hom)
    (hu : smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).map a.inv
        ≫ s ≫ c.hom) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (smoothTrace ℓ f d ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _) := by
  let H := boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j
  let ε := H.map (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
    (boundedConstructibleUpperShriekAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _)
  have hq' : q ≫ c.hom = H.map b.hom ≫ ε := by
    simpa only [H, ε, Functor.map_comp, Category.assoc] using hq
  have h := smoothTrace_unit_normalized_transitivity
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f) H
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j))
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
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (smoothTrace ℓ f d ≫ q) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _)) :
    smoothPurityMap ℓ (f ≫ j) d ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).hom.app (𝟙_ _) =
      smoothPurityMap ℓ f d ≫
        (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map q := by
  exact smoothTrace_composite_adjunct_square
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j) _ _ q htrace

omit [SmoothOfRelativeDimension d f.left] in
/-- The formal last step of the normalized trace construction. Once the geometric
comparison is an isomorphism and the chosen trace is its counit transpose, the actual
purity map is that comparison and is invertible. No comparison is chosen here. -/
private theorem isIso_smoothPurityMap_of_trace_formula
    (e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map e.hom ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
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
      (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ c.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
    ∃ e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
        (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
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
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).obj
            (𝟙_ (Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦
              Profinite.padicAlgClRingObj ℓ⟧)) ⟶ 𝟙_ _,
      ∀ K : Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ 𝟙_ _ ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
            (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).map a ≫ t) := by
  exact not_existsUnique_representing_trace_at_point ℓ (k := k)

end PointObstruction

/-- Blueprint `sk-thm-sp-qbar`: **smooth purity** (SGA 4, Exposé XVIII, Théorème 3.2.5): the
adjoint of the trace, `ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, is an isomorphism. -/
-- STATEMENT-DISPUTED: the elaborated signature omits SmoothOfRelativeDimension d f.left.
-- For a nonempty point and f = identity, d = 1 would identify the unit with a complex
-- concentrated in degree -2. The intended smoothness hypothesis requires an upstream
-- signature correction; it cannot be supplied by a proof of the current statement.
-- smoothPurityMap_point_dimension_one_not_isIso certifies this counterexample for a
-- separably closed point, independently of the trace choice and before this instance.
instance isIso_smoothPurityMap : IsIso (smoothPurityMap ℓ f d) :=
  sorry

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. It is the inverse of
the adjoint of the trace (`smoothPurityMap`), after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  (ObjectProperty.ι _).mapIso (asIso (smoothPurityMap ℓ f d)).symm

omit [SmoothOfRelativeDimension d f.left] in
/-- The normalized inverse formula for an explicitly reconstructed trace.
Source: `def-pur-condensed-smooth-purity-iso` and the last step of
`lem-route-smooth-purity-iso-comp-open-immersion`. The preceding helper constructs the
comparison before the disputed purity instance; here equality of its hom with the
actual adjunct identifies its inverse with the already defined purity isomorphism. -/
private theorem smoothPurityIso_eq_of_reconstructed_trace
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (c : M ≅ (boundedConstructibleUpperShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ c.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
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

omit [SmoothOfRelativeDimension d f.left] in
/-- Inverting a common-source comparison square gives the required open-composition
formula for purity. Source: `lem-route-smooth-purity-iso-comp-open-immersion`, Step 8.
Apply the reconstructed trace formula to each map, cancel the two comparison
isomorphisms in the supplied square, and map the resulting inverse equation through
the inclusion. The equality of reconstructed comparisons is a geometric input. -/
private theorem smoothPurityIso_comp_of_reconstructed_traces
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (j : Y ⟶ Z)
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (a : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (cf : M ≅ (boundedConstructibleUpperShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _))
    (ch : M ≅ (boundedConstructibleUpperShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).obj (𝟙_ _))
    (r : (boundedConstructibleUpperShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).obj (𝟙_ _) ≅
      (boundedConstructibleUpperShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (𝟙_ _))
    (hf : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ cf.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _))
    (hh : smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).map
          (((ObjectProperty.ι _).preimageIso
            (X := M) (Y := boundedConstructibleTateTwist ℓ X d (2 * d)) a).inv ≫ ch.hom) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ j)).counit.app (𝟙_ _))
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
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (((ObjectProperty.ι _).preimageIso
            (X := 𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
            (Y := boundedConstructibleTateTwist ℓ X 0 (2 * 0))
            ((tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
              ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm)).inv ≫
            (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _)) :
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

private theorem representing_trace_of_iso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M : C} {L : D} (e : M ≅ G.obj L) :
    ∀ K : C, Function.Bijective
      (fun b : K ⟶ M ↦ F.map b ≫ F.map e.hom ≫ adj.counit.app L) := by
  intro K
  constructor
  · intro a b hab
    change F.map a ≫ F.map e.hom ≫ adj.counit.app L =
      F.map b ≫ F.map e.hom ≫ adj.counit.app L at hab
    have h' := congrArg (adj.homEquiv K L) hab
    have hc : (adj.homEquiv (G.obj L) L) (adj.counit.app L) = 𝟙 _ := by
      rw [adj.homEquiv_unit, adj.right_triangle_components]
    have h'' : a ≫ e.hom = b ≫ e.hom := by
      simp only [← Category.assoc, ← F.map_comp,
        adj.homEquiv_naturality_left, hc, Category.comp_id] at h'
      exact h'
    exact (cancel_mono e.hom).1 h''
  · intro y
    refine ⟨adj.homEquiv K L y ≫ e.inv, ?_⟩
    change F.map (adj.homEquiv K L y ≫ e.inv) ≫ F.map e.hom ≫
      adj.counit.app L = y
    rw [← Category.assoc, ← F.map_comp, Category.assoc, e.inv_hom_id,
      Category.comp_id]
    exact (adj.homEquiv_counit K L (adj.homEquiv K L y)).symm.trans
      ((adj.homEquiv K L).symm_apply_apply y)

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
  let D_X := Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  let D_Y := Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  let M := boundedConstructibleTateTwist ℓ X 0 (2 * 0)
  let U := 𝟙_ D_Y
  let a : (𝟙_ D_X).obj ≅ M.obj :=
    (tateTwistDerivedZeroIso ℓ X.left).symm ≪≫
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _).symm
  let A : (𝟙_ D_X) ≅ M := (ObjectProperty.ι _).preimageIso a
  let c := boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j
  let e : M ≅
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj U :=
    A.symm ≪≫ c.symm
  let adj := boundedConstructibleUpperShriekAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ j
  let hsm : SmoothOfRelativeDimension 0 j.left := inferInstance
  let hE := existsUnique_smoothTrace ℓ j 0 hsm M (Iso.refl _)
    U rfl
  have htrace : smoothTrace ℓ j 0 =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map e.hom ≫
        adj.counit.app U := by
    have heq : smoothTrace ℓ j 0 = hE.choose := by
      rw [smoothTrace, dif_pos (show Nonempty (SmoothOfRelativeDimension 0 j.left)
        from ⟨hsm⟩)]
    rw [heq]
    exact hE.unique hE.choose_spec.1 (representing_trace_of_iso adj e)
  smoothPurityIso_zero_of_trace_formula ℓ j
    htrace

omit [SmoothOfRelativeDimension d f.left] in
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
    (hf : IsIso (smoothPurityMap ℓ f d)) (hh : IsIso (smoothPurityMap ℓ (f ≫ j) d))
    (htrace : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f j).inv.app
          (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫ smoothTrace ℓ (f ≫ j) d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).map
          (smoothTrace ℓ f d ≫ (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv) ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app (𝟙_ _)) :
    smoothPurityIso ℓ (f ≫ j) d =
      (ObjectProperty.ι _).mapIso
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
            (boundedConstructibleUpperShriek _ ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d := by
  let := hf
  let := hh
  let G := boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f
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
            (boundedConstructibleUpperShriek _ ℓ f).mapIso
              (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)) ≪≫
        smoothPurityIso ℓ f d :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
