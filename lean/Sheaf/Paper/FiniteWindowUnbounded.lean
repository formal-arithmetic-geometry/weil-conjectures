/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.Paper.ConstructibleIndExtBound
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt

/-!
# Lower-tail vanishing without a lower cohomology bound

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
sk-lem-finite-window-unbounded.md and its proof (blueprint: det-finite-window-unbounded).

The two statements give the finite-extension and algebraic-closure coefficient cases.
IndCons is Mathlib's filtered-colimit closure of finite constant-model constructibility.
Dic membership is imposed on every cohomology sheaf in the ordinary derived category.
The Ext hypothesis uses Mathlib's Ext with its standard size convention, canonically
identified with ambient derived morphisms by `CategoryTheory.Abelian.Ext.homAddEquiv`.
The proof reuses the source library's generic left-complete devissage on the strict
lower tail and then attaches the boundary cohomology layer by a truncation triangle.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The single-degree identification between Ext and derived morphisms. -/
private theorem hom_single_of_ext_bound
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (C B : A) (d : ℕ) (q : ℤ) (hq : q ≤ -(d : ℤ) - 1)
    (hExt : Subsingleton
      (@Abelian.Ext _ _ _ (HasExt.standard _) C B (-q).toNat)) :
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      (DerivedCategory.singleFunctor A q).obj B) := by
  have : HasExt A := HasExt.standard A
  have hcast : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
  have : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦((-q).toNat : ℤ)⟧) :=
    Equiv.subsingleton (Abelian.Ext.homEquiv (X := C) (Y := B)).symm
  have hshift : Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      ((DerivedCategory.singleFunctor A 0).obj B)⟦-q⟧) := by
    simpa only [hcast] using this
  let e := ((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app B
  exact ⟨fun f g ↦ by
    have hfg := hshift.elim (f ≫ e.inv) (g ≫ e.inv)
    simpa using congrArg (fun k ↦ k ≫ e.hom) hfg⟩

/-- Apply left-complete devissage below the cutoff, then attach its boundary layer.
The auxiliary property includes zero so truncations preserve it without requiring
any additional closure property of the original class of sheaves. -/
private theorem hom_lower_tail_of_ext
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [HasLimitsOfShape (Discrete ℕ) A]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (C : A) (d : ℕ)
    (hExt : ∀ B, P B → ∀ r : ℕ, d < r →
      Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r))
    (L : DerivedCategory A) (hL : DerivedCategory.homologyProperty P L)
    (hvanish : ∀ q : ℤ, -(d : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor A q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶ L) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let P₀ : ObjectProperty A := fun B ↦ P B ∨ IsZero B
  have : P₀.ContainsZero := ⟨⟨HasZeroObject.zero.choose, isZero_zero A, Or.inr (isZero_zero A)⟩⟩
  have : P₀.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.elim
    (fun h ↦ Or.inl (P.prop_of_iso e h)) (fun h ↦ Or.inr (h.of_iso e.symm))⟩
  let N : ℤ := -(d : ℤ) - 1
  let S := (DerivedCategory.singleFunctor A 0).obj C
  have hv : ∀ B, P₀ B → ∀ q ≤ N,
      ∀ f : S ⟶ (DerivedCategory.singleFunctor A q).obj B, f = 0 := by
    intro B hB q hq f
    rcases hB with hB | hB
    · exact (hom_single_of_ext_bound C B d q hq
        (hExt B hB (-q).toNat (by dsimp [N] at hq; omega))).elim f 0
    · exact ((DerivedCategory.singleFunctor A q).map_isZero hB).eq_of_tgt f 0
  have hL₀ : DerivedCategory.homologyProperty P₀ L := fun q ↦ Or.inl (hL q)
  have : L.IsLE N := (DerivedCategory.isLE_iff L N).mpr hvanish
  let T := (t.triangleLTGE N).obj L
  have hT := t.triangleLTGE_distinguished N L
  have h₁ : DerivedCategory.homologyProperty P₀ T.obj₁ :=
    (DerivedCategory.homologyProperty P₀).prop_of_iso
      ((t.truncLEIsoTruncLT (N - 1) N (by omega)).app L)
      (DerivedCategory.homologyProperty_truncLE hL₀ (N - 1))
  have h₃ : DerivedCategory.homologyProperty P₀ T.obj₃ :=
    DerivedCategory.homologyProperty_truncGE hL₀ N
  have : T.obj₁.IsLE (N - 1) := inferInstanceAs (t.IsLE T.obj₁ (N - 1))
  have : T.obj₃.IsGE N := inferInstanceAs (t.IsGE T.obj₃ N)
  have : T.obj₃.IsLE N := inferInstanceAs (t.IsLE ((t.truncGE N).obj L) N)
  refine subsingleton_of_forall_eq 0 fun f ↦ ?_
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f
    (DerivedCategory.eq_zero_of_isGE_of_isLE_self N hv N T.obj₃ h₃ le_rfl _)
  rw [hg, DerivedCategory.eq_zero_of_isLE N hv T.obj₁ h₁ g, zero_comp]

/-- Lower-tail vanishing for a finite coefficient subextension, with no lower bound on L.
Source: blueprint main-20261015, sk-lem-finite-window-unbounded, statement and proof
(blueprint: det-finite-window-unbounded).

Proof:
1. The existing constructibleInd_extBound extends the supplied bound to every
ind-constructible sheaf B. For q <= -d_C-1, Ext.homEquiv and the single-functor
shift isomorphism identify Hom(C[0], B[-q]) with Ext^(-q)(C,B), which is zero.
2. Enlarge the cohomology property by adjoining zero objects; this requires no
extra hypothesis and is preserved by good truncations. Repleteness of pro-etale
abelian sheaves transfers to modules and gives exact countable products.
Grothendieckness gives K-injective resolutions.
3. Put N=-d_C-1. The existing source-library eq_zero_of_isLE proves vanishing
for the strict tail tau_lt(N)L, supported in degrees <= N-1. Its proof uses
bounded devissage and the homotopy-limit triangle of the Postnikov truncations;
the one-degree margin also kills maps to every shifted tower term.
4. In tau_lt(N)L -> L -> tau_ge(N)L, the last term is supported in degree N.
The existing single-degree devissage and step 1 kill Hom into that term.
Representable Hom exactness factors every morphism C[0] -> L through the strict
tail, where step 3 kills it. No lower cohomological bound is used. -/
theorem finiteWindow_unbounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X)
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X,
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  let : MonObj (condensedRingObj (Profinite.continuousMapRingObj E) X) :=
    (coefficientRing X (Mon.mk (Profinite.continuousMapRingObj E))).mon
  let A := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E) X)
  let : CountableAB4Star A := .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have : HasExactLimitsOfShape (Discrete ℕ) A := CountableAB4Star.ofShape ℕ
  exact hom_lower_tail_of_ext (A := A)
    (ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X))
    C d_C (fun B hB r hr ↦
      constructibleInd_extBound ℓ E _ (Or.inl rfl) X C hC d_C hExt B hB r hr)
    L hL hvanish

/-- Lower-tail vanishing for the condensed algebraic closure, with no lower bound on L.
Source: blueprint main-20261015, sk-lem-finite-window-unbounded, statement and proof
(blueprint: det-finite-window-unbounded).

Proof:
1. The existing constructibleInd_extBound extends the supplied bound to every
ind-constructible sheaf B. For q <= -d_C-1, Ext.homEquiv and the single-functor
shift isomorphism identify Hom(C[0], B[-q]) with Ext^(-q)(C,B), which is zero.
2. Enlarge the cohomology property by adjoining zero objects; this requires no
extra hypothesis and is preserved by good truncations. Repleteness of pro-etale
abelian sheaves transfers to modules and gives exact countable products.
Grothendieckness gives K-injective resolutions.
3. Put N=-d_C-1. The existing source-library eq_zero_of_isLE proves vanishing
for the strict tail tau_lt(N)L, supported in degrees <= N-1. Its proof uses
bounded devissage and the homotopy-limit triangle of the Postnikov truncations;
the one-degree margin also kills maps to every shifted tower term.
4. In tau_lt(N)L -> L -> tau_ge(N)L, the last term is supported in degree N.
The existing single-degree devissage and step 1 kill Hom into that term.
Representable Hom exactness factors every morphism C[0] -> L through the strict
tail, where step 3 kills it. No lower cohomological bound is used. -/
theorem finiteWindow_unbounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X)
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  let : MonObj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
    (coefficientRing X (Mon.mk (Profinite.padicAlgClRingObj ℓ))).mon
  let A := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  let : CountableAB4Star A := .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have : HasExactLimitsOfShape (Discrete ℕ) A := CountableAB4Star.ofShape ℕ
  exact hom_lower_tail_of_ext (A := A)
    (ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    C d_C (fun B hB r hr ↦
      constructibleInd_extBound ℓ ⟨⊥, inferInstance⟩ _ (Or.inr rfl) X C hC d_C hExt B hB r hr)
    L hL hvanish

end AlgebraicGeometry.ProEtale
