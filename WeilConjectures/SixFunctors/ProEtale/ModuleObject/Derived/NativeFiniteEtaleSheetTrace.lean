/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSplitHomDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSheetSumCompatibility

/-! # The unique native finite-etale sheet trace

The construction descends the canonical sums on finite splitting charts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- The pullbacks to finite splitting charts detect equality of module arrows.
Source: sheaf Hom descent on finite splitting charts.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
theorem nativeFiniteEtaleChart_hom_ext
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    {P Q : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f g : P ⟶ Q)
    (h : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).map f = (upperStar Λ c.map).map g) : f = g := by
  apply (Mod.forget _).map_injective
  apply split_chart_sheaf_hom_ext p
  intro c
  have hc := congrArg (fun v ↦ v.hom) (h c)
  have hn := (profinitePointModuleForgetPullbackIso Λ c.map).hom.naturality f
  have hm := (profinitePointModuleForgetPullbackIso Λ c.map).hom.naturality g
  change ((upperStar Λ c.map).map f).hom ≫ _ = _ at hn
  change ((upperStar Λ c.map).map g).hom ≫ _ = _ at hm
  rw [hc] at hn
  exact (cancel_epi ((profinitePointModuleForgetPullbackIso Λ c.map).hom.app P)).mp
    (hn.symm.trans hm)

private theorem conjugated_counit_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ E) (J : D ⥤ E)
    (a : H ≅ F ⋙ J) (ε : G ⋙ F ⟶ 𝟭 D)
    {P Q : C} (f : P ⟶ Q) :
    H.map (G.map (F.map f)) ≫
        (a.hom.app (G.obj (F.obj Q)) ≫ J.map (ε.app (F.obj Q)) ≫ a.inv.app Q) =
      (a.hom.app (G.obj (F.obj P)) ≫ J.map (ε.app (F.obj P)) ≫ a.inv.app P) ≫
        H.map f := by
  exact (Functor.whiskerLeft (F ⋙ G) a.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft F ε) J ≫ a.inv).naturality f

private theorem sheet_sum_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    {P Q : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : P ⟶ Q) (c : FiniteEtaleModuleChart p) :
    (upperStar Λ c.map).map ((lowerStar Λ p).map ((upperStar Λ p).map f)) ≫
        finiteEtaleTraceSheetSum Λ p Q c.map c.degree c.sheet c.over =
      finiteEtaleTraceSheetSum Λ p P c.map c.degree c.sheet c.over ≫
        (upperStar Λ c.map).map f := by
  classical
  simp only [finiteEtaleTraceSheetSum, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  exact conjugated_counit_naturality (upperStar Λ p) (lowerStar Λ p)
    (upperStar Λ c.map) (upperStar Λ (c.sheet j))
    (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j))
    (upperStarLowerStarAdjunction Λ p).counit f

/-- The chart formula uniquely specifies a trace, including for empty fibres.
Source: finite splitting descent and sheet-sum compatibility.
(blueprint: new-det-sp-native-finite-etale-sheet-trace).
Proof. Descend the compatible sums on all splitting charts. The chart pullbacks
jointly detect equality of module maps, so two such descents coincide. -/
theorem nativeFiniteEtaleSheetTrace_existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃! τ : (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P,
      FiniteEtaleTraceFormula Λ p P τ := by
  obtain ⟨τ, hτ⟩ := finiteEtaleSplitHom_exists Λ p _ P
    (finiteEtaleSheetSum Λ p P) (finiteEtaleSheetSum_compatible Λ p P)
  refine ⟨τ, hτ, ?_⟩
  intro σ hσ
  exact nativeFiniteEtaleChart_hom_ext Λ p σ τ (fun c ↦ (hσ c).trans (hτ c).symm)

/-- The unique descended trace on native condensed module sheaves.
Source: canonical finite sheet summation.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
def nativeFiniteEtaleSheetTrace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P :=
  (nativeFiniteEtaleSheetTrace_existsUnique Λ p P).exists.choose

/-- The constructed trace has exactly the specified sheet normalization.
Source: its unique specification.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
theorem nativeFiniteEtaleSheetTrace_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    FiniteEtaleTraceFormula Λ p P (nativeFiniteEtaleSheetTrace Λ p P) :=
  (nativeFiniteEtaleSheetTrace_existsUnique Λ p P).exists.choose_spec

/-- Naturality of the actual descended finite-etale trace.
Source: naturality of the ordinary counit on each sheet.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
theorem nativeFiniteEtaleSheetTrace_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    {P Q : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : P ⟶ Q) :
    (lowerStar Λ p).map ((upperStar Λ p).map f) ≫ nativeFiniteEtaleSheetTrace Λ p Q =
      nativeFiniteEtaleSheetTrace Λ p P ≫ f := by
  apply nativeFiniteEtaleChart_hom_ext Λ p
  intro c
  simp only [Functor.map_comp]
  rw [nativeFiniteEtaleSheetTrace_formula Λ p Q c,
    nativeFiniteEtaleSheetTrace_formula Λ p P c]
  exact sheet_sum_naturality Λ p f c

/-- The sheet trace as a natural transformation, rather than an unrelated arrow
at each object. Source: sheetwise counit naturality.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
def nativeFiniteEtaleSheetTraceNat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] : upperStar Λ p ⋙ lowerStar Λ p ⟶ 𝟭 _ where
  app P := nativeFiniteEtaleSheetTrace Λ p P
  naturality _ _ f := nativeFiniteEtaleSheetTrace_naturality Λ p f

/-- A reverse adjunction satisfies the chart formula precisely when its counit
is the fixed sheet trace.
Source: uniqueness of finite splitting descent.
(blueprint: new-det-sp-native-finite-etale-sheet-trace).
Proof. Apply uniqueness of the descended arrow at each object; the converse is
the formula already proved for the construction. -/
theorem nativeFiniteEtaleSheetCounit_eq_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (b : lowerStar Λ p ⊣ upperStar Λ p) :
    b.counit = nativeFiniteEtaleSheetTraceNat Λ p ↔
      ∀ P, FiniteEtaleTraceFormula Λ p P (b.counit.app P) := by
  constructor
  · intro h P
    rw [h]
    exact nativeFiniteEtaleSheetTrace_formula Λ p P
  · intro h
    apply NatTrans.ext
    funext P
    exact (nativeFiniteEtaleSheetTrace_existsUnique Λ p P).unique (h P)
      (nativeFiniteEtaleSheetTrace_formula Λ p P)

/-- The sheet normalization determines the entire reverse adjunction.
Source: uniqueness of the descended trace and of an adjunction with fixed counit.
(blueprint: new-det-sp-native-finite-etale-sheet-trace). -/
theorem nativeFiniteEtaleSheetAdjunction_unique
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (b b' : lowerStar Λ p ⊣ upperStar Λ p)
    (hb : ∀ P, FiniteEtaleTraceFormula Λ p P (b.counit.app P))
    (hb' : ∀ P, FiniteEtaleTraceFormula Λ p P (b'.counit.app P)) : b = b' := by
  apply Adjunction.ext_counit
  exact ((nativeFiniteEtaleSheetCounit_eq_iff Λ p b).mpr hb).trans
    ((nativeFiniteEtaleSheetCounit_eq_iff Λ p b').mpr hb').symm

end AlgebraicGeometry.ProEtale.CondensedRing
