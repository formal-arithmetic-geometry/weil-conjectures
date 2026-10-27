/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.SixFunctors.CompositionProjectionMate
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ProEtaleCompositionTowerNormalization
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.AmbientProperOpenPasting
import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.SixFunctors.CartesianCompactSupportCompositor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import Sheaf.Paper.CompactSupportSiteCoherence

/-! # Compatible triangles and the canonical projection compositor

Source: main-20261015, fix-prop-projection-formula, composition clause; Stacks
Tags 0F7J and 0F7K (blueprint: lem-sf-projection-compatible-triangle-assembly).
The finite comparison is to the independently defined canonical origin compositor.
Systems retain their intrinsic maps before evaluation; their mate is not asserted invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genInjectivity false
universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly

variable {F : WeilConjectures.FiniteFieldDatum.{u}}

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem tensor_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    {T : Scheme.{u}} {K L : ProperOpenDerived A T}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T L) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T
      (((ProperOpenTensor A T).obj K).obj L) := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK
  obtain ⟨L₀, _, ⟨eL⟩⟩ := hL.1
  let M := ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K₀).obj L₀
  let e : N.obj M ≅ ((ProperOpenTensor A T).obj K).obj L :=
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K₀).app L₀ ≪≫ MonoidalCategory.tensorIso eK eL
  obtain ⟨a, b, hLt⟩ := hL.2
  have hKb := (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
    hK₀).bounded
  have hKb' := _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso eK hKb
  obtain ⟨c, d, hKcd⟩ :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hKb'
  have hT := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
    hKcd hLt
  have hb := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨_, _, hT⟩
  have hb' := _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm hb
  have hp := (Functor.bounded_of_bounded_mapDerivedCategory_obj
    (comparisonUpperStar (ModuleCat.{u + 1} A) T) hb').1
  exact ⟨M, hp, ⟨e⟩⟩

variable (F) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)] [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)

/-- The specified compositor on a triangle, using the factor compactifications of
j q, i s and (j b)(p s). The last candidate is indexed by the equal composite (j q)(i s).
Source: Stacks 0F7J (blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def canonical
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ)
      X.obj.left).FullSubcategory) :
    (compact (ordinary F Λ) j q ⋙ compact (ordinary F Λ) i s).obj K.obj ⟶
      (compact (ordinary F Λ) (j ≫ b) (p ≫ s)).obj K.obj :=
  candidateCompositor Λ (f := (j ≫ q).hom.left) (g := (i ≫ s).hom.left)
    (WeilConjectures.sixFunctorFactorCompactification j q
      ‹IsOpenImmersion ((geometry F).map j)› ‹IsProper ((geometry F).map q)›
      (j ≫ q) rfl)
    (WeilConjectures.sixFunctorFactorCompactification i s
      ‹IsOpenImmersion ((geometry F).map i)› ‹IsProper ((geometry F).map s)›
      (i ≫ s) rfl)
    (WeilConjectures.sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
      (mappedCompositeOpen (geo := geometry F) j b)
      (mappedCompositeProper (geo := geometry F) p s) ((j ≫ q) ≫ (i ≫ s)) (by
        simp only [Category.assoc]
        rw [← Category.assoc q i s, ← hb]
        simp only [Category.assoc])) K

/-- The projection equation with the canonical, rather than raw, compositor.
The two origin proofs merely admit K and K tensor P_f P_g L to the full origin category.
They are conclusions of the assembly theorem, not extra input assumptions there.
Source: blueprint projection composition display; Stacks 0F7J
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def ProjectionEquation (K : ProperOpenDerived Λ X.obj.left)
    (L : ProperOpenDerived Λ Z.obj.left)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left K)
    (hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left
      ((ordinaryTensor F Λ).tensor X |>.obj
        (K, ((ordinary F Λ).P (j ≫ q)).obj (((ordinary F Λ).P (i ≫ s)).obj L)))) : Prop :=
  projection (ordinary F Λ) (ordinaryTensor F Λ) i s
      ((compact (ordinary F Λ) j q).obj K) L ≫
    (compact (ordinary F Λ) i s).map
      (projection (ordinary F Λ) (ordinaryTensor F Λ) j q K
        (((ordinary F Λ).P (i ≫ s)).obj L)) ≫
    canonical F Λ j b q p i s hb ⟨_, hT⟩ ≫
    (compact (ordinary F Λ) (j ≫ b) (p ≫ s)).map
      ((ordinaryTensor F Λ).tensor X |>.map
        (Prod.mkHom (𝟙 K) ((trianglePull (ordinary F Λ) j b q p i s hb).hom.app L))) =
  ((ordinaryTensor F Λ).tensor Z).map
      (Prod.mkHom (canonical F Λ j b q p i s hb ⟨K, hK⟩) (𝟙 L)) ≫
    projection (ordinary F Λ) (ordinaryTensor F Λ) (j ≫ b) (p ≫ s) K L

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

/-- The two normalized identity-square equations, written at their actual components.
Together with the sId and jId identifications these are the identity cases of the
triangle compositor. Source: Stacks 0F7B and 0F7K
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def IdentityCompatibility (c : Calculus.{u, g, h, v, w} G geo) : Prop :=
  (∀ {U T : G} (a : U ⟶ T) [IsOpenImmersion (geo.map a)] [QuasiCompact (geo.map a)]
    (h₀ : a ≫ (𝟙 T) = (𝟙 U) ≫ a) (M : c.D U),
    (c.gamma a (𝟙 U) (𝟙 T) a h₀).app M ≫ (c.sId T).hom.app ((c.J a).obj M) =
      (c.J a).map ((c.sId U).hom.app M)) ∧
  (∀ {U T : G} (a : U ⟶ T) [IsProper (geo.map a)]
    (h₀ : (𝟙 U) ≫ a = a ≫ (𝟙 T)) (M : c.D U),
    (c.gamma (𝟙 U) a a (𝟙 T) h₀).app M ≫ (c.S a).map ((c.jId U).hom.app M) =
      (c.jId T).hom.app ((c.S a).obj M))

/-- Just the system projection equality for every supplied triangle and arbitrary inputs.
Unlike TriangleLaws, this predicate makes no invertibility assertion about the system mate.
Source: blueprint system clause before evaluation
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def SystemEquation (c : Calculus.{u, g, h, v, w} G geo) (t : TensorData c) : Prop :=
  ∀ {X V W Y B Z : G} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    [IsProper (geo.map s)] (hb : b ≫ p = q ≫ i) (K : c.D X) (L : c.D Z),
    leftMap c t j b q p i s hb K L = rightMap c t j b q p i s hb K L

/-- The finite assembly clauses for every compatible Cartesian triangle: identification
on all bounded-below origin inputs, and the canonical projection identity with finite Tor
only on L. Source: Stacks 0F7J and the blueprint composition calculation
(blueprint: lem-sf-projection-compatible-triangle-assembly). -/
def FiniteAssembly (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : Prop :=
  ∀ {X V W Y B Z : Spaces F} (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y)
    (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)] [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (_sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left),
    (∀ K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ)
        X.obj.left).FullSubcategory,
      (alpha (ordinary F Λ) j b q p i s hb).app K.obj =
        canonical F Λ j b q p i s hb K) ∧
    ∀ (K : ProperOpenDerived Λ X.obj.left) (L : ProperOpenDerived Λ Z.obj.left),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X.obj.left K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z.obj.left L →
      ∃ hK hT, ProjectionEquation F Λ j b q p i s hb K L hK hT

private theorem left_identity_hom {D : Type v} [Category.{w} D]
    {J P : D ⥤ D} (a : J ⊣ P) (e : P ≅ 𝟭 D) (M : D) :
    a.homEquiv M M ((a.leftAdjointIdIso e).hom.app M) = e.inv.app M := by
  have h := unit_conjugateEquiv_symm Adjunction.id a e.inv M
  change 𝟙 M ≫ e.inv.app M =
    a.unit.app M ≫ P.map ((a.leftAdjointIdIso e).hom.app M) at h
  exact (Category.id_comp _).symm.trans h |>.symm

private theorem left_identity_eq {D : Type v} [Category.{w} D]
    {J P : D ⥤ D} (a : J ⊣ P) (e : P ≅ 𝟭 D) :
    a.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) = a.leftAdjointIdIso e := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (a.homEquiv M M).injective
  rw [left_identity_hom]
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Functor.whiskerLeft_app, Functor.id_obj,
    Iso.symm_hom, Category.id_comp]
    using a.homEquiv_leftAdjointUniq_hom_app (Adjunction.id.ofNatIsoRight e.symm) M

private theorem left_identity_transport {D : Type v} [Category.{w} D]
    {J P J' P' : D ⥤ D} (a : J ⊣ P) (a' : J' ⊣ P')
    (e : P ≅ P') (d : P' ≅ 𝟭 D) :
    a.leftAdjointIdIso (e ≪≫ d) =
      (a.ofNatIsoRight e).leftAdjointUniq a' ≪≫ a'.leftAdjointIdIso d := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((a.ofNatIsoRight e).homEquiv M M).injective
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Adjunction.homEquiv_naturality_right]
  have h := (a.ofNatIsoRight e).homEquiv_leftAdjointUniq_hom_app a' M
  change ((a.ofNatIsoRight e).homEquiv M (J'.obj M))
    (((a.ofNatIsoRight e).leftAdjointUniq a').hom.app M) = a'.unit.app M at h
  rw [h, Adjunction.homEquiv_ofNatIsoRight_apply, left_identity_hom]
  change (d.inv.app M ≫ e.inv.app M) ≫ e.hom.app M =
    a'.homEquiv M M ((a'.leftAdjointIdIso d).hom.app M)
  rw [left_identity_hom, Category.assoc, e.inv_hom_id_app, Category.comp_id]

private theorem identity_square_transport
    {C D : Type*} [Category C] [Category D]
    {A A' : C ⥤ D} {S S' : C ⥤ C} {T T' : D ⥤ D}
    (a : A ≅ A') (r : S ≅ S') (t : T ≅ T')
    (e : S' ≅ 𝟭 C) (d : T' ≅ 𝟭 D)
    (γ : S ⋙ A ⟶ A ⋙ T) (γ' : S' ⋙ A' ⟶ A' ⋙ T')
    (hc : ∀ M, γ.app M ≫ t.hom.app (A.obj M) ≫ T'.map (a.hom.app M) =
      a.hom.app (S.obj M) ≫ A'.map (r.hom.app M) ≫ γ'.app M)
    (hu : ∀ M, γ'.app M ≫ d.hom.app (A'.obj M) = A'.map (e.hom.app M))
    (M : C) :
    γ.app M ≫ (t ≪≫ d).hom.app (A.obj M) = A.map ((r ≪≫ e).hom.app M) := by
  apply (cancel_mono (a.hom.app M)).mp
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [show d.hom.app (A.obj M) ≫ a.hom.app M =
    T'.map (a.hom.app M) ≫ d.hom.app (A'.obj M) from (d.hom.naturality _).symm]
  rw [reassoc_of% (hc M)]
  rw [hu, ← A'.map_comp, ← a.hom.naturality]
  simp only [Functor.map_comp, Category.assoc, Functor.id_obj]

private theorem identity_square_transport_dual
    {C D : Type*} [Category C] [Category D]
    {A A' : C ⥤ D} {S S' : C ⥤ C} {T T' : D ⥤ D}
    (a : A ≅ A') (r : S ≅ S') (t : T ≅ T')
    (e : S' ≅ 𝟭 C) (d : T' ≅ 𝟭 D)
    (γ : A ⋙ T ⟶ S ⋙ A) (γ' : A' ⋙ T' ⟶ S' ⋙ A')
    (hc : ∀ M, γ.app M ≫ a.hom.app (S.obj M) ≫ A'.map (r.hom.app M) =
      t.hom.app (A.obj M) ≫ T'.map (a.hom.app M) ≫ γ'.app M)
    (hu : ∀ M, γ'.app M ≫ A'.map (e.hom.app M) = d.hom.app (A'.obj M))
    (M : C) :
    γ.app M ≫ A.map ((r ≪≫ e).hom.app M) = (t ≪≫ d).hom.app (A.obj M) := by
  apply (cancel_mono (a.hom.app M)).mp
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [show A.map (e.hom.app M) ≫ a.hom.app M =
    a.hom.app (S'.obj M) ≫ A'.map (e.hom.app M) from a.hom.naturality _]
  rw [reassoc_of% (a.hom.naturality (r.hom.app M))]
  rw [reassoc_of% (hc M)]
  rw [hu, d.hom.naturality]
  rfl

private theorem right_id_transport
    {D : Type*} [Category* D] {P S P' S' : D ⥤ D}
    (a : P ⊣ S) (b : P' ⊣ S') (e : P ≅ P') (d : P' ≅ 𝟭 D) :
    (conjugateIsoEquiv Adjunction.id a (e ≪≫ d)).symm =
      conjugateIsoEquiv a b e.symm ≪≫
        (conjugateIsoEquiv Adjunction.id b d).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact congr_app (conjugateEquiv_comp a b Adjunction.id e.inv d.inv).symm M


attribute [local irreducible] SemilinearProperOpen.P SemilinearProperOpen.J
  SemilinearProperOpen.jAdj SemilinearProperOpen.pId
  WeilConjectures.IntegralSystemRealization.CanonicalBridge.pull

open WeilConjectures.IntegralSystemRealization in
set_option maxRecDepth 2048 in
private theorem realized_sId (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o)
    (X : Spaces F) :
    (realizedSystems F l E o z).sId X =
      z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left := by
  change (conjugateIsoEquiv Adjunction.id (o.direct (𝟙 X.obj.left)).adj
    (z.canonicalBridge.pull l E (𝟙 X.obj.left) ≪≫
      SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X.obj.left)).symm = _
  exact right_id_transport (o.direct (𝟙 X.obj.left)).adj
    (SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) (𝟙 X.obj.left))
    (z.canonicalBridge.pull l E (𝟙 X.obj.left))
    (SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X.obj.left)

open WeilConjectures.IntegralSystemRealization in
set_option maxRecDepth 2048 in
private theorem realized_jId (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o)
    (X : Spaces F) :
    (realizedSystems F l E o z).jId X =
      z.canonicalBridge.shriek l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) X.obj.left := by
  change (o.extension (𝟙 X.obj.left)).adj.leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (z.canonicalBridge.pull l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E)
          X.obj.left).symm) = _
  exact (left_identity_eq (o.extension (𝟙 X.obj.left)).adj
    (z.canonicalBridge.pull l E (𝟙 X.obj.left) ≪≫
      SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X.obj.left)).trans
    (left_identity_transport (o.extension (𝟙 X.obj.left)).adj
      (SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) (𝟙 X.obj.left))
      (z.canonicalBridge.pull l E (𝟙 X.obj.left))
      (SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X.obj.left))

attribute [local irreducible] SemilinearProperOpen.gamma SemilinearProperOpen.R

attribute [local irreducible] Calculus.sId Calculus.jId
  SemilinearProperOpen.sId SemilinearProperOpen.jId
  WeilConjectures.IntegralSystemRealization.CanonicalBridge.push
  WeilConjectures.IntegralSystemRealization.CanonicalBridge.shriek

open WeilConjectures.IntegralSystemRealization in
set_option maxRecDepth 2048 in
private theorem realized_identities (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (o : Operations l E) (z : Realizations l E F o) :
    IdentityCompatibility (realizedSystems F l E o z) := by
  let c := realizedSystems F l E o z
  change IdentityCompatibility c
  have hg {U V W Z : Spaces F} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z)
      [IsOpenImmersion ((geometry F).map k)] [IsOpenImmersion ((geometry F).map i)]
      [QuasiCompact ((geometry F).map k)] [QuasiCompact ((geometry F).map i)]
      [IsProper ((geometry F).map r)] [IsProper ((geometry F).map p)]
      [IsOpenImmersion k.hom.left] [IsOpenImmersion i.hom.left]
      [QuasiCompact k.hom.left] [QuasiCompact i.hom.left]
      [IsProper r.hom.left] [IsProper p.hom.left]
      (h : k ≫ p = r ≫ i) :
      c.gamma k r p i h = z.properOpen.gamma k.hom.left r.hom.left
        p.hom.left i.hom.left (congrArg (fun f ↦ f.hom.left) h) := by
    change (mateEquiv _ _) ((mateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  constructor
  · intro U T a ha hqc h M
    have : IsOpenImmersion a.hom.left := ha
    have : QuasiCompact a.hom.left := hqc
    have : IsProper (𝟙 U : U ⟶ U).hom.left := by
      change IsProper (𝟙 U.obj.left)
      infer_instance
    have : IsProper (𝟙 T : T ⟶ T).hom.left := by
      change IsProper (𝟙 T.obj.left)
      infer_instance
    rw [hg a (𝟙 U) (𝟙 T) a h]
    change _ ≫ ((realizedSystems F l E o z).sId T).hom.app
      ((Operations.shriek l E o a.hom.left).obj M) =
        (Operations.shriek l E o a.hom.left).map
          (((realizedSystems F l E o z).sId U).hom.app M)
    refine (congrArg (fun e ↦
      (z.properOpen.gamma a.hom.left (𝟙 U.obj.left) (𝟙 T.obj.left) a.hom.left
        (congrArg (fun f ↦ f.hom.left) h)).app M ≫
          e.hom.app ((Operations.shriek l E o a.hom.left).obj M))
        (realized_sId F l E o z T)).trans ?_
    refine Eq.trans ?_ (congrArg (fun e ↦
      (Operations.shriek l E o a.hom.left).map (e.hom.app M))
        (realized_sId F l E o z U).symm)
    exact identity_square_transport
      (z.canonicalBridge.shriek l E a.hom.left)
      (z.canonicalBridge.push l E (𝟙 U.obj.left))
      (z.canonicalBridge.push l E (𝟙 T.obj.left))
      (SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) U.obj.left)
      (SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) T.obj.left)
      (z.properOpen.gamma a.hom.left (𝟙 U.obj.left) (𝟙 T.obj.left) a.hom.left
        (congrArg (fun f ↦ f.hom.left) h))
      (SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
        a.hom.left (𝟙 U.obj.left) (𝟙 T.obj.left)
        a.hom.left (congrArg (fun f ↦ f.hom.left) h))
      (z.properOpen.canonical a.hom.left (𝟙 U.obj.left) (𝟙 T.obj.left) a.hom.left
        (congrArg (fun f ↦ f.hom.left) h)) (by
        intro N
        exact (SemilinearProperOpen.gamma_identities
          (scalarRings l E) (scalarTransitions l E)).1 a.hom.left
          (congrArg (fun f ↦ f.hom.left) h) N) M
  · intro U T a ha h M
    have : IsProper a.hom.left := ha
    have : IsOpenImmersion (𝟙 U : U ⟶ U).hom.left := by
      change IsOpenImmersion (𝟙 U.obj.left)
      infer_instance
    have : IsOpenImmersion (𝟙 T : T ⟶ T).hom.left := by
      change IsOpenImmersion (𝟙 T.obj.left)
      infer_instance
    have : QuasiCompact (𝟙 U : U ⟶ U).hom.left := by
      change QuasiCompact (𝟙 U.obj.left)
      infer_instance
    have : QuasiCompact (𝟙 T : T ⟶ T).hom.left := by
      change QuasiCompact (𝟙 T.obj.left)
      infer_instance
    rw [hg (𝟙 U) a a (𝟙 T) h]
    change _ ≫ (Operations.push l E o a.hom.left).map
      (((realizedSystems F l E o z).jId U).hom.app M) =
        ((realizedSystems F l E o z).jId T).hom.app
          ((Operations.push l E o a.hom.left).obj M)
    refine (congrArg (fun e ↦
      (z.properOpen.gamma (𝟙 U.obj.left) a.hom.left a.hom.left (𝟙 T.obj.left)
        (congrArg (fun f ↦ f.hom.left) h)).app M ≫
          (Operations.push l E o a.hom.left).map (e.hom.app M))
        (realized_jId F l E o z U)).trans ?_
    refine Eq.trans ?_ (congrArg (fun e ↦
      e.hom.app ((Operations.push l E o a.hom.left).obj M))
        (realized_jId F l E o z T).symm)
    exact identity_square_transport_dual
      (z.canonicalBridge.push l E a.hom.left)
      (z.canonicalBridge.shriek l E (𝟙 U.obj.left))
      (z.canonicalBridge.shriek l E (𝟙 T.obj.left))
      (SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) U.obj.left)
      (SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) T.obj.left)
      (z.properOpen.gamma (𝟙 U.obj.left) a.hom.left a.hom.left (𝟙 T.obj.left)
        (congrArg (fun f ↦ f.hom.left) h))
      (SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
        (𝟙 U.obj.left) a.hom.left a.hom.left
        (𝟙 T.obj.left) (congrArg (fun f ↦ f.hom.left) h))
      (z.properOpen.canonical (𝟙 U.obj.left) a.hom.left a.hom.left (𝟙 T.obj.left)
        (congrArg (fun f ↦ f.hom.left) h)) (by
        intro N
        exact (SemilinearProperOpen.gamma_identities
          (scalarRings l E) (scalarTransitions l E)).2 a.hom.left
          (congrArg (fun f ↦ f.hom.left) h) N) M



attribute [local irreducible] originCompositionAmbient originCompactSupport
  towerCandidateComparison

private theorem canonical_eq
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ)
      X.obj.left).FullSubcategory) :
    (alpha (ordinary F Λ) j b q p i s hb).app K.obj =
      canonical F Λ j b q p i s hb K := by
  exact cartesianCompactSupportCompositor F Λ j b q p i s hb sq K

attribute [local irreducible] canonical candidateCompositor alpha projection
  trianglePull compact

set_option maxRecDepth 2048 in
private theorem finiteAssembly_of_comparison
    (hr : ∀ {X V W Y B Z : Spaces F} (j : X ⟶ V) (b : V ⟶ W)
      (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
      [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
      [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
      [QuasiCompact ((geometry F).map i)] [IsProper ((geometry F).map q)]
      [IsProper ((geometry F).map p)] [IsProper ((geometry F).map s)]
      (hb : b ≫ p = q ≫ i)
      (_sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
      (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ)
        X.obj.left).FullSubcategory),
      (alpha (ordinary F Λ) j b q p i s hb).app K.obj =
        canonical F Λ j b q p i s hb K)
    (hp : TriangleLaws (ordinary F Λ) (ordinaryTensor F Λ)) : FiniteAssembly F Λ := by
  intro X V W Y B Z j b q p i s _ _ _ _ _ _ _ _ hb sq
  constructor
  · exact hr j b q p i s hb sq
  intro K L hK hL
  have hL' := constructibleFiniteTor_leftDerivedFunctor_upperStar_obj
    (j ≫ q).hom.left
    (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj
      (i ≫ s).hom.left hL)
  have hT := tensor_origin Λ hK hL'
  have hT' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X.obj.left
      (((ordinaryTensor F Λ).tensor X).obj
        (K, ((ordinary F Λ).P (j ≫ q)).obj (((ordinary F Λ).P (i ≫ s)).obj L))) := by
    simpa only [ordinaryTensor, ordinary, ProperOpenPull, Functor.uncurry] using hT
  refine ⟨hK.plusEtaleOrigin, hT', ?_⟩
  have he := (hp j b q p i s hb).2.1 K L
  dsimp only [leftMap, rightMap] at he
  have hrK := hr j b q p i s hb sq ⟨K, hK.plusEtaleOrigin⟩
  have hrT := hr j b q p i s hb sq
    ⟨((ordinaryTensor F Λ).tensor X).obj
      (K, ((ordinary F Λ).P (j ≫ q)).obj (((ordinary F Λ).P (i ≫ s)).obj L)), hT'⟩
  dsimp only [ProjectionEquation]
  rw [← hrK, ← hrT]
  exact he

/-- Compatible triangles exist over every prescribed compactification, and their normalized
proper/open mates realize the canonical compositor and projection equation. All spaces
are finite type over the field, without separated structure maps. The finite level n+1
ranges over exactly the positive quotient levels. The operation datum is the recorded
six-functor operation datum, with no hypothesis asserting projection invertibility.
The system clause is intrinsic, before evaluation, and has arbitrary unbounded inputs.
Source: main-20261015 fix-prop-projection-formula, composition sentence; Stacks 0F7J--0F7K
(blueprint: lem-sf-projection-compatible-triangle-assembly).

Proof:
1. Finite type over a field implies Noetherian and qcqs (finite-type-over-Noetherian,
   locally-Noetherian-quasi-separated). Apply compatible-compactification-triangle to
   the supplied compactification of g. Properness gives finite type of both new spaces;
   Noetherian-open-subscheme gives quasi-compactness of every open. No absolute separatedness.
2. For its Cartesian square the clopen projector in ambient-proper-open-pasting is identity.
   The proper mate Gamma has restriction lambda inverse by open-tensor-normalization,
   mate-pasting and the adjunction triangle identities. Thus it is the actual open adjunct
   of etale-origin-proper-open-interchange, with the derived-open-restriction normalization.
3. Finite-site-tower-paste identifies the raw tower arrow after its canonical site input
   comparison with B_gf nu*(alpha_et). Unbounded-compact-support-comparisons supplies the
   bounded-below etale compositor; proper-open-coefficient-mate identifies the interchange
   with the map of step 2. Compact-support-site-coherence gives the same equation for
   canonical alpha. Cancel the invertible input comparison and conjugate the origin witness.
4. Pullback-tor-amplitude for g then f, and tensor-ctf clause (i), show K tensor P_f P_g L
   is bounded constructible, with no finite Tor assumption on K. Proetale-constructible-origin
   supplies bounded etale witnesses for it and K. Step 3 therefore applies to both components.
5. Composition-projection-mate is the equation for the raw alpha. Substitute step 3 at K
   and at the tensor input from step 4. The projections are def-exchange-projection's
   proper counit projection followed by the open tensor map. trianglePull inserts exactly
   the canonical comparison from P_f P_g L to P_gf L in the displayed direction.
6. Site coherence respects refinements and identities; thm-sf-comp-composition supplies
   associativity and units on origin inputs. Apply step 5 twice on each threefold path.
   Both reduce to the final projection after the same triple compositor tensor identity.
   Ambient-pasting gives the two identity-square equations and the normalized compositors.
7. For systems apply composition-projection-mate to the very same geometric triangle,
   using realizedSystems and realizedTensor. The raw alpha retains the intrinsic Gamma
   and all quotient transitions. Ambient pasting gives associativity and units before
   evaluation. No detection of derived maps by their evaluations or system-mate inverse.
-/
theorem projectionCompatibleTriangleAssembly
    (F : WeilConjectures.FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ)
    (_S : WeilConjectures.SixFunctorOperationDatum F C E (n + 1) (Nat.le_add_left 1 n)) :
    (∀ {X Y B Z : Spaces F} (f : X ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsOpenImmersion ((geometry F).map i)] [IsProper ((geometry F).map s)],
      ∃ (V W : Spaces F) (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B),
        IsOpenImmersion j.hom.left ∧ IsOpenImmersion b.hom.left ∧
        IsProper q.hom.left ∧ IsProper p.hom.left ∧ f = j ≫ q ∧ b ≫ p = q ≫ i ∧
        IsPullback b.hom.left q.hom.left p.hom.left i.hom.left ∧
        IsNoetherian V.obj.left ∧ IsNoetherian W.obj.left ∧
        QuasiCompact j.hom.left ∧ QuasiCompact b.hom.left ∧ QuasiCompact i.hom.left) ∧
    FiniteAssembly F (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1))) ∧
    Associativity (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1)))) ∧
    IdentityCompatibility
      (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1)))) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations C.l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations C.l E F o),
      SystemEquation (realizedSystems F C.l E o z) (realizedTensor F C.l E o z) ∧
      Associativity (realizedSystems F C.l E o z) ∧
      IdentityCompatibility (realizedSystems F C.l E o z) := by
  have hm := compositionProjectionMate F C.l C.different E n
  have ha := ambientProperOpenPasting F C.l C.different E n
  refine ⟨?_, ?_, hm.2.1, ⟨ha.1.gamma_vertical_id, ha.1.gamma_horizontal_id⟩, ?_⟩
  · intro X Y B Z f i s _ _ _ _ _
    have : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    have : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    have : QuasiCompact i.hom.left := inferInstance
    let d : Compactification (i.hom.left ≫ s.hom.left) :=
      ⟨B.obj.left, s.hom.left, i.hom.left, rfl, inferInstance, inferInstance⟩
    obtain ⟨e, he, c, hc, hqc, hcb, hcf, hb, hqb, hq, hsq, _, _⟩ :=
      exists_compatible_compactification_triangle f.hom.left
        (i.hom.left ≫ s.hom.left) d
    have := Y.property.1
    have := Y.property.2
    have := B.property.1
    have := B.property.2
    have := hb
    have := hqb
    have := hq
    have := hc
    have := hqc
    let W : Spaces F := ⟨Over.mk (e.g ≫ B.obj.hom), by
      change LocallyOfFiniteType (e.g ≫ B.obj.hom) ∧ QuasiCompact (e.g ≫ B.obj.hom)
      exact ⟨inferInstance, inferInstance⟩⟩
    let V : Spaces F :=
      ⟨Over.mk (pullback.snd e.g d.i ≫ Y.obj.hom), by
        change LocallyOfFiniteType (pullback.snd e.g d.i ≫ Y.obj.hom) ∧
          QuasiCompact (pullback.snd e.g d.i ≫ Y.obj.hom)
        exact ⟨inferInstance, inferInstance⟩⟩
    let q : V ⟶ Y := ⟨Over.homMk (pullback.snd e.g d.i) rfl⟩
    let p : W ⟶ B := ⟨Over.homMk e.g rfl⟩
    let b : V ⟶ W := ⟨Over.homMk (pullback.fst e.g d.i) (by
      change pullback.fst e.g d.i ≫ (e.g ≫ B.obj.hom) =
        pullback.snd e.g d.i ≫ Y.obj.hom
      rw [← Category.assoc, pullback.condition, Category.assoc, i.hom.w])⟩
    let j : X ⟶ V := ⟨Over.homMk c (by
      change c ≫ (pullback.snd e.g d.i ≫ Y.obj.hom) = X.obj.hom
      rw [← Category.assoc, hcf, f.hom.w])⟩
    refine ⟨V, W, j, b, q, p, hc, hb, hq, e.isProper, ?_, ?_, hsq,
      spaceNoetherian F V, spaceNoetherian F W, hqc, hqb, inferInstance⟩
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact hcf.symm
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact pullback.condition
  · apply finiteAssembly_of_comparison F _
    · intro X V W Y B Z j b q p i s _ _ _ _ _ _ _ _ hb sq K
      exact canonical_eq F _ j b q p i s hb sq K
    · exact hm.1
  · intro o z
    refine ⟨?_, (hm.2.2 o z).2, ?_⟩
    · intro X V W Y B Z j b q p i s _ _ _ _ _ _ _ _ hb K L
      exact ((hm.2.2 o z).1 j b q p i s hb).2.1 K L
    · exact realized_identities F C.l E o z

end AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly
