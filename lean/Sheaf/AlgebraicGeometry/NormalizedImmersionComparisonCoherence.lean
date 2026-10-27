/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import Sheaf.CategoryTheory.ImmersionComparisonNormalized
public import Sheaf.CategoryTheory.ImmersionComparisonComposition
import Sheaf.CategoryTheory.NormalizedComparisonBinaryRestriction
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Sheaf.CategoryTheory.NormalizedComparisonTowerRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Restriction-normalized immersion comparisons

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md, (2)--(3);
Stacks Project, proetale.tex, Tags 09AA and 09BN.
(blueprint: lem-sfb-normalized-immersion-comparison-coherence).

All structures below bundle parameters or clauses of this one conditional assertion.
The extension and inverse-image functors are the published arbitrary-ring functors.
No scalar-extension functor or comparison is constructed from a mere existence claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The schemes quantified over in the assertion, bundled with its two hypotheses.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev ImmersionComparisonBase :=
  { X : Scheme.{u} // IsLocallyNoetherian X ∧ CompactSpace X }

/-- Cartesian coefficient parameters, before imposing their identity and composition laws.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure ImmersionComparisonRings (I : Type v) where
  ring : ∀ (_r : I) (X : ImmersionComparisonBase.{u}),
    Sheaf (ProEt.topology X.val) CommRingCat.{u + 1}
  coefficient : ∀ (r : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    (proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj (ring r X) ≅ ring r S

namespace ImmersionComparisonRings

variable {I : Type v} (G : ImmersionComparisonRings.{u} I)

/-- Use the dependency's coefficient bundle without redefining module sheaves.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def object (r : I) (X : ImmersionComparisonBase.{u}) : LocallyClosedCoefficients.{u} where
  scheme := X.val
  locallyNoetherian := X.property.1
  compact := X.property.2
  ring := G.ring r X

/-- An immersion with exactly the given cartesian coefficient identification.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def arrow (r : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] : LocallyClosedCoefficientImmersion (G.object r S) (G.object r X) where
  hom := a
  immersion := inferInstance
  coefficient := G.coefficient r a

/-- Coherence means the actual inverse-image identity and composition identifications.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Cartesian : Prop where
  identity : ∀ (r : I) (X : ImmersionComparisonBase.{u}),
    G.arrow r (𝟙 X.val) = LocallyClosedCoefficientImmersion.identity (G.object r X)
  composition : ∀ (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b],
    G.arrow r (b ≫ a) = (G.arrow r a).comp (G.arrow r b)

/-- The ordinary unbounded derived category of the given coefficient ring sheaf.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev category (r : I) (X : ImmersionComparisonBase.{u}) :=
  DerivedCategory (proEtaleRingModules X.val (G.ring r X))

/-- Exact inverse image, localized termwise as in the dependency.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pull (r : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] : G.category r X ⥤ G.category r S :=
  (G.arrow r a).pull.mapDerivedCategory

/-- The dependency's extension, with the cartesian coefficient identification inserted.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def extend (E : LocallyClosedExtensionData.{u}) (r : I)
    {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val) [IsImmersion a] :
    G.category r S ⥤ G.category r X :=
  E.derived (S := G.object r S) (X := G.object r X) (G.arrow r a)

/-- Canonical restriction composition, using the actual module inverse-image compositor.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pullComp (hG : G.Cartesian) (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b] :
    G.pull r (b ≫ a) ≅ G.pull r a ⋙ G.pull r b :=
  eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) (hG.composition r a b)) ≪≫
    Functor.mapDerivedCategoryNatIso ((G.arrow r a).pullComp (G.arrow r b)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The published extension compositor, transported along cartesian coefficient coherence.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def gamma (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) (r : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b] :
    G.extend E r b ⋙ G.extend E r a ≅ G.extend E r (b ≫ a) :=
  D.gamma (G.arrow r a) (G.arrow r b) ≪≫
    eqToIso (congrArg E.derived (hG.composition r a b).symm)

/-- The identity restriction identification, read from the normalized extension identity.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def pullId (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) (r : I) (X : ImmersionComparisonBase.{u}) :
    G.pull r (𝟙 X.val) ≅ 𝟭 (G.category r X) :=
  eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) (hG.identity r X)) ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (D.identity (G.object r X)).symm _ ≪≫
        D.restriction (.identity (G.object r X))

/-- The supplied F and q, including exactly their identity and composition coherence.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (hG : G.Cartesian) :=
  { data : (Σ functor :
      ∀ (r s : I) (X : ImmersionComparisonBase.{u}), G.category r X ⥤ G.category s X,
      ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a],
    functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ functor r s S) //
    (∀ (r s : I) (X : ImmersionComparisonBase.{u}) (M : G.category r X),
    (data.2 r s (𝟙 X.val)).hom.app M ≫
        (data.1 r s X).map ((G.pullId E D hG r X).hom.app M) =
      (G.pullId E D hG s X).hom.app ((data.1 r s X).obj M)) ∧
    (∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b],
    immersionComparisonComposition
      (G.pull r a) (G.pull r b) (G.pull r (b ≫ a))
      (G.pull s a) (G.pull s b) (G.pull s (b ≫ a))
      (G.pullComp hG r a b) (G.pullComp hG s a b)
      (data.1 r s X) (data.1 r s S) (data.1 r s T)
      (data.2 r s a) (data.2 r s b) (data.2 r s (b ≫ a))) }

variable {G}

/-- The supplied functor component of the comparison parameters.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors.functor {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
    {hG : G.Cartesian} (F : G.Functors E D hG) (r s : I) (X : ImmersionComparisonBase.{u}) :
    G.category r X ⥤ G.category s X := F.val.1 r s X

/-- The supplied restriction comparison component of the parameters.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Functors.q {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
    {hG : G.Cartesian} (F : G.Functors E D hG) (r s : I)
    {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val) [IsImmersion a] :
    F.functor r s X ⋙ G.pull s a ≅ G.pull r a ⋙ F.functor r s S :=
  F.val.2 r s a

namespace Functors

variable {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
  {hG : G.Cartesian} (F : G.Functors E D hG)

/-- The type of comparison isomorphisms; no existence is included in this notation.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
abbrev Comparison (r s : I) {S X : ImmersionComparisonBase.{u}} (a : S.val ⟶ X.val)
    [IsImmersion a] := G.extend E r a ⋙ F.functor r s X ≅
      F.functor r s S ⋙ G.extend E s a

/-- The precise restriction normalization (N), including both restriction isomorphisms.
Source: node proof step 1 (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def Normalized {r s : I} {S X : ImmersionComparisonBase.{u}} {a : S.val ⟶ X.val}
    [IsImmersion a] (d : F.Comparison r s a) : Prop :=
  immersionComparisonNormalized (G.pull r a) (G.pull s a)
    (G.extend E r a) (G.extend E s a)
    (D.restriction (G.arrow r a)) (D.restriction (G.arrow s a))
    (F.functor r s X) (F.functor r s S) (F.q r s a) d

/-- The two separately supplied comparisons, including their normalization. In a clopen
case both are retained as input; their equality is a conclusion, not an assumption.
Source: blueprint proof (2) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Elementary where
  openComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (_ : IsOpenImmersion a), F.Comparison r s a
  closedComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (_ : IsClosedImmersion a), F.Comparison r s a
  openNormalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsOpenImmersion a),
    F.Normalized (openComparison r s a ha)
  closedNormalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsClosedImmersion a),
    F.Normalized (closedComparison r s a ha)

/-- The actual factorization composite: insert inverse gamma, the two given comparisons,
and gamma. All data are existing isomorphisms, with explicit functor associators.
Source: node proof steps 3--4 (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
def composite {r s : I} {S X T : ImmersionComparisonBase.{u}}
    {a : S.val ⟶ X.val} {b : T.val ⟶ S.val} [IsImmersion a] [IsImmersion b]
    (da : F.Comparison r s a) (db : F.Comparison r s b) : F.Comparison r s (b ≫ a) :=
  Functor.isoWhiskerRight (G.gamma E D hG r a b).symm (F.functor r s X) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (G.extend E r b) da ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight db (G.extend E s a) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (F.functor r s T) (G.gamma E D hG s a b)

/-- The additional natural isomorphisms t for one triple of labels r, s, t, with exactly
the stated restriction square. Nothing is assumed for other triples, and no associativity
of these tower isomorphisms is assumed.
Source: blueprint proof (3) (blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Tower (r s t : I) where
  iso : ∀ X : ImmersionComparisonBase.{u},
    F.functor r s X ⋙ F.functor s t X ≅ F.functor r t X
  compatible : ∀ {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (M : G.category r X),
    (G.pull t a).map ((iso X).hom.app M) ≫ (F.q r t a).hom.app M =
      (F.q s t a).hom.app ((F.functor r s X).obj M) ≫
        (F.functor s t S).map ((F.q r s a).hom.app M) ≫
          (iso S).hom.app ((G.pull r a).obj M)

/-- All the clauses asserted for the assembled comparisons. Factorization equations use
ordinary natural isomorphism equality, so two factorizations with equal composite maps
produce the very same comparison after equality transport.
Source: blueprint proof (2)--(3)
(blueprint: lem-sfb-normalized-immersion-comparison-coherence). -/
structure Coherent (B : F.Elementary)
    (d : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a], F.Comparison r s a) : Prop where
  normalized : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a], F.Normalized (d r s a)
  openComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsOpenImmersion a),
    d r s a = B.openComparison r s a ha
  closedComparison : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (ha : IsClosedImmersion a),
    d r s a = B.closedComparison r s a ha
  closedOpen : ∀ (r s : I) {S V X : ImmersionComparisonBase.{u}}
    (c : S.val ⟶ V.val) (v : V.val ⟶ X.val) [IsImmersion c] [IsImmersion v]
    (hc : IsClosedImmersion c) (hv : IsOpenImmersion v),
    d r s (c ≫ v) = F.composite (B.openComparison r s v hv) (B.closedComparison r s c hc)
  openClosed : ∀ (r s : I) {S Z X : ImmersionComparisonBase.{u}}
    (j : S.val ⟶ Z.val) (i : Z.val ⟶ X.val) [IsImmersion j] [IsImmersion i]
    (hj : IsOpenImmersion j) (hi : IsClosedImmersion i),
    d r s (j ≫ i) = F.composite (B.closedComparison r s i hi) (B.openComparison r s j hj)
  composition : ∀ (r s : I) {S X T : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) (b : T.val ⟶ S.val) [IsImmersion a] [IsImmersion b]
    (M : G.category r T),
    (F.functor r s X).map ((G.gamma E D hG r a b).hom.app M) ≫
        (d r s (b ≫ a)).hom.app M =
      (d r s a).hom.app ((G.extend E r b).obj M) ≫
        (G.extend E s a).map ((d r s b).hom.app M) ≫
          (G.gamma E D hG s a b).hom.app ((F.functor r s T).obj M)
  tower : ∀ (r s t : I) (H : F.Tower r s t) {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [IsImmersion a] (M : G.category r S),
    (F.functor s t X).map ((d r s a).hom.app M) ≫
        (d s t a).hom.app ((F.functor r s S).obj M) ≫
          (G.extend E t a).map ((H.iso S).hom.app M) =
      (H.iso X).hom.app ((G.extend E r a).obj M) ≫
        (d r t a).hom.app M

end Functors
end ImmersionComparisonRings

set_option Elab.async false
-- Keep the concrete coefficient functors shared while checking the localization equations.
set_option cleanup.letToHave false
attribute [local instance 30000] reductionModulesHasDerivedCategory

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback

private theorem derived_restriction_eq {E : LocallyClosedExtensionData.{u}}
    (D : E.DerivedCoherence) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :
    D.restriction a = Functor.mapDerivedCategoryCompNatIso (E.restriction a) ≪≫
      Functor.mapDerivedCategoryIdIso _ := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules S.scheme S.ring) (.up ℤ))
  intro K
  rw [D.restrictionTermwise]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryIdIso_hom_app_Q_obj]
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.restriction a) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  exact h.symm

private theorem derived_gamma_eq {E : LocallyClosedExtensionData.{u}}
    (D : E.DerivedCoherence) {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    D.gamma a b = Functor.mapDerivedCategoryCompNatIso (E.gamma a b) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules T.scheme T.ring) (.up ℤ))
  intro K
  apply (cancel_mono ((E.extension (a.comp b)).mapDerivedCategoryFactors.hom.app K)).mp
  rw [D.gammaTermwise]
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q (E.gamma a b) K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app] at h
  erw [Category.id_comp] at h
  exact h.symm

private theorem derived_normalization
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (Eab : A ⥤ C)
    (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    [Ea.Additive] [Eb.Additive] [Eab.Additive] [La.Additive] [Lb.Additive] [Lab.Additive]
    [PreservesFiniteLimits Ea] [PreservesFiniteColimits Ea]
    [PreservesFiniteLimits Eb] [PreservesFiniteColimits Eb]
    [PreservesFiniteLimits Eab] [PreservesFiniteColimits Eab]
    [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
    [PreservesFiniteLimits Lab] [PreservesFiniteColimits Lab]
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (rab : Eab ⋙ Lab ≅ 𝟭 A)
    (g : Eb ⋙ Ea ≅ Eab) (c : Lab ≅ La ⋙ Lb)
    (h : ∀ N : A, Lab.map (g.hom.app N) ≫ rab.hom.app N =
      c.hom.app (Ea.obj (Eb.obj N)) ≫ Lb.map (ra.hom.app (Eb.obj N)) ≫ rb.hom.app N)
    (M : DerivedCategory A) :
    Lab.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso g).hom.app M) ≫
        (Functor.mapDerivedCategoryCompNatIso rab ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app M =
      (Functor.mapDerivedCategoryNatIso c ≪≫
        Functor.mapDerivedCategoryCompIso La Lb).hom.app
          (Ea.mapDerivedCategory.obj (Eb.mapDerivedCategory.obj M)) ≫
        Lb.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompNatIso ra ≪≫
          Functor.mapDerivedCategoryIdIso B).hom.app (Eb.mapDerivedCategory.obj M)) ≫
        (Functor.mapDerivedCategoryCompNatIso rb ≪≫
          Functor.mapDerivedCategoryIdIso A).hom.app M := by
  let z : Ea ⋙ Lab ≅ Lb :=
    Functor.isoWhiskerLeft (Ea) (c) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (ra) Lb ≪≫ Functor.leftUnitor Lb
  have hz (N : B) :
      z.hom.app N = (c).hom.app ((Ea).obj N) ≫
        Lb.map ((ra).hom.app N) := by
    simp [z]
  have h₁ := Functor.mapDerivedCategoryCompNatIso_cocycle
    (g) (rab) z (rb)
    (fun N ↦ by simpa only [hz, Category.assoc] using h N) M
  have h₂ := Functor.mapDerivedCategoryCompNatIso_cocycle
    (ra) (Functor.leftUnitor Lb) (c).symm z
    (fun N ↦ by simp [hz, ← Category.assoc])
    ((Eb.mapDerivedCategory).obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% h₁]
  have hL : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor Lb)).hom =
      𝟙 Lb.mapDerivedCategory := Functor.mapDerivedCategoryNatIso_refl
  have hu : (Functor.mapDerivedCategoryCompNatIso (Functor.leftUnitor Lb)).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryIdIso _).hom
        Lb.mapDerivedCategory := by
    simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, hL,
      Iso.symm_hom]
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 _) Lb).hom).mp
    erw [Category.comp_id, Iso.hom_inv_id]
    exact (Functor.mapDerivedCategoryCompIso_id_comp Lb).symm
  have hc : (Functor.mapDerivedCategoryCompNatIso (c).symm).hom =
      (Functor.mapDerivedCategoryNatIso (c) ≪≫
        Functor.mapDerivedCategoryCompIso La Lb).inv := by
    simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm]
  rw [hu, hc] at h₂
  have hz' := congrArg (fun f ↦
    (Functor.mapDerivedCategoryNatIso (c) ≪≫
      Functor.mapDerivedCategoryCompIso La Lb).hom.app
        ((Ea.mapDerivedCategory).obj ((Eb.mapDerivedCategory).obj M)) ≫ f) h₂
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hz'
  rw [← reassoc_of% hz']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]

private theorem derived_normalized {E : LocallyClosedExtensionData.{u}} (hE : E.Coherent)
    (D : E.DerivedCoherence) {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : DerivedCategory (proEtaleRingModules T.scheme T.ring)) :
    (a.comp b).pull.mapDerivedCategory.map ((D.gamma a b).hom.app M) ≫
        (D.restriction (a.comp b)).hom.app M =
      (Functor.mapDerivedCategoryNatIso (a.pullComp b) ≪≫
        Functor.mapDerivedCategoryCompIso a.pull b.pull).hom.app
          ((E.derived a).obj ((E.derived b).obj M)) ≫
        b.pull.mapDerivedCategory.map ((D.restriction a).hom.app ((E.derived b).obj M)) ≫
          (D.restriction b).hom.app M := by
  rw [derived_gamma_eq D, derived_restriction_eq D,
    derived_restriction_eq D, derived_restriction_eq D]
  exact derived_normalization (E.extension a) (E.extension b) (E.extension (a.comp b))
    a.pull b.pull (a.comp b).pull (E.restriction a) (E.restriction b)
    (E.restriction (a.comp b)) (E.gamma a b) (a.pullComp b) (hE.normalized a b) M

private theorem restriction_detects
    {E : LocallyClosedExtensionData.{u}} (D : E.DerivedCoherence)
    {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X)
    {A : DerivedCategory (proEtaleRingModules X.scheme X.ring)}
    {M N : DerivedCategory (proEtaleRingModules S.scheme S.ring)}
    (e : A ≅ (E.derived a).obj M) (f g : A ⟶ (E.derived a).obj N)
    (h : a.pull.mapDerivedCategory.map f = a.pull.mapDerivedCategory.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  apply (D.homBijection a M N).injective
  simp only [Functor.map_comp, h]

private theorem comparison_transport_eq
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {Ea : B ⥤ A} {Eb : C ⥤ B} {Eab : C ⥤ A}
    {Fa : E ⥤ D} {Fb : F ⥤ E} {Fab : F ⥤ D}
    {FX : A ⥤ D} {FS : B ⥤ E} {FT : C ⥤ F}
    (da : Ea ⋙ FX ≅ FS ⋙ Fa) (db : Eb ⋙ FS ≅ FT ⋙ Fb)
    (gr : Eb ⋙ Ea ≅ Eab) (gs : Fb ⋙ Fa ≅ Fab) :
    Functor.isoWhiskerRight gr.symm FX ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Eb da ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight db Fa ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FT gs =
      binaryComparisonTransport da db gr gs := by
  simp only [binaryComparisonTransport, binaryComparisonComposite, Iso.trans_assoc]

private theorem normalized_explicit_composite
    {Xr Sr Tr Xs Ss Ts : Type*}
    [Category Xr] [Category Sr] [Category Tr]
    [Category Xs] [Category Ss] [Category Ts]
    (Lar : Xr ⥤ Sr) (Lbr : Sr ⥤ Tr) (Labr : Xr ⥤ Tr)
    (Las : Xs ⥤ Ss) (Lbs : Ss ⥤ Ts) (Labs : Xs ⥤ Ts)
    (Ear : Sr ⥤ Xr) (Ebr : Tr ⥤ Sr) (Eabr : Tr ⥤ Xr)
    (Eas : Ss ⥤ Xs) (Ebs : Ts ⥤ Ss) (Eabs : Ts ⥤ Xs)
    (rar : Ear ⋙ Lar ≅ 𝟭 Sr) (rbr : Ebr ⋙ Lbr ≅ 𝟭 Tr)
    (rabr : Eabr ⋙ Labr ≅ 𝟭 Tr)
    (ras : Eas ⋙ Las ≅ 𝟭 Ss) (rbs : Ebs ⋙ Lbs ≅ 𝟭 Ts)
    (rabs : Eabs ⋙ Labs ≅ 𝟭 Ts)
    (cr : Labr ≅ Lar ⋙ Lbr) (cs : Labs ≅ Las ⋙ Lbs)
    (gr : Ebr ⋙ Ear ≅ Eabr) (gs : Ebs ⋙ Eas ≅ Eabs)
    (gr_compat : ∀ M : Tr,
      Labr.map (gr.hom.app M) ≫ rabr.hom.app M =
        cr.hom.app (Ear.obj (Ebr.obj M)) ≫
          Lbr.map (rar.hom.app (Ebr.obj M)) ≫ rbr.hom.app M)
    (gs_compat : ∀ M : Ts,
      Labs.map (gs.hom.app M) ≫ rabs.hom.app M =
        cs.hom.app (Eas.obj (Ebs.obj M)) ≫
          Lbs.map (ras.hom.app (Ebs.obj M)) ≫ rbs.hom.app M)
    (FX : Xr ⥤ Xs) (FS : Sr ⥤ Ss) (FT : Tr ⥤ Ts)
    (qa : FX ⋙ Las ≅ Lar ⋙ FS) (qb : FS ⋙ Lbs ≅ Lbr ⋙ FT)
    (qab : FX ⋙ Labs ≅ Labr ⋙ FT)
    (q_compat : immersionComparisonComposition Lar Lbr Labr Las Lbs Labs
      cr cs FX FS FT qa qb qab)
    (ha : Ear ⋙ FX ≅ FS ⋙ Eas) (hb : Ebr ⋙ FS ≅ FT ⋙ Ebs)
    (na : immersionComparisonNormalized Lar Las Ear Eas rar ras FX FS qa ha)
    (nb : immersionComparisonNormalized Lbr Lbs Ebr Ebs rbr rbs FS FT qb hb) :
    immersionComparisonNormalized Labr Labs Eabr Eabs rabr rabs FX FT qab
      (Functor.isoWhiskerRight gr.symm FX ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Ebr ha ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight hb Eas ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FT gs) := by
  unfold immersionComparisonNormalized
  rw [comparison_transport_eq]
  exact (normalizedComparison_binary_restriction
    Lar Lbr Labr Las Lbs Labs Ear Ebr Eabr Eas Ebs Eabs
    rar rbr rabr ras rbs rabs cr cs gr gs gr_compat gs_compat
    FX FS FT qa qb qab q_compat ha hb na nb).2

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem normalized_coefficient_composite
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (Xr Sr Tr Xs Ss Ts : LocallyClosedCoefficients.{u})
    (ar : LocallyClosedCoefficientImmersion Sr Xr)
    (br : LocallyClosedCoefficientImmersion Tr Sr)
    (abr : LocallyClosedCoefficientImmersion Tr Xr)
    (as_ : LocallyClosedCoefficientImmersion Ss Xs)
    (bs : LocallyClosedCoefficientImmersion Ts Ss)
    (abs : LocallyClosedCoefficientImmersion Ts Xs)
    (hr : abr = ar.comp br) (hs : abs = as_.comp bs) :
    let Lar := ar.pull.mapDerivedCategory
    let Lbr := br.pull.mapDerivedCategory
    let Labr := abr.pull.mapDerivedCategory
    let Las := as_.pull.mapDerivedCategory
    let Lbs := bs.pull.mapDerivedCategory
    let Labs := abs.pull.mapDerivedCategory
    let Ear := E.derived ar
    let Ebr := E.derived br
    let Eabr := E.derived abr
    let Eas := E.derived as_
    let Ebs := E.derived bs
    let Eabs := E.derived abs
    let rar : Ear ⋙ Lar ≅ 𝟭 _ := D.restriction ar
    let rbr : Ebr ⋙ Lbr ≅ 𝟭 _ := D.restriction br
    let rabr : Eabr ⋙ Labr ≅ 𝟭 _ := D.restriction abr
    let ras : Eas ⋙ Las ≅ 𝟭 _ := D.restriction as_
    let rbs : Ebs ⋙ Lbs ≅ 𝟭 _ := D.restriction bs
    let rabs : Eabs ⋙ Labs ≅ 𝟭 _ := D.restriction abs
    let cr : Labr ≅ Lar ⋙ Lbr := eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) hr) ≪≫
      Functor.mapDerivedCategoryNatIso (ar.pullComp br) ≪≫
        Functor.mapDerivedCategoryCompIso ar.pull br.pull
    let cs : Labs ≅ Las ⋙ Lbs := eqToIso (congrArg (fun k ↦ k.pull.mapDerivedCategory) hs) ≪≫
      Functor.mapDerivedCategoryNatIso (as_.pullComp bs) ≪≫
        Functor.mapDerivedCategoryCompIso as_.pull bs.pull
    let gr : Ebr ⋙ Ear ≅ Eabr := D.gamma ar br ≪≫ eqToIso (congrArg E.derived hr.symm)
    let gs : Ebs ⋙ Eas ≅ Eabs := D.gamma as_ bs ≪≫ eqToIso (congrArg E.derived hs.symm)
    ∀ (FX : DerivedCategory (proEtaleRingModules Xr.scheme Xr.ring) ⥤
        DerivedCategory (proEtaleRingModules Xs.scheme Xs.ring))
      (FS : DerivedCategory (proEtaleRingModules Sr.scheme Sr.ring) ⥤
        DerivedCategory (proEtaleRingModules Ss.scheme Ss.ring))
      (FT : DerivedCategory (proEtaleRingModules Tr.scheme Tr.ring) ⥤
        DerivedCategory (proEtaleRingModules Ts.scheme Ts.ring))
    (qa : FX ⋙ Las ≅ Lar ⋙ FS) (qb : FS ⋙ Lbs ≅ Lbr ⋙ FT)
    (qab : FX ⋙ Labs ≅ Labr ⋙ FT)
    (_q_compat : immersionComparisonComposition Lar Lbr Labr Las Lbs Labs
      cr cs FX FS FT qa qb qab)
    (ha : Ear ⋙ FX ≅ FS ⋙ Eas) (hb : Ebr ⋙ FS ≅ FT ⋙ Ebs)
    (_na : immersionComparisonNormalized Lar Las Ear Eas rar ras FX FS qa ha)
    (_nb : immersionComparisonNormalized Lbr Lbs Ebr Ebs rbr rbs FS FT qb hb),
    immersionComparisonNormalized Labr Labs Eabr Eabs rabr rabs FX FT qab
      (Functor.isoWhiskerRight gr.symm FX ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Ebr ha ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight hb Eas ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FT gs) := by
  cases hr
  cases hs
  dsimp only
  intro FX FS FT qa qb qab hq da db ha hb
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans] at *
  exact normalized_explicit_composite
    (Xr := DerivedCategory (proEtaleRingModules Xr.scheme Xr.ring))
    (Sr := DerivedCategory (proEtaleRingModules Sr.scheme Sr.ring))
    (Tr := DerivedCategory (proEtaleRingModules Tr.scheme Tr.ring))
    (Xs := DerivedCategory (proEtaleRingModules Xs.scheme Xs.ring))
    (Ss := DerivedCategory (proEtaleRingModules Ss.scheme Ss.ring))
    (Ts := DerivedCategory (proEtaleRingModules Ts.scheme Ts.ring))
    ar.pull.mapDerivedCategory br.pull.mapDerivedCategory (ar.comp br).pull.mapDerivedCategory
    as_.pull.mapDerivedCategory bs.pull.mapDerivedCategory (as_.comp bs).pull.mapDerivedCategory
    (E.derived ar) (E.derived br) (E.derived (ar.comp br))
    (E.derived as_) (E.derived bs) (E.derived (as_.comp bs))
    (D.restriction ar) (D.restriction br) (D.restriction (ar.comp br))
    (D.restriction as_) (D.restriction bs) (D.restriction (as_.comp bs))
    (Functor.mapDerivedCategoryNatIso (ar.pullComp br) ≪≫
      Functor.mapDerivedCategoryCompIso ar.pull br.pull)
    (Functor.mapDerivedCategoryNatIso (as_.pullComp bs) ≪≫
      Functor.mapDerivedCategoryCompIso as_.pull bs.pull)
    (D.gamma ar br) (D.gamma as_ bs)
    (derived_normalized hE D ar br) (derived_normalized hE D as_ bs)
    FX FS FT qa qb qab hq da db ha hb

namespace ImmersionComparisonRings.Functors

variable {I : Type v} {G : ImmersionComparisonRings.{u} I}
  {E : LocallyClosedExtensionData.{u}} {D : E.DerivedCoherence}
  {hG : G.Cartesian} (F : G.Functors E D hG)


private theorem normalized_unique {r s : I} {S X : ImmersionComparisonBase.{u}}
    {a : S.val ⟶ X.val} [IsImmersion a] (d e : F.Comparison r s a)
    (hd : F.Normalized d) (he : F.Normalized e) : d = e := by
  apply Iso.ext
  ext M
  apply restriction_detects D (G.arrow s a) (d.app M)
  apply (cancel_mono ((D.restriction (G.arrow s a)).hom.app
    ((F.functor r s S).obj M))).mp
  exact (hd M).trans (he M).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem normalized_composite (hE : E.Coherent)
    {r s : I} {S X T : ImmersionComparisonBase.{u}}
    {a : S.val ⟶ X.val} {b : T.val ⟶ S.val} [IsImmersion a] [IsImmersion b]
    (da : F.Comparison r s a) (db : F.Comparison r s b)
    (ha : F.Normalized da) (hb : F.Normalized db) :
    F.Normalized (F.composite da db) := by
  exact normalized_coefficient_composite E hE D
    (G.object r X) (G.object r S) (G.object r T)
    (G.object s X) (G.object s S) (G.object s T)
    (G.arrow r a) (G.arrow r b) (G.arrow r (b ≫ a))
    (G.arrow s a) (G.arrow s b) (G.arrow s (b ≫ a))
    (hG.composition r a b) (hG.composition s a b)
    (F.functor r s X) (F.functor r s S) (F.functor r s T)
    (F.q r s a) (F.q r s b) (F.q r s (b ≫ a))
    (F.property.2 r s a b) da db ha hb

end ImmersionComparisonRings.Functors

private theorem immersion_factorization {S X : ImmersionComparisonBase.{u}}
    (a : S.val ⟶ X.val) [ha : IsImmersion a] :
    ∃ (V : ImmersionComparisonBase.{u}) (c : S.val ⟶ V.val) (v : V.val ⟶ X.val),
      IsClosedImmersion c ∧ IsOpenImmersion v ∧ c ≫ v = a := by
  obtain ⟨V, c, v, hc, hv, h⟩ := IsImmersion.isImmersion_iff_exists.mp ha
  let := hv
  let := X.property.1
  let := X.property.2
  let : IsNoetherian X.val := ⟨⟩
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  let : NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟨V, inferInstance, inferInstance⟩, c, v, hc, hv, h⟩

/-- Restriction-normalized open and closed comparisons assemble independently of either
factorization order, respect immersion composition, and respect every compatible tower.

Source: blueprint main-20261015, det-prop-scalar-six-pullback.proof.md, (2)--(3);
Stacks Project, proetale.tex, Tags 09AA and 09BN.
(blueprint: lem-sfb-normalized-immersion-comparison-coherence).

Proof, following the node's five steps:
1. Derive normalization of the supplied derived extension compositor from its termwise
   characterization, the exact-functor cocycle, and the module extension normalization.
   The named generic normalization and composition predicates are exactly these equations.
2. The restriction Hom bijection detects equality between extension images. Conjugating
   the source by an existing comparison gives uniqueness of every normalized comparison.
3. Factor an immersion as closed then open. The binary-restriction theorem normalizes
   the composite of the two supplied comparisons. Uniqueness identifies it with every
   other factorization, including open then closed, and with supplied elementary maps.
4. The binary-restriction theorem also normalizes the composite for arbitrary immersions.
   Uniqueness identifies it with the assembled comparison. Precompose by F(gamma) to
   obtain the stated composition equation.
5. The tower-restriction theorem makes the two tower paths equal after restriction.
   Their source is isomorphic to an extension image using the two comparison isomorphisms;
   the restriction Hom bijection therefore makes the original paths equal. -/
theorem normalizedImmersionComparisonCoherence
    {I : Type v} (G : ImmersionComparisonRings.{u} I) (hG : G.Cartesian)
    (E : LocallyClosedExtensionData.{u}) (hE : E.Coherent) (D : E.DerivedCoherence)
    (F : G.Functors E D hG) (B : F.Elementary) :
    ∃ d : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a], F.Comparison r s a,
      F.Coherent B d := by
  classical
  have exists_normalized (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a] :
      ∃ d : F.Comparison r s a, F.Normalized d := by
    obtain ⟨V, c, v, hc, hv, h⟩ := immersion_factorization a
    let := hc
    let := hv
    subst a
    exact ⟨F.composite (B.openComparison r s v hv) (B.closedComparison r s c hc),
      F.normalized_composite hE _ _ (B.openNormalized r s v hv)
        (B.closedNormalized r s c hc)⟩
  let d : ∀ (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a], F.Comparison r s a :=
    fun r s _ _ a _ ↦ (exists_normalized r s a).choose
  have hd (r s : I) {S X : ImmersionComparisonBase.{u}}
      (a : S.val ⟶ X.val) [IsImmersion a] : F.Normalized (d r s a) :=
    (exists_normalized r s a).choose_spec
  refine ⟨d, ⟨hd, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r s S X a _ ha
    exact F.normalized_unique _ _ (hd r s a) (B.openNormalized r s a ha)
  · intro r s S X a _ ha
    exact F.normalized_unique _ _ (hd r s a) (B.closedNormalized r s a ha)
  · intro r s S V X c v _ _ hc hv
    exact F.normalized_unique _ _ (hd r s (c ≫ v))
      (F.normalized_composite hE _ _ (B.openNormalized r s v hv)
        (B.closedNormalized r s c hc))
  · intro r s S Z X j i _ _ hj hi
    exact F.normalized_unique _ _ (hd r s (j ≫ i))
      (F.normalized_composite hE _ _ (B.closedNormalized r s i hi)
        (B.openNormalized r s j hj))
  · intro r s S X T a b _ _ M
    have he := F.normalized_unique (d r s (b ≫ a))
      (F.composite (d r s a) (d r s b)) (hd r s (b ≫ a))
      (F.normalized_composite hE _ _ (hd r s a) (hd r s b))
    rw [he]
    simp only [ImmersionComparisonRings.Functors.composite, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Category.id_comp]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · intro r s t H S X a _ M
    have h := normalizedComparisonTower_restriction
      (G.pull r a) (G.pull s a) (G.pull t a)
      (G.extend E r a) (G.extend E s a) (G.extend E t a)
      (D.restriction (G.arrow r a)) (D.restriction (G.arrow s a))
      (D.restriction (G.arrow t a))
      (F.functor r s X) (F.functor s t X) (F.functor r t X)
      (F.functor r s S) (F.functor s t S) (F.functor r t S)
      (F.q r s a) (F.q s t a) (F.q r t a)
      (d r s a) (d s t a) (d r t a)
      (hd r s a) (hd s t a) (hd r t a) (H.iso X) (H.iso S) (H.compatible a)
    let e := (F.functor s t X).mapIso ((d r s a).app M) ≪≫
      (d s t a).app ((F.functor r s S).obj M)
    apply restriction_detects D (G.arrow t a) e
    simpa only [normalizedComparisonTowerLeftPath, normalizedComparisonTowerRightPath,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj, ImmersionComparisonRings.pull, ImmersionComparisonRings.extend] using
      congr_app h.2.2 M

end AlgebraicGeometry.Scheme
