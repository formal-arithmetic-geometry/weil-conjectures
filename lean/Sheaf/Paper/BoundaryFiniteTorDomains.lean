/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DualityPairing
public import Sheaf.Paper.BoundaryDualizingComposition
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.EtaleGeometricBiduality
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat

/-! # Finite-stage domains for closed boundary duality

Source: current Weil blueprint, cor-weil-boundary-duality-discharge, first proof paragraph
(blueprint: lem-weil-boundary-finite-tor-domains).

The predicates below package the clauses of this node, using the ordinary constant-module
categories, the recorded finite-Tor predicate, the actual ambient exceptional adjoint,
and the canonical evaluation transpose. The two dualizing identifications and their
comparison-origin transport are the existing constructions recorded by
`def-weil-boundary-composition-mate`, in BoundaryDualizingComposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry

namespace WeilConjectures

/-- The closed-pair clauses: ordinary and exceptional restriction preserve Dᵇ_ctf,
and a natural costalk isomorphism composes with Gδ to an isomorphism on that category.
The composition compatibility refers to the specified etale and pro-etale dualizing
identifications `Etale.boundaryDualizingEtaleIso` and `Etale.boundaryDualizingProIso`,
including their pasted-counit equation and bounded-below origin transport.
These constructions are recorded by def-weil-boundary-composition-mate.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-finite-tor-domains). -/
def BoundaryClosedFiniteTorDomains
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] {T Z : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  letI : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated aT
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let DT := Etale.verdierDual (ModuleCat.{u + 1} A) aT
  let DZ := Etale.verdierDual (ModuleCat.{u + 1} A) (i ≫ aT)
  let G := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) i
  let s := (Etale.upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory
  (∀ L : Etale.DerivedCategoryModule A T,
    finiteTorConstructibleEtale l E n hn T L →
      finiteTorConstructibleEtale l E n hn Z (s.obj L) ∧
      finiteTorConstructibleEtale l E n hn Z (G.obj L)) ∧
    (∃ α : DT ⋙ G ≅ s.op ⋙ DZ,
      ∀ L : Etale.DerivedCategoryModule A T,
        finiteTorConstructibleEtale l E n hn T L →
          finiteTorConstructibleEtale l E n hn Z (s.obj (DT.obj (op L))) ∧
          IsIso (G.map
            ((Etale.verdierDualDoubleDual (ModuleCat.{u + 1} A) aT).app L) ≫
              α.hom.app (op (DT.obj (op L))))) ∧
    Nonempty (G.obj (Etale.dualizingComplex (ModuleCat.{u + 1} A) aT) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} A) (i ≫ aT)) ∧
    Nonempty ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) i).obj
        ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) aT).obj (𝟙_ _)) ≅
      (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) (i ≫ aT)).obj (𝟙_ _)) ∧
    Etale.BoundaryCompositionCompatibility A i aT

/-- The clauses for one locally closed piece: geometric finiteness, existence of the
ambient compact-support adjunction, preservation of D+, duality and its canonical
biduality on Dᵇ_ctf, and all closed pairs with this target. The dualizing complex is
literally a-times of the constant coefficient complex, as in Etale.dualizingComplex.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-finite-tor-domains). -/
def BoundaryPieceFiniteTorDomains
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] {W : Scheme.{u}}
    (aW : W ⟶ Spec (.of k)) [IsSeparated aW] [LocallyOfFiniteType aW] [QuasiCompact aW] :
    Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  IsNoetherian W ∧
    Nonempty (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) aW ⊣
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) aW) ∧
    (∀ K : Etale.DerivedCategoryModule A (Spec (.of k)),
      DerivedCategory.TStructure.t.plus K → DerivedCategory.TStructure.t.plus
        ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) aW).obj K)) ∧
    (∀ K : Etale.DerivedCategoryModule A W,
      finiteTorConstructibleEtale l E n hn W K →
        finiteTorConstructibleEtale l E n hn W
          ((Etale.verdierDual (ModuleCat.{u + 1} A) aW).obj (op K)) ∧
        IsIso ((Etale.verdierDualDoubleDual (ModuleCat.{u + 1} A) aW).app K)) ∧
    ∀ (Z : Scheme.{u}) (i : Z ⟶ W) [IsClosedImmersion i],
      BoundaryClosedFiniteTorDomains l E n hn aW i

/-- Every immersion into Y is a separated finite-type Noetherian piece. The existential
witnesses are proofs of those geometric conclusions, used only to type the subsequent
canonical functors; they are conclusions, never additional geometric assumptions.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-finite-tor-domains). -/
def BoundaryFiniteTorDomains
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of D.k)) : Prop :=
  ∀ (W : Scheme.{u}) (w : W ⟶ Y) [IsImmersion w],
    ∃ (hs : IsSeparated (w ≫ aY)) (ht : LocallyOfFiniteType (w ≫ aY))
      (hq : QuasiCompact (w ≫ aY)),
      @BoundaryPieceFiniteTorDomains l _ E _ _ _ n hn D.k _ W (w ≫ aY) hs ht hq

private lemma boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦ ?_⟩
    · exact (DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
    · exact (DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private lemma finiteTorConstructibleEtale_iff_source
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X) :
    finiteTorConstructibleEtale l E n hn X K ↔
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X K := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  constructor
  · rintro ⟨hc, a, b, hab, ht⟩
    exact ⟨(boundedConstructible_iff_source _ X K).1 hc, a, b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    exact ⟨(boundedConstructible_iff_source _ X K).2 hc, min a b, b, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (ht.mono (min_le_left _ _) le_rfl)⟩

private lemma finiteTorConstructibleEtale_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    {K L : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X}
    (e : K ≅ L) (hK : finiteTorConstructibleEtale l E n hn X K) :
    finiteTorConstructibleEtale l E n hn X L := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  have h := (finiteTorConstructibleEtale_iff_source l E n hn X K).1 hK
  exact (finiteTorConstructibleEtale_iff_source l E n hn X L).2
    ⟨(Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X).prop_of_iso e h.1,
      (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X).prop_of_iso e h.2⟩

attribute [local instance] Etale.derivedBraidedCategory

private theorem boundary_costalk_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] {T Z : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i] :
    Nonempty (Etale.verdierDual (ModuleCat.{u + 1} A) aT ⋙
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) i ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.op ⋙
        Etale.verdierDual (ModuleCat.{u + 1} A) (i ≫ aT)) := by
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  let : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated aT
  let adjT : (Etale.verdierDual (ModuleCat.{u + 1} A) aT).rightOp ⊣
      Etale.verdierDual (ModuleCat.{u + 1} A) aT :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let adjZ : (Etale.verdierDual (ModuleCat.{u + 1} A) (i ≫ aT)).rightOp ⊣
      Etale.verdierDual (ModuleCat.{u + 1} A) (i ≫ aT) :=
    MonoidalClosed.ihomFlipSelfAdjunction _
  let e := Etale.verdierDualLowerShriekIso (ModuleCat.{u + 1} A) aT i
    (Etale.derivedHomRightDerivedLowerShriekIsoOfFinite A i)
    (Etale.boundaryDualizingEtaleIso A i aT) (Iso.refl _)
  exact ⟨conjugateIsoEquiv
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) i).comp adjT)
    (adjZ.comp (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).op)
    e.symm⟩

/-- Finite-stage domains for closed boundary duality, with exactly the global datum,
prime-to-characteristic coefficients, and separated finite-type ambient scheme.
No evaluation normalization is imposed on the natural costalk isomorphism.
Source: current Weil blueprint, boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-finite-tor-domains).

Proof plan:
1. The field is Noetherian. Finite type makes Y Noetherian. Factor an immersion
   through a closed immersion and an open immersion. Opens of Noetherian schemes
   are Noetherian and quasi-compact, hence their inclusions are finite type. Closed
   immersions are proper, hence finite type. Composition proves finite type of W.
   Uses lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-qc-open-immersion-finite-type, lem-weil-pbc-closed-immersion-proper,
   and lem-sfb-finite-type-composition-base-change.
2. Immersions are separated; composition with aY is separated. Apply
   lem-weil-boundary-etale-adjunction-restriction to each structure map and each
   closed i. For a closed immersion proper compact support is ordinary direct image.
   Uses lem-weil-pbc-separated-cancellation and lem-weil-pbc-proper-fp-permanence.
3. Apply thm-weil-etale-geometric-biduality to each piece: duality preserves Dᵇ_ctf
   and its specified evaluation double-dual map is invertible.
4. Exact constant-module pullback commutes with cohomology. Pull back finite
   constructible strata and their etale trivializing covers; constant finite modules
   remain constant. A bounded flat K-flat model pulls back to such a model in the
   same Tor interval. Uses prop-weil-pbc-inverse-image-modules-exact,
   lem-pur-scheme-constructible-preimage, lem-sf-etale-tor-flat-pullback-model.
5. Apply lem-weil-boundary-dualizing-composition to i and aT at A. Its mate gives
   the etale dualizing identification with pasted counits. Comparison-unit transport
   gives the specified pro-etale identification on bounded-below etale-origin objects.
6. Apply lem-weil-closed-costalk-duality in the ambient etale category and postcompose
   with the dualizing identification. This gives natural α_H for every H. At H=DT L,
   compose α with Gδ_L; both factors are invertible.
7. P=s DT L and DZ P are bounded finite-Tor constructible by steps 3 and 4. The
   isomorphism GL to DZ P transfers bounded constructibility and one Tor interval
   to GL, since cohomology and derived tensor preserve isomorphisms.
-/
theorem boundary_finite_tor_domains
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    BoundaryFiniteTorDomains D l E n hn aY := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  intro W w hw
  have : TopologicalSpace.NoetherianSpace W := w.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact w := inferInstance
  have : IsSeparated (w ≫ aY) := inferInstance
  have : LocallyOfFiniteType (w ≫ aY) := inferInstance
  have : QuasiCompact (w ≫ aY) := inferInstance
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ aY)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ aY)
  have : IsNoetherian W := ⟨⟩
  refine ⟨inferInstance, ⟨Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (w ≫ aY)⟩, ?_, ?_, ?_⟩
  · exact Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} A) (w ≫ aY)
  · intro K hK
    have h := (finite_stage_etale_geometric_biduality D l _hl E n hn W (w ≫ aY)).2
    exact ⟨h.2.1 K hK, h.1 K hK⟩
  · intro Z i hi
    let aW := w ≫ aY
    let DT := Etale.verdierDual (ModuleCat.{u + 1} A) aW
    let DZ := Etale.verdierDual (ModuleCat.{u + 1} A) (i ≫ aW)
    let G := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) i
    let s := (Etale.upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory
    have pull (K : Etale.DerivedCategoryModule A W)
        (hK : finiteTorConstructibleEtale l E n hn W K) :
        finiteTorConstructibleEtale l E n hn Z (s.obj K) := by
      apply (finiteTorConstructibleEtale_iff_source l E n hn Z _).2
      exact Etale.constructibleFiniteTor_mapDerivedCategory_upperStar A i
        ((finiteTorConstructibleEtale_iff_source l E n hn W _).1 hK)
    have dualW := (finite_stage_etale_geometric_biduality D l _hl E n hn W aW).2
    have dualZ := (finite_stage_etale_geometric_biduality D l _hl E n hn Z (i ≫ aW)).2
    obtain ⟨α⟩ := boundary_costalk_iso A aW i
    have compIso (L : Etale.DerivedCategoryModule A W)
        (hL : finiteTorConstructibleEtale l E n hn W L) :
        IsIso (G.map ((Etale.verdierDualDoubleDual (ModuleCat.{u + 1} A) aW).app L) ≫
          α.hom.app (op (DT.obj (op L)))) := by
      have := dualW.1 L hL
      infer_instance
    refine ⟨?_, ⟨α, ?_⟩, ⟨Etale.boundaryDualizingEtaleIso A i aW⟩,
      ⟨Etale.boundaryDualizingProIso A i aW⟩, ?_⟩
    · intro L hL
      refine ⟨pull L hL, ?_⟩
      have := compIso L hL
      let e : G.obj L ≅ DZ.obj (op (s.obj (DT.obj (op L)))) :=
        asIso (G.map ((Etale.verdierDualDoubleDual (ModuleCat.{u + 1} A) aW).app L) ≫
          α.hom.app (op (DT.obj (op L))))
      exact finiteTorConstructibleEtale_of_iso l E n hn Z e.symm
        (dualZ.2.1 _ (pull _ (dualW.2.1 L hL)))
    · intro L hL
      exact ⟨pull _ (dualW.2.1 L hL), compIso L hL⟩
    · exact Etale.boundary_dualizing_composition D l _hl E n hn
        Z W (Spec (.of D.k)) (i ≫ aW) aW (𝟙 _) i aW rfl (Category.comp_id _)

end WeilConjectures
