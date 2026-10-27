/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.CoefficientHeartStratificationDefs
import Sheaf.Paper.ContinuousLocallyFreePullback
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.LisseFiniteCoefficientModel
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Sheaf.Paper.ContinuousAffineEtaleLattice
import all Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.Paper.ContinuousFiniteEtaleTraceLattice
import Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.Paper.ContinuousIntegralLocalizationCounit
import Sheaf.Paper.ContinuousIntegralUnderivedPushComparison
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.ContinuousLatticeSum
import Sheaf.Paper.LatticeSheafLocallyConstant

/-!
# Stratified integral lattices for lisse rational modules on qcqs schemes

Source: blueprint, six-functors basics, `sk-lem-stratified-lattice`, proof paragraphs
"Rank", "Sheaf of lattices", and "Pushing down by trace"; the qcqs refinement uses
Stacks Project, Tag 03S0, and finite-subextension lisse descent
(blueprint: lem-sfb-qcqs-lisse-stratified-integral-lattices).

The first conjunct takes the coefficient field itself as its model. The second
chooses one finite subfield model before stratifying. Every rationalization map is
induced by the specified integral inclusion. The last composite is the actual map
from the algebraic-closure scalar extension to the restriction of the original module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.pullIso CondensedRing.upperStarComp
  Mod.extendScalarsComp

attribute [local instance 2000] Limits.HasImages.has_image

private theorem lisse_iff_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsLisseCoefficientModule Λ M ↔ CondensedRing.LocallyFree (condensedRingObj Λ X) M := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i ↦ ?_⟩
    let φ := condensedPullbackHom Λ (U.f i)
    exact free_of_iso (free_comap (inv φ) (hU i))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm

private theorem compact_finite_affine_etale_cover
    (X : Scheme.{u}) [CompactSpace X]
    (Q : ∀ U : Scheme.{u}, (U ⟶ X) → Prop)
    (hlocal : ∀ x : X, ∃ (U : Scheme.{u}) (p : U ⟶ X),
      IsAffine U ∧ Etale p ∧ x ∈ Set.range p ∧ Q U p) :
    ∃ (I : Type u) (_ : Finite I) (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X),
      (∀ i, IsAffine (Y i)) ∧ (∀ i, Etale (p i)) ∧
      (∀ x : X, ∃ (i : I) (y : Y i), p i y = x) ∧ (∀ i, Q (Y i) (p i)) := by
  classical
  choose Y p hY hp hcover hQ using hlocal
  let (x : X) : Etale (p x) := hp x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ Set.range (p x))
    (fun x ↦ (p x).isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hcover x⟩)
  refine ⟨s, inferInstance, (fun i ↦ Y i.val), (fun i ↦ p i.val),
    (fun i ↦ hY i.val), (fun i ↦ hp i.val), ?_, (fun i ↦ hQ i.val)⟩
  intro x
  obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, y, hy⟩

private theorem compact_etale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), Etale p ∧ Surjective p ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) U),
        CondensedRing.LocallyFree (condensedRingObj (CondensedRing.integralCoeff ℓ E) U) M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (CondensedRing.integralScalarMap ℓ E) U)).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) := by
  classical
  let Q : ∀ U : Scheme.{u}, (U ⟶ X) → Prop := fun U p ↦
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) U),
      CondensedRing.LocallyFree (condensedRingObj (CondensedRing.integralCoeff ℓ E) U) M ∧
      Nonempty ((Mod.extendScalars
        (coefficientMap (CondensedRing.integralScalarMap ℓ E) U)).obj M ≅
          (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)
  obtain ⟨I, hI, Y, p, hY, hp, hcover, hQ⟩ :=
    compact_finite_affine_etale_cover X Q
      (CondensedRing.continuousLisse_affine_etale_lattice ℓ E X P hP)
  let : Finite I := hI
  let (i : I) : IsAffine (Y i) := hY i
  let (i : I) : Etale (p i) := hp i
  dsimp only [Q] at hQ
  choose M hM e using hQ
  exact CondensedRing.etale_lattice_of_finite_affine_lattices
    (CondensedRing.integralCoeff ℓ E) (Profinite.continuousMapRingObj E)
    (CondensedRing.integralScalarMap ℓ E) X P Y p hcover M hM e

private def HasLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
    IsLisseCoefficientModule A N ∧
    ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
      Mono ι ∧ IsIso (Mod.extendHom (coefficientMap a X) ι)

private theorem traceImage_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {U : Scheme.{u}} (p : U ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (CondensedRing.integralScalarMap l E) U)).obj M ≅
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (τ : (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P) [Epi τ]
    (hI : CondensedRing.LocallyFree (condensedRingObj (CondensedRing.integralCoeff l E) X)
      (Limits.image (CondensedRing.latticePushedEmbedding
        (CondensedRing.integralScalarMap l E) X P p M e ≫
          (Mod.comap (coefficientMap (CondensedRing.integralScalarMap l E) X)).map τ))) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff l E) X),
      CondensedRing.LocallyFree (condensedRingObj (CondensedRing.integralCoeff l E) X) N ∧
      ∃ ι : N ⟶ (Mod.comap (coefficientMap (CondensedRing.integralScalarMap l E) X)).obj P,
        Mono ι ∧ IsIso (Mod.extendHom
          (coefficientMap (CondensedRing.integralScalarMap l E) X) ι) := by
  let a := coefficientMap (CondensedRing.integralScalarMap l E) X
  let F := Mod.extendScalars a
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) a
  let adj := Mod.extendRestrictAdjunction a
  let b := CondensedRing.latticePushedEmbedding
    (CondensedRing.integralScalarMap l E) X P p M e
  let g := b ≫ G.map τ
  have := CondensedRing.integralScalarCounit_isIso l E X P
  have := CondensedRing.integralScalarCounit_isIso l E X
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P))
  have := CondensedRing.integralScalarUnderivedPushHom_isIso l E p M
  have := CondensedRing.latticePushedEmbedding_map_isIso
    (CondensedRing.integralScalarMap l E) X P p M e
  have hfac : F.map g ≫ adj.counit.app P = F.map b ≫ adj.counit.app _ ≫ τ := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun z ↦ F.map b ≫ z) (adj.counit.naturality τ)
  have : Epi (F.map g ≫ adj.counit.app P) := by
    rw [hfac]
    infer_instance
  have : Epi (F.map g) :=
    (epi_comp_iff_of_isIso (F.map g) (adj.counit.app P)).mp inferInstance
  have : Epi (F.map (Limits.factorThruImage g) ≫ F.map (Limits.image.ι g)) := by
    rw [← F.map_comp, Limits.image.fac]
    infer_instance
  have : Epi (F.map (Limits.image.ι g)) :=
    epi_of_epi (F.map (Limits.factorThruImage g)) (F.map (Limits.image.ι g))
  have : IsIso (F.map (Limits.image.ι g)) := isIso_of_mono_of_epi _
  have hι : IsIso ((adj.homEquiv (Limits.image g) P).symm (Limits.image.ι g)) := by
    change IsIso (F.map (Limits.image.ι g) ≫ adj.counit.app P)
    infer_instance
  refine ⟨Limits.image g, hI, Limits.image.ι g, inferInstance, ?_⟩
  dsimp only [adj] at hι
  rw [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at hι
  exact hι

private theorem finiteEtale_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff l E) U))
    (hM : CondensedRing.LocallyFree
      (condensedRingObj (CondensedRing.integralCoeff l E) U) M)
    (e : (Mod.extendScalars (coefficientMap (CondensedRing.integralScalarMap l E) U)).obj M ≅
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    HasLattice (CondensedRing.integralCoeff l E) (Profinite.continuousMapRingObj E)
      (CondensedRing.integralScalarMap l E) X P := by
  obtain ⟨τ, hτ, hI⟩ := CondensedRing.continuousFiniteEtaleTrace_lattice
    l E X P hP p M hM e
  have := hτ
  obtain ⟨B, hB, ι, hι, he⟩ := traceImage_lattice l E X P p M e τ hI
  exact ⟨B, (lisse_iff_locallyFree _ B).mpr hB, ι, hι, he⟩

private noncomputable def latticePullbackIso
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] {X U V : Scheme.{u}} (p : U ⟶ X) (j : V ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅
      (CondensedRing.upperStar B p).obj P) :
    (Mod.extendScalars (coefficientMap a (Limits.pullback p j))).obj
        ((CondensedRing.upperStar A (Limits.pullback.fst p j)).obj M) ≅
      (CondensedRing.upperStar B (Limits.pullback.snd p j)).obj
        ((CondensedRing.upperStar B j).obj P) :=
  (CondensedRing.pullIso a (Limits.pullback.fst p j)).app M ≪≫
  (CondensedRing.upperStar B (Limits.pullback.fst p j)).mapIso e ≪≫
  (CondensedRing.upperStarComp B (Limits.pullback.fst p j) p).symm.app P ≪≫
  eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar B f).obj P)
    (Limits.pullback.condition)) ≪≫
  (CondensedRing.upperStarComp B (Limits.pullback.snd p j) j).app P

attribute [local irreducible] latticePullbackIso

private theorem latticeOnPullback
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    {X U V : Scheme.{u}} (p : U ⟶ X) (j : V ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hM : CondensedRing.LocallyFree (condensedRingObj A U) M)
    (hP : CondensedRing.LocallyFree (condensedRingObj B X) P)
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅
      (CondensedRing.upperStar B p).obj P)
    (hd : ∀ (Y : Scheme.{u})
      (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)),
      CondensedRing.LocallyFree (condensedRingObj B Y) Q →
      ∀ {W : Scheme.{u}} (q : W ⟶ Y) [IsFinite q] [Etale q] [Surjective q]
        (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj A W)),
        CondensedRing.LocallyFree (condensedRingObj A W) N →
        ((Mod.extendScalars (coefficientMap a W)).obj N ≅
          (CondensedRing.upperStar B q).obj Q) → HasLattice A B a Y Q)
    [Surjective p] [IsFinite (Limits.pullback.snd p j)] [Etale (Limits.pullback.snd p j)] :
    HasLattice A B a V ((CondensedRing.upperStar B j).obj P) := by
  exact hd V _ (CondensedRing.locallyFree_upperStar B j hP)
    (Limits.pullback.snd p j) _
    (CondensedRing.locallyFree_upperStar A (Limits.pullback.fst p j) hM)
    (latticePullbackIso A B a p j M P e)

private theorem stratified_property
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (p : U ⟶ X) [Etale p]
    (Q : ∀ V : Scheme.{u}, (V ⟶ X) → Prop)
    (hQ : ∀ (V : Scheme.{u}) (j : V ⟶ X),
      IsFinite (Limits.pullback.snd p j) → Etale (Limits.pullback.snd p j) → Q V j) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, Q (S.domain i) (S.immersion i) := by
  obtain ⟨S, hS, hf⟩ := Scheme.exists_etale_stratified_finite p
  let R : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨R, hS, fun i ↦ hQ (S.domain i) (S.immersion i) (hf i).1 (hf i).2⟩

private theorem stratifiedLattices_of_cover
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (p : U ⟶ X) [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hM : CondensedRing.LocallyFree (condensedRingObj A U) M)
    (hP : CondensedRing.LocallyFree (condensedRingObj B X) P)
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅
      (CondensedRing.upperStar B p).obj P)
    (hd : ∀ (Y : Scheme.{u})
      (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)),
      CondensedRing.LocallyFree (condensedRingObj B Y) Q →
      ∀ {W : Scheme.{u}} (q : W ⟶ Y) [IsFinite q] [Etale q] [Surjective q]
        (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj A W)),
        CondensedRing.LocallyFree (condensedRingObj A W) N →
        ((Mod.extendScalars (coefficientMap a W)).obj N ≅
          (CondensedRing.upperStar B q).obj Q) → HasLattice A B a Y Q) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, HasLattice A B a (S.domain i)
        ((CondensedRing.upperStar B (S.immersion i)).obj P) := by
  apply stratified_property p
    (fun V j ↦ HasLattice A B a V ((CondensedRing.upperStar B j).obj P))
  intro V j hfinite hetale
  have := hfinite
  have := hetale
  exact latticeOnPullback A B a p j M P hM hP e hd

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normedField_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) P) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, HasLattice (CondensedRing.integralCoeff ℓ E)
        (Profinite.continuousMapRingObj E) (CondensedRing.integralScalarMap ℓ E)
        (S.domain i) ((CondensedRing.upperStar
          (Profinite.continuousMapRingObj E) (S.immersion i)).obj P) := by
  have hfree := (lisse_iff_locallyFree _ P).mp hP
  obtain ⟨U, p, hp, hs, hc, hq, M, hM, ⟨e⟩⟩ := compact_etale_lattice ℓ E X P hfree
  have := hp
  have := hs
  have := hc
  have := hq
  exact stratifiedLattices_of_cover (CondensedRing.integralCoeff ℓ E)
    (Profinite.continuousMapRingObj E) (CondensedRing.integralScalarMap ℓ E)
    p M P hM hfree e (finiteEtale_lattice ℓ E)

private structure LatticeCoefficientDiagram where
  integral : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  rational : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  map : integral ⟶ rational

private def latticeCoefficientDiagram
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] : LatticeCoefficientDiagram.{u} :=
  ⟨CommMon.mk A, CommMon.mk B, CommMon.homMk (Mon.ofHom a)⟩

private def StratifiedLattices
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
    IsLisseCoefficientModule B P →
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, HasLattice A B a (S.domain i)
        ((CondensedRing.upperStar B (S.immersion i)).obj P)

private def DiagramStratifiedLattices (D : LatticeCoefficientDiagram.{u})
    (X : Scheme.{u}) : Prop :=
  StratifiedLattices D.integral.X D.rational.X D.map.hom.hom X

private theorem diagramStratified_pack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u}) (h : StratifiedLattices A B a X) :
    DiagramStratifiedLattices (latticeCoefficientDiagram A B a) X := h

private theorem diagramStratified_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : DiagramStratifiedLattices (latticeCoefficientDiagram A B a) X) :
    StratifiedLattices A B a X := h

private def continuousLatticeDiagram (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] : LatticeCoefficientDiagram.{u} :=
  latticeCoefficientDiagram (CondensedRing.integralCoeff ℓ E)
    (Profinite.continuousMapRingObj E) (CondensedRing.integralScalarMap ℓ E)

private def finiteLatticeDiagram (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : LatticeCoefficientDiagram.{u} :=
  latticeCoefficientDiagram (Profinite.padicIntegersRingObj ℓ E.1)
    (Profinite.continuousMapRingObj E.1) (padicIntegersRingObjToContinuousMapRingObj ℓ E)

private theorem latticeDiagram_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    continuousLatticeDiagram.{u} ℓ E.1 = finiteLatticeDiagram ℓ E := by
  rfl

private theorem continuousDiagram_stratified (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    DiagramStratifiedLattices (continuousLatticeDiagram ℓ E) X := by
  exact diagramStratified_pack (CondensedRing.integralCoeff ℓ E)
    (Profinite.continuousMapRingObj E) (CondensedRing.integralScalarMap ℓ E) X
    (normedField_lattices ℓ E X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteCoefficients_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    (hP : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) P) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
      ∀ s : Fin S.n,
        ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain s)),
          IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) B ∧
          ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ E)).obj
              ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
                (S.immersion s)).obj P),
            Mono ι ∧ IsIso (Mod.extendHom
              (padicIntegersToPadicSubfield (S.domain s) ℓ E) ι) := by
  have h : DiagramStratifiedLattices (finiteLatticeDiagram ℓ E) X :=
    Eq.mp (congrArg (fun D ↦ DiagramStratifiedLattices D X) (latticeDiagram_eq ℓ E))
      (continuousDiagram_stratified ℓ E.1 X)
  exact diagramStratified_unpack (Profinite.padicIntegersRingObj ℓ E.1)
    (Profinite.continuousMapRingObj E.1) (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    X h P hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Lisse rational modules on a qcqs scheme have embedded lisse integral lattices on
finitely many constructible locally closed strata, for both allowed coefficient rings.
For finite coefficients the model is M itself, so the first scalar comparison is the
canonical identity comparison `Mod.extendScalarsId`. For algebraic-closure coefficients
one first chooses a finite subfield F and a lisse F-model L with comparison e.

Source: blueprint `sk-lem-stratified-lattice`, rank, lattice-scheme and trace paragraphs;
Stacks Project, Tag 03S0; `sk-lem-coefficient-finite-descent-lisse`, assertion (1)
(blueprint: lem-sfb-qcqs-lisse-stratified-integral-lattices).

Proof plan:
1. Apply lem-sfb-lisse-finite-coefficient-model in the algebraic-closure case. In the
finite case set F = E, L = M, and use the identity scalar-extension comparison.
2. By det-lem-stratified-lattice-rank divide the qcqs base into finitely many clopen
constant-rank pieces. Each remains qcqs; ranks zero and varying ranks are allowed.
3. On each piece use det-lem-stratified-lattice-scheme to obtain a separated surjective
etale lattice scheme and its universal embedded lattice. Apply the finite affine sieve
refinement and proetale qcqs finite-family geometry lemmas to obtain a qcqs etale
surjective cover carrying an embedded lattice. Locally free pullback and Cartesian
coefficients preserve the inclusion and its rationalization.
4. Stacks 03S0 (lem-weil-pbc-etale-stratified-finite) gives finitely many constructible
locally closed strata on which that cover is finite etale. The base-changed cover is
surjective: the tensor product of the two residue fields over the image residue field
is nonzero and has a prime. Pull the lattice to each base change; internal extension
commutes with inverse image, preserving its rationalization.
5. Use lem-sfb-embedded-lattice-coefficient-comparison to pass to continuous-function
coefficients. The finite-etale-trace-image lemma forms the image of the pushed lattice
under trace. Finite etale local splitting identifies this image with the sheet sum;
the sheet set is nonempty on a nonempty neighbourhood, by surjectivity.
6. Trivialize the rational module proetale locally. The locally constant lattice-class
sheaf makes the finitely many sheet lattices simultaneously constant after refinement.
The continuous-lattice-sum lemma makes their sum finite free with invertible actual
rationalization. Transport this embedded lattice back to internal modules. No degree
is divided out and no Noetherianity is used.
7. Unite the finite partitions of the clopen rank pieces. Pull back e using Cartesian
coefficients and inverse-image/scalar-extension compatibility. Compose with scalar
extension of the lattice rationalization and tensor transitivity, whose pure-tensor
map is lambda tensor (f tensor b) to lambda*f tensor b, with inverse inserting 1.
This gives exactly the final displayed composite. For an empty base use the empty
partition; on rank-zero pieces use zero lattices. No dimension, characteristic or
invertibility-of-ell hypothesis enters any step. -/
theorem qcqs_lisse_stratified_integral_lattices
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) T),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M →
      ∃ S : Scheme.FiniteLocallyClosedStratification T,
        (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
        ∀ s : Fin S.n,
          ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
              (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (S.domain s)),
            IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) B ∧
            ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ E)).obj
                ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
                  (S.immersion s)).obj M),
              Mono ι ∧ IsIso (Mod.extendHom
                (padicIntegersToPadicSubfield (S.domain s) ℓ E) ι)) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M →
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
        (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj F.1) T)),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj F.1) L ∧
        ∃ e : (Mod.extendScalars
            (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T)).obj L ≅ M,
          ∃ S : Scheme.FiniteLocallyClosedStratification T,
            (∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)) ∧
            ∀ s : Fin S.n,
              ∃ B : Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
                  (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) (S.domain s)),
                IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F.1) B ∧
                ∃ ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield (S.domain s) ℓ F)).obj
                    ((CondensedRing.upperStar (Profinite.continuousMapRingObj F.1)
                      (S.immersion s)).obj L),
                  Mono ι ∧
                  IsIso (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ∧
                  IsIso
                    ((Mod.extendScalarsComp (padicIntegersToPadicSubfield (S.domain s) ℓ F)
                      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.domain s))).hom.app B ≫
                      (Mod.extendScalars (coefficientMap
                        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) (S.domain s))).map
                          (Mod.extendHom (padicIntegersToPadicSubfield (S.domain s) ℓ F) ι) ≫
                      (CondensedRing.pullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F)
                        (S.immersion s)).hom.app L ≫
                      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                        (S.immersion s)).map e.hom)) := by
  constructor
  · exact finiteCoefficients_lattices ℓ E T
  · intro M hM
    obtain ⟨F, L, hL, ⟨e⟩⟩ := exists_lisse_finiteCoefficient_model T ℓ M hM
    obtain ⟨S, hS, hB⟩ := finiteCoefficients_lattices ℓ F T L hL
    refine ⟨F, L, hL, e, S, hS, fun s ↦ ?_⟩
    have hx := hB s
    obtain ⟨B, hBs, ι, hι, he⟩ := hx
    have := he
    refine ⟨B, hBs, ι, hι, he, ?_⟩
    refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_))
    · exact NatIso.hom_app_isIso _ _
    · exact Functor.map_isIso _ _
    · exact NatIso.hom_app_isIso _ _
    · exact Functor.map_isIso _ _

end AlgebraicGeometry.ProEtale
