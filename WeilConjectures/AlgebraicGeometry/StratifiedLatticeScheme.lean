/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProetaleConstantSplitDescent
import WeilConjectures.AlgebraicGeometry.IndQuasiAffineEffectiveDescent
import WeilConjectures.AlgebraicGeometry.ProetaleAffineConstantCover
import WeilConjectures.AlgebraicGeometry.ProetaleEffectiveSheafDescent
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The separated etale scheme of integral lattices

Source: latest Weil blueprint, sec-six-functors-basics/sk-lem-lattice-atlas/
sk-lem-stratified-lattice-scheme.md, assertions (1)--(4)
(blueprint: det-lem-stratified-lattice-scheme).

We use the existing presentation by lattice pairs modulo intertwining integral
isomorphisms. Its restriction law records equality of the embedded submodules.
Slice restriction along an etale object is the inverse image on the small pro-etale site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem proetale_singleton_covers {X V : Scheme.{u}}
    (p : V ⟶ X) [WeaklyEtale p] [QuasiCompact p] [Surjective p] :
    (Scheme.ProEt.topology X).CoversTop (fun _ : PUnit.{u + 2} ↦ Scheme.ProEt.mk p) := by
  intro U
  let W := Scheme.ProEt.mk (pullback.snd p U.hom ≫ U.hom)
  let a : W ⟶ U := MorphismProperty.Over.homMk (pullback.snd p U.hom) rfl
  let b : W ⟶ Scheme.ProEt.mk p := MorphismProperty.Over.homMk (pullback.fst p U.hom)
    (pullback.condition (f := p) (g := U.hom))
  apply (Scheme.ProEt.topology X).superset_covering
    (S := Sieve.generate (Presieve.singleton a))
  · rintro A f ⟨_, g, _, ⟨⟩, rfl⟩
    exact ⟨PUnit.unit, ⟨g ≫ b⟩⟩
  · apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton (pullback.snd p U.hom) ∈ _
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance

private theorem etale_singleton_covers (X : Scheme.{u}) (Z : X.Etale)
    [Surjective Z.hom] :
    X.smallEtaleTopology.CoversTop (fun _ : PUnit.{u + 2} ↦ Z) := by
  intro U
  let W : X.Etale := Scheme.Etale.mk (pullback.fst U.hom Z.hom ≫ U.hom)
  let a : W ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom Z.hom) rfl
  let b : W ⟶ Z := MorphismProperty.Over.homMk (pullback.snd U.hom Z.hom)
    (pullback.condition (f := U.hom) (g := Z.hom)).symm
  apply X.smallEtaleTopology.superset_covering
    (S := Sieve.ofArrows (fun _ : PUnit.{1} ↦ W) (fun _ ↦ a))
  · rintro V f ⟨_, g, _, ⟨i⟩, rfl⟩
    exact ⟨PUnit.unit, ⟨g ≫ b⟩⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := (inferInstance : Surjective (pullback.fst U.hom Z.hom)).surj x
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, y, hy⟩

private theorem lattice_identity_representative (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt,
      IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U))
    (hc : IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c)
    (Z : X.Etale)
    (e : F.obj ≅ (Scheme.ProEt.forget X).op ⋙
      yoneda.obj ((Scheme.Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2}) :
    ∃ P : IntegralLatticePair (integralLatticeCoefficientMap X l E) L
        ((Scheme.toProEt X).obj Z),
      e.hom.app (op ((Scheme.toProEt X).obj Z))
        (c ((Scheme.toProEt X).obj Z) P) =
          ULift.up (𝟙 ((Scheme.Etale.forget X).obj Z)) := by
  let U := (Scheme.toProEt X).obj Z
  let z : F.obj.obj (op U) :=
    e.inv.app (op U) (ULift.up (𝟙 ((Scheme.Etale.forget X).obj Z)))
  obtain ⟨P, hP⟩ := hc.1 U z
  refine ⟨P, ?_⟩
  rw [hP]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (op U)) _

/-- The lattice sheaf of a lisse rank `r` rational coefficient module is constant in
any frame, is represented by a separated surjective etale scheme, has a universal
lattice, and has lattice sections on an etale covering.

`IsLatticeClassPresentation` identifies sections with embedded integral lattices:
its surjection gives representatives, its kernel is intertwining integral isomorphism,
and its restriction criterion is equality of embedded images. The universal pair is
normalized by the identity of the representing scheme. Together with naturality of
`e` and that restriction criterion, this says that every class is the pullback of
this universal lattice along its classifying morphism.

Source: latest Weil blueprint, sec-six-functors-basics/sk-lem-lattice-atlas/
sk-lem-stratified-lattice-scheme.md, assertions (1)--(4), and its .proof.md
(blueprint: det-lem-stratified-lattice-scheme).

Proof plan:
1. The continuous integral coefficient inclusion is injective in free coordinates
   (lem-weil-pbc-lattice-free-scalar-extension). The image criterion
   (lem-weil-pbc-lattice-pair-image-classification) identifies pairs with submodules.
   Apply lem-weil-pbc-lattice-sheaf-locally-constant to get the presentation and (1).
2. Refine a trivializing pro-etale cover to finitely many affine pieces using qcqs.
   Their disjoint union V is affine, pro-etale, and faithfully flat quasi-compact over X
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-proetale-qcqs-finite-family-geometry). Apply
   lem-sfb-proetale-constant-split-descent to the constant lattice set on V.
   The split scheme is separated, etale, ind-quasi-affine, and surjective, since
   the identity coset is a lattice, also in rank zero.
3. Apply lem-sfb-ind-quasi-affine-effective-descent (Stacks 0APK) to descend the
   split scheme. Apply lem-weil-pbc-fpqc-descend-separated and
   lem-galois-fpqc-descend-etale. Lifting a point to V and then to a split component
   proves surjectivity of the descended morphism.
4. By lem-weil-pbc-fpqc-representable-descent, maps into the descended scheme are
   exactly compatible local maps. Split descent and the sheaf axiom identify these
   naturally with lattice classes, proving representability.
5. The identity section gives a lattice representative over the representing scheme.
   Naturality gives its universal property. Affine opens in that scheme form an
   etale covering of X; restrict the universal lattice to obtain (4). -/
theorem integralLatticeSheaf_representable (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (r : ℕ)
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFreeOfRank r] :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U)),
      IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c ∧
      (∀ (V : X.ProEt),
        Nonempty (L.over V ≅ latticeFreeSheaf X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) V r) →
        Nonempty ((constantSheaf ((Scheme.ProEt.topology X).over V) (Type (u + 2))).obj
          (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)) ≅
            F.over V)) ∧
      (∃ (Z : X.Etale), IsSeparated Z.hom ∧ Surjective Z.hom ∧
        ∃ e : F.obj ≅ (Scheme.ProEt.forget X).op ⋙
            yoneda.obj ((Scheme.Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2},
          ∃ P : IntegralLatticePair (integralLatticeCoefficientMap X l E) L
              ((Scheme.toProEt X).obj Z),
            e.hom.app (op ((Scheme.toProEt X).obj Z))
              (c ((Scheme.toProEt X).obj Z) P) =
                ULift.up (𝟙 ((Scheme.Etale.forget X).obj Z))) ∧
      (∃ (I : Type (u + 1)) (W : I → X.Etale),
        X.smallEtaleTopology.CoversTop W ∧
        ∀ i : I, Nonempty (IntegralLatticePair (integralLatticeCoefficientMap X l E) L
          ((Scheme.toProEt X).obj (W i)))) := by
  classical
  have : L.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L r
  obtain ⟨F, c, hc, hconst⟩ := integralLatticeSheaf_locallyConstant X l E L
  have hrep : ∃ (Z : X.Etale), IsSeparated Z.hom ∧ Surjective Z.hom ∧
      ∃ e : F.obj ≅ (Scheme.ProEt.forget X).op ⋙
          yoneda.obj ((Scheme.Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2},
        ∃ P : IntegralLatticePair (integralLatticeCoefficientMap X l E) L
            ((Scheme.toProEt X).obj Z),
          e.hom.app (op ((Scheme.toProEt X).obj Z))
            (c ((Scheme.toProEt X).obj Z) P) =
              ULift.up (𝟙 ((Scheme.Etale.forget X).obj Z)) := by
    let S := ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)
    obtain ⟨I, U, hU, hu⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := L) (r := r)).mp
        (inferInstance : L.IsFiniteLocallyFreeOfRank r)
    let C := (constantSheaf (Scheme.ProEt.topology X) (Type (u + 2))).obj S
    let e (i : I) : F.over (U i) ≅ C.over (U i) := by
      let k := (hconst (U i) r (hu i).some).choose
      exact k.symm ≪≫
        (((Scheme.ProEt.topology X).overPullbackConstantSheafIso
          (Type (u + 2)) (U i)).app S).symm
    obtain ⟨V, p, hw, ha, hs, hqc, ⟨ep⟩⟩ :=
      exists_affine_constant_cover X F S I U hU e
    have := hw
    have := ha
    have := hs
    have := hqc
    obtain ⟨⟨rho, hnat, _hnorm, _halpha, D, hcompat⟩, htsep, htet, htsurj, htind⟩ :=
      proetaleConstantSplitDescent p S F ep
    let t := proetaleSplitCodiagonal V S
    have : IsSeparated t := htsep
    have : Etale t := htet
    have : Surjective t := htsurj inferInstance
    obtain ⟨Z₀, q, hq, hD⟩ :=
      Over.DescentDatum.isEffective_of_indQuasiAffine_flat_surjective_quasiCompact
        p t htind D
    have hZet : Etale Z₀.hom := by
      have hb : Etale (pullback.snd Z₀.hom p) := by
        apply (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
          hq.isoPullback.hom _).mp
        rw [hq.isoPullback_hom_snd]
        exact htet
      apply etale_of_fpqc_cover Z₀.hom (fun _ : PUnit.{1} ↦ V) (fun _ ↦ p)
      · simpa only [Presieve.ofArrows_pUnit] using p.singleton_mem_fpqcPrecoverage
      · intro _
        exact hb
    have hZsep : IsSeparated Z₀.hom := by
      have : IsSeparated (pullback.snd Z₀.hom p) := by
        apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated)
          hq.isoPullback.hom _).mp
        rw [hq.isoPullback_hom_snd]
        exact htsep
      exact isSeparated_of_flat_surjective_baseChange Z₀.hom p
    have hZsurj : Surjective Z₀.hom := by
      constructor
      intro x
      obtain ⟨v, hv⟩ := (inferInstance : Surjective p).surj x
      obtain ⟨z, hz⟩ := (inferInstance : Surjective t).surj v
      refine ⟨q z, ?_⟩
      change (q ≫ Z₀.hom) z = x
      rw [hq.w]
      change p (t z) = x
      rw [hz]
      exact hv
    let Z := Scheme.Etale.mk Z₀.hom
    obtain ⟨e⟩ := representable_of_effective_proetale_descent p t Z q hq F rho hnat D hD hcompat
      (proetale_singleton_covers p)
    obtain ⟨P, hP⟩ := lattice_identity_representative X l E L F c hc Z e
    exact ⟨Z, hZsep, hZsurj, e, P, hP⟩
  refine ⟨F, c, hc, ?_, hrep, ?_⟩
  · intro V ⟨e⟩
    obtain ⟨k, _⟩ := hconst V r e
    exact ⟨k⟩
  · obtain ⟨Z, _, hZ, e, P, _⟩ := hrep
    have := hZ
    exact ⟨PUnit.{u + 2}, fun _ ↦ Z, etale_singleton_covers X Z, fun _ ↦ ⟨P⟩⟩

end AlgebraicGeometry.ProEtale
