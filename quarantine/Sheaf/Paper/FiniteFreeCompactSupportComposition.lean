/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.FiniteFreeCompactSupportData
import Sheaf.Paper.FiniteFreeCompactSupportSiteSquare
import Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension

/-! # Finite-free compact-support composition

The canonical constructions are re-exported unchanged from the data module.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: lem-pur-finite-free-compact-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.FiniteCoefficientAdjoints
namespace AlgebraicGeometry.FiniteFreeCompactSupport

private theorem coefficientMap_naturality (pro : Bool)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : Sites.D pro A X} (v : K ⟶ K') :
    (Sites.scalar pro φ Y).map ((support pro A c).map v) ≫
        coefficientMap pro φ c K' =
      coefficientMap pro φ c K ≫
        (support pro B c).map ((Sites.scalar pro φ X).map v) := by
  cases pro
  · let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    let R := (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
    change (Etale.scalarExtension φ Y).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map (J.map v)) ≫
        (Etale.scalarMate φ c.g).app (J.obj K') ≫
          R.map ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K') =
      ((Etale.scalarMate φ c.g).app (J.obj K) ≫
        R.map ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K)) ≫
          R.map ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B)
            c.i).mapDerivedCategory.map ((Etale.scalarExtension φ X).map v))
    have hp := (Etale.scalarMate φ c.g).naturality (J.map v)
    dsimp only [Functor.comp_map] at hp
    rw [← Category.assoc, hp]
    simp only [Category.assoc]
    rw [← R.map_comp, ← R.map_comp]
    congr 1
    have hj := (Etale.ExceptionalCoefficients.openIso φ c.i).hom.naturality v
    dsimp only [Functor.comp_map] at hj
    exact congrArg R.map hj
  · let aX := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    let aY := Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    let F := ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let G := ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let ρ := ProEtale.compactSupportRestrictionIso φ c
    change (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).leftAdjoint.map
        (F.map v) ≫ (aY.homEquiv _ _).symm
          (F.map (aX.unit.app K') ≫ ρ.hom.app
            ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.obj K')) =
      (aY.homEquiv _ _).symm (F.map (aX.unit.app K) ≫ ρ.hom.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.obj K)) ≫
          G.map ((Sheaf.derivedRestrictScalars
            (Scheme.ProEt.topology X) φ).leftAdjoint.map v)
    apply (aY.homEquiv _ _).injective
    rw [aY.homEquiv_naturality_left, aY.homEquiv_naturality_right]
    simp only [Functor.id_obj, Equiv.apply_symm_apply]
    have hu := aX.unit.naturality v
    have hr := ρ.hom.naturality
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).leftAdjoint.map v)
    dsimp only [Functor.id_map, Functor.comp_map] at hu hr
    change F.map v ≫ F.map (aX.unit.app K') ≫ _ = _
    rw [← Category.assoc, ← F.map_comp, hu, F.map_comp]
    simp only [Category.assoc]
    exact congrArg (fun w ↦ F.map (aX.unit.app K) ≫ w) hr

private theorem scalar_plus {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K : Sites.D false A X)
    {a b : ℤ} (ht : Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    _root_.DerivedCategory.TStructure.t.plus ((Sites.scalar false φ X).obj K) := by
  refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_⟩
  apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
  exact (ht (Etale.scalarCoefficientSheaf φ X) q (Or.inl hq)).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.scalarTensorIso φ X).app K))

private theorem origin (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) (K : Sites.D pro A X) (hK : Sites.Ctf pro A X K) :
    ∃ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Nonempty ((realization pro A X).obj L.obj ≅ K) := by
  cases pro
  · obtain ⟨a, b, _, hz⟩ := hK.1.2
    have hb : _root_.DerivedCategory.TStructure.t.plus K :=
      ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ hz q (Or.inl hq)⟩
    exact ⟨⟨K, hb⟩, ⟨Iso.refl _⟩⟩
  · obtain ⟨L, hL, e⟩ := hK.plusEtaleOrigin
    exact ⟨⟨L, hL⟩, e⟩

private theorem scalar_origin (pro : Bool)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (K : Sites.D pro A X) (hK : Sites.Ctf pro A X K) :
    ∃ N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      Nonempty ((realization pro B X).obj N.obj ≅ (Sites.scalar pro φ X).obj K) := by
  cases pro
  · obtain ⟨a, b, _, ht⟩ := hK.2
    exact ⟨⟨(Sites.scalar false φ X).obj K, scalar_plus φ X K ht⟩, ⟨Iso.refl _⟩⟩
  · obtain ⟨L, _, ⟨e⟩⟩ := hK.plusEtaleOrigin
    obtain ⟨a, b, ht⟩ := hK.2
    have htL := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
    have het := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := A) a b L).mp htL
    have hp := scalar_plus φ X L
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr het)
    refine ⟨⟨(Sites.scalar false φ X).obj L, hp⟩, ⟨?_⟩⟩
    exact (Sites.scalarSite φ X).symm.app L ≪≫ (Sites.scalar true φ X).mapIso e

private theorem etale_coefficient_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (K : Sites.D false A X) :
    IsIso (coefficientMap false φ c K) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (Etale.properFiniteCoefficientExtension φ c.g).1
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)
  dsimp only [coefficientMap, Etale.ExceptionalCoefficients.compactSupportMap]
  infer_instance

private theorem pro_coefficient_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hφ : letI := φ.toAlgebra; Module.Finite A B ∧ Module.Free A B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (K : Sites.D true A X) (hK : Sites.Ctf true A X K) :
    IsIso (coefficientMap true φ c K) := by
  obtain ⟨L, hL, ⟨α⟩⟩ := hK.plusEtaleOrigin
  obtain ⟨a, b, ht⟩ := hK.2
  have htL := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso α.symm ht
  have het := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
    (Λ := A) a b L).mp htL
  have hp := scalar_plus φ X L
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr het)
  let M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨L, hL⟩
  let N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨(Sites.scalar false φ X).obj L, hp⟩
  have hs := finiteFree_site_square φ hφ c M N (Iso.refl _)
  have hi := etale_coefficient_isIso φ c L
  have hi' : IsIso (coefficientMap true φ c ((Sites.nu A X).obj L)) := by
    rw [hs]
    infer_instance
  have hn := coefficientMap_naturality true φ c α.hom
  have hh : IsIso (coefficientMap true φ c ((Sites.nu A X).obj L) ≫
      (support true B c).map ((Sites.scalar true φ X).map α.hom)) := by infer_instance
  have hh' : IsIso ((Sites.scalar true φ Y).map
      ((support true A c).map α.hom) ≫ coefficientMap true φ c K) := by
    exact hn.symm ▸ hh
  exact IsIso.of_isIso_comp_left
    ((Sites.scalar true φ Y).map ((support true A c).map α.hom))
    (coefficientMap true φ c K)

/-- Finite-free extension preserves the specified coefficient maps, refinement and
composition, as actual B-linear arrows on both sites.
Source: blueprint main-20261015, sk-thm-purity-transport.proof.md Steps 1 and 3
(blueprint: lem-pur-finite-free-compact-composition).

Proof (the eight steps of the node):
1. lem-coef-finite-free-extension identifies the ramified quotient with the quotient
by the nth power of the base uniformizer, and makes its scalar map finite free.
lem-pur-derived-change-of-rings computes it termwise on K-flat representatives.
lem-trf-open-ctf, cor-sf-direct-image-ctf-nonproper, its pro-etale counterpart, and
lem-kun-dimension-finite-type certify every intermediate constructible Tor domain.
lem-sf-proetale-constructible-origin supplies all witnesses used in the statement.
2. On c=(j,p), lem-coef-finite-direct-image makes the proper extended-counit map
invertible. lem-pur-etale-open-derived-tensor gives the open balancing isomorphism.
Their composite is coefficientMap; both maps retain the B action.
3. Apply lem-sf-proper-open-coefficient-refinement to the specified proper/open alpha.
Apply Rp_* and naturality of its coefficient map, then its composition identity.
Invert the two geometric refinement comparisons to obtain the displayed square.
4. For compatible compactifications, the proper composition square is the identity
of lem-coef-finite-direct-image. The open composition square follows termwise from
lem-cbc-extension-zero-composition: both maps keep the same supported sections.
5. The middle proper/open interchange is the normalized map of
lem-cbc-proper-open-interchange-coherence. On bounded-below injectives it equals
lem-amb-unbounded-proper-open-interchange. Scalar/pullback balancing agrees on
K-flat tensors; lem-weil-pbc-mate-pasting gives its counit-mate exchange square.
6. Insert the open balancing unit identity into that square and transpose under the
open adjunction. Both transposes reduce to the proper coefficient map. Injectivity
of the adjunction bijection proves the B-linear interchange square. Pasting with
Step 4 gives the composition equation for the compatible compactifications.
7. Use Step 3 to conjugate by comparisons to arbitrary compactifications. Their
coherence (lem-amb-etale-compact-comparisons) cancels adjacent inverse comparisons.
8. Transport through lem-sf-class-compact-support-comparison. Scalar/site balancing
is Sites.scalarSite. Proper maps transport by the fixed counit mate and direct-image
composition; open maps by lem-cbc-proetale-extension-zero-comparison and
lem-sf-comparison-open-tensor-coherence. Mate pasting transports the interchange.
lem-pur-compact-support-site-coherence and the proper/open site normalization
transport both geometric comparisons. Naturality inserts any retained witness,
including arbitrary isomorphic realizations and identity witnesses. -/
theorem finite_free_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) (t : Stage l E) (a : Arrow (baseStage n) t)
    (_level : t.exponent = n) (pro : Bool)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (K : Sites.D pro (baseStage (l := l) (E := E) n).ring X)
    (_hK : Sites.Ctf pro (baseStage (l := l) (E := E) n).ring X K) :
    (∀ (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (baseStage (l := l) (E := E) n).ring))),
      Sites.Ctf false (baseStage (l := l) (E := E) n).ring X L.obj →
      ∀ (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
        (γ : N.obj ≅ (Sites.scalar false a.ringMap X).obj L.obj),
        SiteCompatibility a.ringMap c L N γ) ∧
    IsIso (coefficientMap pro a.ringMap c K) ∧
    (∀ (K' : Sites.D pro (baseStage (l := l) (E := E) n).ring X),
      Sites.Ctf pro (baseStage (l := l) (E := E) n).ring X K' → ∀ v : K ⟶ K',
      (Sites.scalar pro a.ringMap Y).map ((support pro _ c).map v) ≫
          coefficientMap pro a.ringMap c K' =
        coefficientMap pro a.ringMap c K ≫
          (support pro t.ring c).map ((Sites.scalar pro a.ringMap X).map v)) ∧
    (∃ (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (baseStage (l := l) (E := E) n).ring))),
      Nonempty ((realization pro _ X).obj L.obj ≅ K)) ∧
    (∃ (N : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring))),
      Nonempty ((realization pro _ X).obj N.obj ≅ (Sites.scalar pro a.ringMap X).obj K)) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (baseStage (l := l) (E := E) n).ring)))
      (α : (realization pro _ X).obj L.obj ≅ K)
      (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
      (β : (realization pro _ X).obj N.obj ≅ (Sites.scalar pro a.ringMap X).obj K),
      (Sites.scalar pro a.ringMap Z).map (composition pro _ c d e L α) ≫
          coefficientMap pro a.ringMap e K =
        coefficientMap pro a.ringMap d ((support pro _ c).obj K) ≫
          (support pro t.ring d).map (coefficientMap pro a.ringMap c K) ≫
            composition pro t.ring c d e N β ∧
      ∀ (c' : Compactification f) (r : c'.Refinement c),
        (Sites.scalar pro a.ringMap Y).map (refinement pro _ r L α) ≫
            coefficientMap pro a.ringMap c K =
          coefficientMap pro a.ringMap c' K ≫ refinement pro t.ring r N β) := by
  let : IsNoetherian X := finiteTypeNoetherian D.k X
  let : IsNoetherian Y := finiteTypeNoetherian D.k Y
  let : IsNoetherian Z := finiteTypeNoetherian D.k Z
  have hφ := stage_finiteFree a (show (baseStage n).exponent = t.exponent from _level.symm)
  refine ⟨?_, ?_, ?_, origin pro _ X K _hK, scalar_origin pro a.ringMap X K _hK, ?_⟩
  · intro L _ N γ
    exact finiteFree_site_square a.ringMap hφ c L N γ
  · cases pro
    · exact etale_coefficient_isIso a.ringMap c K
    · exact pro_coefficient_isIso a.ringMap hφ c K _hK
  · intro K' _ v
    exact coefficientMap_naturality pro a.ringMap c v
  · intro L α N β
    exact finiteFree_geometric_squares a.ringMap hφ pro c d e L α N β

end AlgebraicGeometry.FiniteFreeCompactSupport
