/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import all WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage

/-! # The canonical compact-support scalar/site square

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts; Stacks Tags 09A6, 09AF,
07A7, 0D6D and 0GL1 (blueprint: lem-sp-finite-ctf-site-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The bounded-below variant for arbitrary finite commutative rings. Only the
site comparisons are asserted invertible; neither scalar map is inverted.
Source: latest blueprint, Charts; Stacks 09A6, 09AF, 07A7, 0D6D and 0GL1
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

Proof: (1) properness makes c.g qcqs; exact open extension sends L and L_B
into D+. (2) The normalized proper comparison is invertible there, as is the
exact open comparison, so both compact-support site maps are invertible.
(3) The inverse open site comparison has adjunct given by the site/pullback
comparison and the etale open unit. The inverse scalar/open balancing map has
adjunct given by the inverse scalar/pullback map and the scalar-extended unit.
(4) Apply the scalar/site/pullback cube to c.i; these adjunct formulas make
the two inverse open routes equal. Injectivity of the B-linear open adjunction
gives the open square. (5) Apply the direct-image scalar/site mate equation to
c.g and j_!L; its scalar extension is bounded below by open balancing.
Precompose with scalar extension of the A-site comparison to remove its inverse.
(6) Paste this proper square with the open square. Naturality of the proper
scalar mate at the A-open comparison and of the B-site mate at the etale
balancing map gives exactly the displayed equality, without forgetting B-actions. -/
theorem finiteCtfSiteCoefficientSquare_of_boundedBelow
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [IsNoetherian c.Z]
    (L : Etale.DerivedCategoryModule A X)
    (_hL : _root_.DerivedCategory.TStructure.t.plus L)
    (_hLB : _root_.DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj L)) :
    IsIso (finiteCtfCompactSiteMap A c L) ∧
      IsIso (finiteCtfCompactSiteMap B c ((Etale.scalarExtension φ X).obj L)) ∧
      FiniteCtfSiteCoefficientSquare φ c L := by
  let IA := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let IB := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
  have hopen (R : Type (u + 1)) [CommRing R]
      (M : Etale.DerivedCategoryModule R X)
      (hM : _root_.DerivedCategory.TStructure.t.plus M) :
      _root_.DerivedCategory.TStructure.t.plus
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M) := by
    obtain ⟨n, hn⟩ := hM
    have := hn
    exact ⟨n, Functor.isGE_mapDerivedCategory_obj _ M n⟩
  have hJ := hopen A L _hL
  have hJB := hopen B ((Etale.scalarExtension φ X).obj L) _hLB
  have hTJ : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ c.Z).obj (IA.obj L)) := by
    exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.openScalarExtension φ c.i).app L).symm hJB
  have := ProEtale.directImageComparisonAmbient_isIso A c.g (IA.obj L) hJ
  have := ProEtale.directImageComparisonAmbient_isIso B c.g
    (IB.obj ((Etale.scalarExtension φ X).obj L)) hJB
  refine ⟨?_, ?_, ?_⟩
  · unfold finiteCtfCompactSiteMap
    infer_instance
  · unfold finiteCtfCompactSiteMap
    infer_instance
  · have ho := ProEtale.OpenScalarSite.scalar_site_square_aux φ c.i L
    have hp := ProEtale.etaleProEtale_scalar_mate φ c.g (IA.obj L) hJ hTJ
    let CA (T : Scheme.{u}) :=
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
    let CB (T : Scheme.{u}) :=
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory
    let T (Z : Scheme.{u}) :=
      @ProEtale.pbcFixedScalarExtension.{u} Z.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z)
        A B inferInstance inferInstance φ
    let PA := (ProEtale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
    let PB := (ProEtale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
    let EB := (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
    let IPB := (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
    let eA := (ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) c.i).hom.app L
    let eB := (ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} B) c.i).hom.app ((Etale.scalarExtension φ X).obj L)
    let dA := (ProEtale.directImageComparisonAmbient A c.g).app (IA.obj L)
    let dB := ProEtale.directImageComparisonAmbient B c.g
    let δZ := (ProEtale.pbcComparisonReduction c.Z φ).hom.app (IA.obj L)
    let δY := (ProEtale.pbcComparisonReduction Y φ).hom.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj (IA.obj L))
    let δX := (ProEtale.pbcComparisonReduction X φ).hom.app L
    let v := (Etale.openScalarExtension φ c.i).hom.app L
    let w := (ProEtale.OpenScalarSite.scalarOpen φ c.i).hom.app ((CA X).obj L)
    let γ := (mateEquiv
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
      (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso φ c.g).hom)).natTrans
    let γe := (Etale.scalarMate φ c.g).app (IA.obj L)
    have hn := γ.naturality eA
    dsimp only [Functor.comp_map] at hn
    have hd := dB.naturality v
    dsimp only [Functor.comp_map] at hd
    have hp' : (T Y).map dA ≫ γ.app ((CA c.Z).obj (IA.obj L)) ≫ PB.map δZ =
        δY ≫ (CB Y).map γe ≫ dB.app ((Etale.scalarExtension φ c.Z).obj (IA.obj L)) := by
      have h := congrArg (fun q ↦ (T Y).map dA ≫ q) hp
      simp only [T, dA, ProEtale.directImageComparisonAmbientIso, asIso_inv,
        ← Functor.map_comp_assoc, IsIso.hom_inv_id] at h
      rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
      simpa only [T, dA, γ, CA, PB, δZ, δY, CB, γe, dB,
        ProEtale.scalarPullbackEtaleIso, Etale.scalarMate, Etale.scalarExtension] using h
    change (T Y).map (dA ≫ PA.map eA) ≫
        (γ.app _ ≫ PB.map w) ≫ PB.map (IPB.map δX) =
      δY ≫ (CB Y).map ((Etale.compactScalarMap φ c).app L) ≫
        (dB.app _ ≫ PB.map eB)
    have hb : (Etale.compactScalarMap φ c).app L = γe ≫ EB.map v := by
      simp only [Etale.compactScalarMap, Etale.ExceptionalCoefficients.compactSupportMap,
        Etale.compactScalarOpen_eq, γe, EB, v, IA]
    rw [hb]
    calc
      _ = (T Y).map dA ≫ γ.app _ ≫
          PB.map ((T c.Z).map eA ≫ w ≫ IPB.map δX) := by
        simpa only [Functor.map_comp, Category.assoc, T, PA, PB, CA, IA,
          Functor.comp_obj] using congrArg
          (fun q ↦ (T Y).map dA ≫ q ≫ PB.map w ≫ PB.map (IPB.map δX)) hn
      _ = (T Y).map dA ≫ γ.app _ ≫
          PB.map (δZ ≫ (CB c.Z).map v ≫ eB) := by
        rw [ho]
      _ = δY ≫ (CB Y).map γe ≫ dB.app _ ≫
          PB.map ((CB c.Z).map v) ≫ PB.map eB := by
        simp only [Functor.map_comp]
        rw [reassoc_of% hp']
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← reassoc_of% hd]

/-- The finite-torsion constructible finite-Tor case, with all the geometric and
coefficient hypotheses of the node. The Tate-twist convention is the existing
finiteEtaleTateTwist; no twist occurs in this square.
Source: latest blueprint, Charts; Stacks 09A6, 09AF, 07A7, 0D6D and 0GL1
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

Proof: choose the common Tor interval [a,b] of L and apply its universal
module-sheaf test to B_X. It follows that L_B has cohomology in [a,b], so is
bounded below. L is bounded by the constructible finite-Tor hypothesis.
Apply the bounded-below variant, whose six-step proper/open mate proof is
recorded above. Invertibility of N and the twist convention introduce no extra
maps, and neither beta nor b is asserted invertible. -/
theorem finiteCtfSiteCoefficientSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (N : ℕ) (_hN : 1 ≤ N) (_hA : (N : A) = 0) (_hB : (N : B) = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [IsNoetherian c.Z]
    (_hNX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (_hNY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (_hNZ : ∀ z : c.Z, IsUnit (N : c.Z.presheaf.stalk z))
    (L : Etale.DerivedCategoryModule A X)
    (_hctf : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L) :
    IsIso (finiteCtfCompactSiteMap A c L) ∧
      IsIso (finiteCtfCompactSiteMap B c ((Etale.scalarExtension φ X).obj L)) ∧
      FiniteCtfSiteCoefficientSquare φ c L := by
  obtain ⟨a, b, hTor⟩ := _hctf.2
  have hTor' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hTor
  have hLB := Etale.scalarExtension_lowerBound φ X L a b hTor'
  exact finiteCtfSiteCoefficientSquare_of_boundedBelow φ c L
    _hctf.1.1.1 ⟨a, hLB⟩

end AlgebraicGeometry
