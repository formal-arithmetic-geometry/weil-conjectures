/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarMate
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

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

/-- The canonical compact-support site comparison: the proper counit mate followed
by the exact open-extension comparison. This is a map of ordinary constant-ring
module derived categories, with no realization data.
Source: Stacks 09A6 and 09AF (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfCompactSiteMap (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule R X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj L) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) :=
  (ProEtale.directImageComparisonAmbient R c.g).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj L) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map
      ((ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) c.i).hom.app L)

/-- The pro-etale proper B-linear transpose of the scalar-extended A-counit,
followed by the canonical open balancing map.
Source: Stacks 07A7 and 0GL1 (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfProEtaleScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.pbcFixedScalarExtension (ProEt.topology Y) φ).obj
        ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology X) φ).obj M) :=
  (mateEquiv
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
    (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso φ c.g).hom)).natTrans.app
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((ProEtale.OpenScalarSite.scalarOpen φ c.i).hom.app M)

/-- The displayed square of actual constant-ring derived maps. The named maps
are the canonical proper/open composites; delta is the canonical tensor/site map.
Source: latest blueprint, Charts; Stacks 07A7, 09AF and 0D6D
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def FiniteCtfSiteCoefficientSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) : Prop :=
  (ProEtale.pbcFixedScalarExtension (ProEt.topology Y) φ).map
      (finiteCtfCompactSiteMap A c L) ≫
    finiteCtfProEtaleScalarMap φ c
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      ((ProEtale.pbcComparisonReduction X φ).hom.app L) =
  (ProEtale.pbcComparisonReduction Y φ).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
      ((Etale.compactScalarMap φ c).app L) ≫
    finiteCtfCompactSiteMap B c ((Etale.scalarExtension φ X).obj L)

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
  sorry

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
  sorry

end AlgebraicGeometry
