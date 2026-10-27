/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.SpaceUniversalConormal
public import Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.RingTheory.KoszulConormalBasis
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.Algebra.Module.Projective
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine splitting of the lci conormal transitivity sequence

Source: Stacks Project, spaces-more-morphisms.tex, Tags 06CB and 06CC;
criteria.tex, Tag 06D8, first paragraph
(blueprint: lem-sfb-affine-lci-conormal-splitting).

Conormals are those of any specified universal first-order thickenings. Both
arrows are normalized on actual local ideal tensors, and the isomorphism is the
finite biproduct map of the canonical first arrow and a section of the quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quotient map on conormals, normalized on actual ideal sections. Here `g`
is the map from the universal thickening over Y to the universal thickening over X.
This is the identity-source version of `IsSpaceConormalMap`, with no artificial
identity tensor pullback in the domain.
Source: Stacks, Tag 06BF and the ideal maps of Tag 0607
(blueprint: lem-sfb-affine-lci-conormal-splitting). -/
def IsSpaceConormalQuotient {S : Scheme.{u}} {Z W V : AlgebraicSpace S}
    (g : W ⟶ V) (i : Z ⟶ W) (j : Z ⟶ V)
    (ρ : spaceConormal j ⟶ spaceConormal i) : Prop :=
  ∀ (U : Z.EtaleSite) (B : W.EtaleSite) (A : V.EtaleSite)
    (b : B.obj.left ⟶ A.obj.left)
    (_hb : yoneda.map b ≫ A.obj.hom = B.obj.hom ≫ g.hom.hom)
    (c : U.obj.left ⟶ B.obj.left)
    (hc : yoneda.map c ≫ B.obj.hom = U.obj.hom ≫ i.hom.hom)
    (d : U.obj.left ⟶ A.obj.left)
    (hd : yoneda.map d ≫ A.obj.hom = U.obj.hom ≫ j.hom.hom),
    c ≫ b = d → ∀ (s : (spaceKernel j).val.obj (op A))
      (t : (spaceKernel i).val.obj (op B)),
      (kernel.ι (moduleStructureMap i)).val.app (op B) t =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map b.left.op)
          ((kernel.ι (moduleStructureMap j)).val.app (op A) s) →
      ρ.val.app (op U) (spaceConormalSection j U A d hd s) =
        spaceConormalSection i U B c hc t

/-- The inclusion of a Zariski open of a scheme, regarded as an algebraic-space map.
Source: Stacks, Tag 03G1, scheme objects in the small etale site
(blueprint: lem-sfb-affine-lci-conormal-splitting). -/
def conormalOpenMap {S : Scheme.{u}} (Z : Over S) (U : Z.left.Opens) :
    schemeSpace (Over.mk (U.ι ≫ Z.hom)) ⟶ schemeSpace Z :=
  ObjectProperty.homMk ⟨yoneda.map (Over.homMk U.ι)⟩

/-- Affine lci conormal splitting, with the canonical first summand retained.
Source: Stacks, Tags 06CB, 06CC and 06D8, first paragraph
(blueprint: lem-sfb-affine-lci-conormal-splitting).

Proof:
1. Use lem-sfb-unramified-lci-koszul-etale-charts and
   lem-sfb-universal-conormal-chart-transitivity to obtain etale Koszul immersion
   charts. The closed-case identification of lem-sfb-space-universal-conormal and
   lem-sc-koszul-conormal-basis make the quotient conormal finite free there.
   Lem-sfb-etale-finite-free-zariski-descent gives the displayed Zariski frames.
2. Refine these charts using affine etale charts of the universal thickening of Y
   over X (lem-trf-space-fibre-products-etale-covers). Etale lifting identifies the
   refinements with universal thickenings. Write their rings A, A/I and A/J,
   where I is contained in J, I squared is zero, and J/I is Koszul regular.
3. Universality identifies the thickening of the last chart over X with A/J squared.
   The three conormals are I/IJ, J/J squared and J/(I+J squared). The first arrow
   sends i to i; the second is the quotient. The tensor-pullback comparison of
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies these formulas
   with precisely the two local tensor normalizations in this statement.
4. Lem-sfb-h1-regular-quotient-ideal-intersection gives I intersect J squared = IJ.
   Thus the first arrow is injective, its image is the kernel of the quotient,
   and the quotient is surjective. Apply
   lem-sfb-scheme-etale-module-exact-finiteness-comparison and descend exactness.
5. All three terms are quasi-coherent, using
   lem-sfb-space-module-pullback-quasicoherent for the first. Transfer to Zariski
   modules with lem-trf-scheme-zariski-etale-quasi-coherent-equivalence; its exact
   faithful comparison reflects exactness. On affine Z,
   lem-pc-affine-extension-section-surjectivity makes the map on sections surjective.
   Lem-pc-finite-flat-affine-sections-projective makes the quotient sections
   projective. Lift their identity by def-weil-pbc-projective-module.
6. The counit of lem-weil-pbc-affine-tilde-gamma-adjunction turns this lift into a
   sheaf section. Transport back by the normalized etale equivalence. Naturality
   gives s followed by rho equal to the identity of the same quotient.
7. The finite biproduct map (lambda,s) is invertible: subtract s rho(e) from e and use
   exactness to obtain the unique preimage under lambda. These local preimages
   glue and give the inverse (r,rho). The first summand is exactly lambda.
   Empty schemes and rank zero require no exception. -/
theorem affine_lci_conormal_splitting {S : Scheme.{u}} (Z : Over S)
    [IsAffine Z.left] {Y X : AlgebraicSpace S}
    (u : schemeSpace Z ⟶ Y) (v : Y ⟶ X)
    (hu : SpaceFormallyUnramified u) (hv : SpaceFormallyUnramified v)
    (hlci : RelativeFiniteHilbert.SpaceProperty
      (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) u.hom.hom)
    (WYX WZX WZY : AlgebraicSpace S)
    (kYX : Y ⟶ WYX) (qYX : WYX ⟶ X)
    (kZX : schemeSpace Z ⟶ WZX) (qZX : WZX ⟶ X)
    (kZY : schemeSpace Z ⟶ WZY) (qZY : WZY ⟶ Y)
    (hYX : IsUniversalSpaceFirstOrderThickening v kYX qYX)
    (hZX : IsUniversalSpaceFirstOrderThickening (u ≫ v) kZX qZX)
    (hZY : IsUniversalSpaceFirstOrderThickening u kZY qZY) :
    ∃ (a : WZX ⟶ WYX) (b : WZY ⟶ WZX)
      (lam : (moduleTensorPullback u).obj (spaceConormal kYX) ⟶ spaceConormal kZX)
      (ρ : spaceConormal kZX ⟶ spaceConormal kZY),
      kZX ≫ a = u ≫ kYX ∧ a ≫ qYX = qZX ∧
      kZY ≫ b = kZX ∧ b ≫ qZX = qZY ≫ v ∧
      IsSpaceConormalMap u a kZX kYX lam ∧ IsSpaceConormalQuotient b kZY kZX ρ ∧
      ((moduleTensorPullback u).obj (spaceConormal kYX)).IsQuasicoherent ∧
      (spaceConormal kZX).IsQuasicoherent ∧ (spaceConormal kZY).IsQuasicoherent ∧
      (∀ z : Z.left, ∃ U : Z.left.Opens, z ∈ U ∧ ∃ r : ℕ,
        Nonempty (((moduleTensorPullback (conormalOpenMap Z U)).obj (spaceConormal kZY)) ≅
          (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
            (schemeSpace (Over.mk (U.ι ≫ Z.hom))).structureSheaf))) ∧
      ∃ h : lam ≫ ρ = 0, (ShortComplex.mk lam ρ h).ShortExact ∧
        ∃ s : spaceConormal kZY ⟶ spaceConormal kZX,
          s ≫ ρ = 𝟙 (spaceConormal kZY) ∧ IsIso
            ((prod.fst : (moduleTensorPullback u).obj (spaceConormal kYX) ⨯
                spaceConormal kZY ⟶ (moduleTensorPullback u).obj (spaceConormal kYX)) ≫ lam +
              (prod.snd : (moduleTensorPullback u).obj (spaceConormal kYX) ⨯
                spaceConormal kZY ⟶ spaceConormal kZY) ≫ s) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
