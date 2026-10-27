/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData
public import Mathlib.RingTheory.Flat.Basic

/-! # Coherence of the specified polynomial Koszul diagonal maps

Source: Stacks Project, dualizing.tex, Tags 0E2E, 0BZI, 0BZJ, and the explicit
scalar-extension construction of lem-sfb-polynomial-koszul-diagonal-class.
(blueprint: def-sfb-polynomial-koszul-diagonal-system).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Canonical identification of identity extension, fixed by the restriction adjunction.
Source: Stacks 08DW (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
def koszulDiagonalExtensionId {B : Type u} [CommRing B]
    (f : B →+* B) (hf : f = RingHom.id B) : relativeDualizingDerivedExtension f ≅ 𝟭 _ :=
  ((koszulDiagonalExtensionAdjunction f).ofNatIsoRight
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId' f hf) ≪≫
      Functor.mapDerivedCategoryIdIso _)).leftAdjointUniq Adjunction.id

/-- Canonical composition of scalar extensions, fixed by the two restriction adjunctions.
Source: Stacks 08DW (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
def koszulDiagonalExtensionComp {B D H : Type u}
    [CommRing B] [CommRing D] [CommRing H]
    (f : B →+* D) (g : D →+* H) (h : B →+* H) (hh : h = g.comp f) :
    relativeDualizingDerivedExtension f ⋙ relativeDualizingDerivedExtension g ≅
      relativeDualizingDerivedExtension h :=
  (((koszulDiagonalExtensionAdjunction f).comp
    (koszulDiagonalExtensionAdjunction g)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g h hh) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).symm).leftAdjointUniq
          (koszulDiagonalExtensionAdjunction h)

/-- The graph-normalized diagonal isomorphisms for all localized polynomial charts of B.
The final field is precisely invertibility of multiplication by their adjunct classes.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
structure PolynomialKoszulDiagonalDatum (R B : Type u)
    [CommRing R] [CommRing B] [Algebra R B] where
  kappa : ∀ C : PolynomialKoszulChart R B, C.diagonalHom ≅ koszulDiagonalUnit B
  normalized : ∀ C : PolynomialKoszulChart R B, IsKoszulDiagonalNormalization C (kappa C)
  multiplication : ∀ C : PolynomialKoszulChart R B,
    IsIso (relativeDualizingModuleClassMap R B C.firstPullback (C.diagonalClass (kappa C)))

/-- An assignment of the specified data to every flat finitely presented algebra over
any Noetherian commutative base. No proper scheme or global dualizing pair is supplied.
Source: Stacks 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
abbrev PolynomialKoszulDiagonalAssignment : Type (u + 1) :=
  ∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B],
      PolynomialKoszulDiagonalDatum R B

/-- A normalized exchange paired with its class compatibility, using the canonical
comparison of the degree-zero diagonal and first pullback.
Source: Stacks 0A71, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
def IsKoszulDiagonalCompatibleChange {R B S D : Type u}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    (K : PolynomialKoszulDiagonalDatum R B) (L : PolynomialKoszulDiagonalDatum S D)
    {C : PolynomialKoszulChart R B} {E : PolynomialKoszulChart S D}
    (F : KoszulDiagonalChartChange C E)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model) : Prop :=
  F.IsComparison c ∧ F.PreservesClass (K.kappa C) (L.kappa E) c

/-- Compatibility with identity and successive base changes is an equality of the
specified evaluation-mate comparisons, under the canonical scalar extension identifications.
Source: Stacks 0A71, 0E2E (blueprint: def-sfb-polynomial-koszul-diagonal-system). -/
structure IsPolynomialKoszulDiagonalSystem (K : PolynomialKoszulDiagonalAssignment.{u}) : Prop where
  change : ∀ (R B S D : Type u)
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing S] [Module.Flat S D] [Algebra.FinitePresentation S D]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D)
    (F : KoszulDiagonalChartChange C E), F.IsAdmissible →
    ∃ c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model,
      IsKoszulDiagonalCompatibleChange (K R B) (K S D) F c
  identity : ∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C : PolynomialKoszulChart R B) (F : KoszulDiagonalChartChange C C)
    (hf : F.ring = RingHom.id B) (_hg : F.ambient = RingHom.id C.P)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ C.model),
    F.IsComparison c → c.hom = (koszulDiagonalExtensionId F.ring hf).hom.app C.model
  composition : ∀ (R B S D T H : Type u)
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [CommRing T] [CommRing H] [Algebra T H]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing S] [Module.Flat S D] [Algebra.FinitePresentation S D]
    [IsNoetherianRing T] [Module.Flat T H] [Algebra.FinitePresentation T H]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart S D)
    (J : PolynomialKoszulChart T H)
    (F : KoszulDiagonalChartChange C E) (G : KoszulDiagonalChartChange E J)
    (FG : KoszulDiagonalChartChange C J)
    (_hb : FG.base = G.base.comp F.base)
    (hd : FG.ring = G.ring.comp F.ring)
    (_hp : FG.ambient = G.ambient.comp F.ambient)
    (cF : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model)
    (cG : (relativeDualizingDerivedExtension G.ring).obj E.model ≅ J.model)
    (cFG : (relativeDualizingDerivedExtension FG.ring).obj C.model ≅ J.model),
    F.IsAdmissible → G.IsAdmissible → FG.IsAdmissible →
    F.IsComparison cF → G.IsComparison cG → FG.IsComparison cFG →
    (relativeDualizingDerivedExtension G.ring).map cF.hom ≫ cG.hom =
      (koszulDiagonalExtensionComp F.ring G.ring FG.ring hd).hom.app C.model ≫ cFG.hom
  refinement : ∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C E : PolynomialKoszulChart R B) (F : KoszulDiagonalRefinement C E),
    F.PreservesClass ((K R B).kappa C) ((K R B).kappa E)
  iterated : ∀ (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    (C E : PolynomialKoszulChart R B) (f g : E.model ⟶ C.model),
    KoszulDiagonalRefinementPath C E f → KoszulDiagonalRefinementPath C E g → f = g
  refinement_change : ∀ (R B S D : Type u)
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [CommRing D] [Algebra S D]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing S] [Module.Flat S D] [Algebra.FinitePresentation S D]
    (C E : PolynomialKoszulChart R B) (C' E' : PolynomialKoszulChart S D)
    (F : KoszulDiagonalRefinement C E) (G : KoszulDiagonalRefinement C' E')
    (b : B →+* D) (H : KoszulDiagonalChartChange C C')
    (J : KoszulDiagonalChartChange E E')
    (hH : H.ring = b) (hJ : J.ring = b)
    (_hb : H.base = J.base)
    (_hp : H.ambient.comp F.evaluation.toRingHom =
      G.evaluation.toRingHom.comp J.ambient)
    (e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
      C.coefficient)
    (e' : (ModuleCat.derivedCoinduction G.evaluation.toRingHom).obj E'.coefficient ≅
      C'.coefficient)
    (cH : (relativeDualizingDerivedExtension b).obj C.model ≅ C'.model)
    (cJ : (relativeDualizingDerivedExtension b).obj E.model ≅ E'.model),
    H.IsAdmissible → J.IsAdmissible → F.IsContraction e → G.IsContraction e' →
    H.IsComparison (eqToIso (congrArg
      (fun t : B →+* D ↦ (relativeDualizingDerivedExtension t).obj C.model) hH) ≪≫ cH) →
    J.IsComparison (eqToIso (congrArg
      (fun t : B →+* D ↦ (relativeDualizingDerivedExtension t).obj E.model) hJ) ≪≫ cJ) →
    (relativeDualizingDerivedExtension b).map (F.modelMap e) ≫ cH.hom =
      cJ.hom ≫ G.modelMap e'

end AlgebraicGeometry
