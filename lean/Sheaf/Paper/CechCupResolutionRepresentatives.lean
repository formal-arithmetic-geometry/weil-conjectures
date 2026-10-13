/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Resolution representatives for a Cech cup cocycle

Source: Stacks Project, Tag 0FKV, specialized to sheaves in degree zero.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Two Cech cocycles and their cup admit compatible representatives in a computing
resolution pairing. This statement concerns the pairing of actual resolution
sections, before any sheaf or Cech cup product on cohomology is chosen.
Source: Stacks Project, Tag 0FKV, proof of Lemma 20.31.4, and Tag 07MB
(blueprint: lem-sc-cech-cup-resolution-representatives).

Proof: use Godement resolutions of F, G and F tensor G with their natural
sectionwise pairing. These are nonnegative flasque resolutions; compare them to
injective resolutions to obtain a CupResolutionPairing D. The Cech-to-total beta
maps carry a, b and c to cocycles. The global-sections-to-total alpha maps are
quasi-isomorphisms for these flasque resolutions, so choose global cocycles a'
and b' representing the two images under inverse alpha on homology. Leibniz
makes D.pair p q top a'.val b'.val a cocycle c'. In the signed total Cech
pairing, alpha preserves the pairing. The augmentation preserves the tensor of
sections, hence beta preserves the Cech cup pairing. Tag 0FKV's commuting diagram
therefore identifies the class of c' with the canonical image of c. The classes
of a' and b' are likewise the canonical images of a and b. Comparison with
injective resolutions identifies these classes with D.left.class,
D.right.class and D.target.class and with the specified canonical comparisons.
Degree zero uses the augmentation pairing; vanishing classes or an empty scheme
cause no exception, since cycles representing zero can be chosen to be zero. -/
theorem cechCup_resolution_representatives (X : Scheme.{v}) {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor U).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison U G q cG)
    (cFG : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcFG : IsModuleCechComparison U (F ⊗ G) (p + q) cFG)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    ∃ (D : CupResolutionPairing F G)
      (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
      (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
      (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
      D.left.class p a' = cF (cupCycleClass _ p a) ∧
      D.right.class q b' = cG (cupCycleClass _ q b) ∧
      D.target.class (p + q) c' = cFG (cupCycleClass _ (p + q) c) ∧
      c'.val = D.pair p q ⊤ a'.val b'.val := by sorry

end
end AlgebraicGeometry.Scheme.Modules
