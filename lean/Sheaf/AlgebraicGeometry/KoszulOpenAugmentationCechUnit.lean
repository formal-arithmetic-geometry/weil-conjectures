/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenHomChainRepresentatives
public import Sheaf.AlgebraicGeometry.KoszulOpenSectionsUnit

/-! # The ordinary augmented Koszul cycle is the Cech unit

Source: Stacks Project, Tag 08D1, the signed fraction formula.
(blueprint: lem-sc-koszul-open-augmentation-cech-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The augmentation cycle and restriction of one have the same ordinary Cech class.
Source: Stacks Project, Tag 08D1, proof, the isomorphisms psi^{p,q} and the sign
(-1)^(pq+p(p-1)/2); Tag 08D0, singleton fraction formula.
(blueprint: lem-sc-koszul-open-augmentation-cech-unit).

Proof: Transpose the exponent-one augmentation through the tilde/sections
adjunction. On each singleton wedge e_j it gives f_j times the global unit.
The structure complex is zero outside degree zero. Consequently its degree-zero
Cech component can be nonzero only on singletons, where p=q=0 and the totalization
sign is +1. By the defining koszulCechCocone fraction equation, its value there
multiplied by f_j equals restriction of f_j. Multiplication by f_j is invertible
on D(f_j), so its value is restriction of one. For larger subsets the target
coefficient degree 1-card(J) is nonzero, and its sections module is zero. Thus
this cycle equals the Cech augmentation of the ordinary sections cycle of one.
The ordinary class openStructureUnitClass is represented by that same cycle:
extendHomologyIso and singleObjHomologySelfIso send 1 to its degree-zero unit,
and the termwise tilde.toOpen map restricts it to the chosen open. The naturality
of the short-complex cycles iso and homology projection sends these equal cycles
to the equality below. For r=0 the target Cech complex is zero; zero f_j and the
zero ring cause zero localization modules, so cancellation remains valid.
This is entirely a calculation of ordinary complex homology: no localization
of categories, derived functor, evaluation equivalence or inverse augmentation
is asserted. -/
theorem koszulOpen_augmentation_cech_unit
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) :
    let C := openStructureSheafComplex A
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj C
    let t := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (koszulOpenAugmentation A r f 0)
        ComplexShape.embeddingDownNat)
    let k := (koszulCechHomObjIso A r f M 0).inv ≫
      colimit.ι (koszulCechHomDiagram A r f M) 0 ≫ koszulCechComparison A r f C
    HomologicalComplex.homologyMap k 0
        (koszulHomChainClass (koszulOpenHomTranspose A r f C 0 t)) =
      HomologicalComplex.homologyMap ((principalCechAugmentation r f).app C) 0
        (openStructureUnitClass A (koszulOpen A r f)) := by sorry

end AlgebraicGeometry
