/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.RingTheory.ColimitCategoryFpAlgebras
import WeilConjectures.RingTheory.ColimitFlatRingMap

/-! # A henselian flat group model with a specified split closed fibre

Source: Stacks Project, More on Algebra, Tag 0A41, and Limits, Tag 04AI;
finite Hopf diagram and residue-isomorphism refinement
(blueprint: lem-sfb-henselian-flat-group-split-fibre-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finitely presented flat affine group over a henselian local ring descends to a
henselian local Noetherian G-ring, retaining a specified diagonalizable closed fibre.
Source: Stacks Project, More on Algebra, Tag 0A41; Algebra, Tags 05N9 and 02JO;
Limits, Tag 04AI (blueprint: lem-sfb-henselian-flat-group-split-fibre-model).

The final equality is written after projection to Spec B. Its left side is the given
closed-fibre isomorphism followed by the inverse model isomorphism and projection; its
right side is the descended isomorphism after the canonical coefficient map on group
algebras. The other projection is fixed by the structure maps, so the pullback universal
property says precisely that the scalar extension of a_A followed by b_k is a.

Proof:
1. By lem-sfb-henselian-local-g-ring-colimit (Tag 0A41), express C as a filtered colimit
of henselian local Noetherian G-rings with local transition and cocone maps. Their residue
fields have colimit k: representatives descend, and equality of residues is detected at a
common stage because locality contracts the maximal ideal exactly.
2. Use lem-weil-pbc-lfp-affine-opens-finite-presentation and
lem-weil-pbc-flat-morphism-affine-criterion to write H = Spec E with E finitely presented
and flat over C. Descend E by lem-kun-fp-algebra-descent. The affine-spectrum and affine
fibre-product interfaces def-weil-affine-spectrum and lem-weil-pbc-fibre-product-affine-spectra
translate the group operations into coproduct, counit and antipode maps.
3. Tensor squares and cubes have finite polynomial presentations by
lem-weil-pbc-algebra-tensor-pushout-universal-property. Descend the three operation maps
and their finitely many group equations by lem-weil-pbc-colimit-category-fp-algebras,
Tag 05N9(2),(3). They give a group structure and the model group isomorphism b.
4. Apply lem-weil-pbc-colimit-flat-ring-map, Tag 02JO(3), to make the model algebra flat
at a later stage. Carry all the group data along by scalar extension.
5. By lem-sfb-subgroup-algebra-coset-presentation with L = 0, the group algebra is finitely
presented, including for torsion M. Apply Tag 05N9 over the residue-field colimit to descend
the specified a and its inverse, their inverse equations and their compatibility with all
Hopf operations. The factorization equality retains this particular a.
6. Take that stage as A and B. Step 1 supplies all ring and locality conditions, steps 2--4
supply the flat finitely presented group model and b, and step 5 supplies a_A and the
compatibility equality. No injectivity of A → C or other fibre condition is used. -/
theorem exists_henselian_flat_group_split_fibre_model
    (C : Type u) [CommRing C] [HenselianLocalRing C]
    (H : Grp (Over (Spec (.of C))))
    [IsAffineHom H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (a : ringDiagonalizableGroup (IsLocalRing.ResidueField C) M ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue C)))).mapGrp.obj H) :
    ∃ (A : CommRingCat.{u}) (_ : HenselianLocalRing A), IsGRing A ∧
      ∃ (u : A →+* C) (_ : IsLocalHom u) (B : CommRingCat.{u}) (_ : Algebra A B),
        Algebra.FinitePresentation A B ∧ Module.Flat A B ∧
        ∃ (_ : GrpObj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))),
          ∃ (b : (Over.pullback (Spec.map (CommRingCat.ofHom u))).mapGrp.obj
              (Grp.mk (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))) ≅ H)
            (aA : ringDiagonalizableGroup (IsLocalRing.ResidueField A) M ≅
              (Over.pullback
                (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.obj
                (Grp.mk (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))))),
            a.hom.hom.hom.left ≫
                pullback.fst H.X.hom
                  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue C))) ≫
                b.inv.hom.hom.left ≫
                pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
                  (Spec.map (CommRingCat.ofHom u)) =
              Spec.map (CommRingCat.ofHom
                  (AddMonoidAlgebra.mapRingHom M (IsLocalRing.ResidueField.map u))) ≫
                aA.hom.hom.hom.left ≫
                pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
                  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
  sorry

end AlgebraicGeometry
