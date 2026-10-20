/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition

/-! # Scalar cohomology pullback along a commutative square

Source: Stacks Project, Tags 0097 and 01FD.
(blueprint: lem-sc-scalar-cohomology-pullback-square).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem scalarMap_comp {k : Type w} [Field k] {A : Scheme.{w}}
    (f : A ⟶ Spec (CommRingCat.of k)) {F G H : SheafOfModules.{w} A.ringCatSheaf}
    (a : F ⟶ G) (b : G ⟶ H) (n : ℕ) (x : scalarCohomology f F n) :
    scalarCohomologyMap f (a ≫ b) n x =
      scalarCohomologyMap f b n (scalarCohomologyMap f a n x) := by
  unfold scalarCohomologyMap
  rw [Functor.map_comp, Functor.map_comp]
  rfl

private theorem scalarMap_id {k : Type w} [Field k] {A : Scheme.{w}}
    (f : A ⟶ Spec (CommRingCat.of k)) (F : SheafOfModules.{w} A.ringCatSheaf)
    (n : ℕ) (x : scalarCohomology f F n) :
    scalarCohomologyMap f (𝟙 F) n x = x := by
  unfold scalarCohomologyMap
  simp only [CategoryTheory.Functor.map_id]
  rfl

private theorem scalarMap_eq_pullback {k : Type w} [Field k] {A D : Scheme.{w}}
    (fA : A ⟶ Spec (CommRingCat.of k)) (fD : D ⟶ Spec (CommRingCat.of k))
    (t t' : A ⟶ D) (ht : t ≫ fD = fA) (ht' : t' ≫ fD = fA) (h : t = t')
    (F : D.Modules) (n : ℕ) (x : scalarCohomology fD F n) :
    scalarCohomologyMap fA
      (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj F) h)).hom n
      (scalarCohomologyPullback fD fA t ht F n x) =
        scalarCohomologyPullback fD fA t' ht' F n x := by
  subst t'
  exact scalarMap_id (A := A) fA _ n _

private theorem scalarMap_three_iso {k : Type w} [Field k] {A : Scheme.{w}}
    (fA : A ⟶ Spec (CommRingCat.of k)) {P Q R S : A.Modules}
    (i : Q ≅ P) (j : Q ≅ R) (e : R ≅ S) (n : ℕ)
    (z : scalarCohomology fA P n) (y : scalarCohomology fA S n)
    (z0 : scalarCohomology fA Q n) (z1 : scalarCohomology fA R n)
    (hi : scalarCohomologyMap fA i.inv n z = z0)
    (hj : scalarCohomologyMap fA j.hom n z0 = z1)
    (he : scalarCohomologyMap fA e.inv n y = z1) :
    scalarCohomologyMap fA (i.symm ≪≫ j ≪≫ e).hom n z = y := by
  have cancel : scalarCohomologyMap fA e.hom n
      (scalarCohomologyMap fA e.inv n y) = y :=
    (scalarMap_comp (A := A) fA e.inv e.hom n y).symm.trans
      ((congrArg (fun q ↦ scalarCohomologyMap fA q n y) e.inv_hom_id).trans
        (scalarMap_id (A := A) fA _ n y))
  calc
    scalarCohomologyMap fA (i.symm ≪≫ j ≪≫ e).hom n z =
        scalarCohomologyMap fA (j.hom ≫ e.hom) n
          (scalarCohomologyMap fA i.inv n z) :=
      scalarMap_comp (A := A) fA i.inv (j.hom ≫ e.hom) n z
    _ = scalarCohomologyMap fA e.hom n
        (scalarCohomologyMap fA j.hom n (scalarCohomologyMap fA i.inv n z)) :=
      scalarMap_comp (A := A) fA j.hom e.hom n _
    _ = scalarCohomologyMap fA e.hom n z1 :=
      congrArg (scalarCohomologyMap fA e.hom n)
        ((congrArg (scalarCohomologyMap fA j.hom n) hi).trans hj)
    _ = scalarCohomologyMap fA e.hom n (scalarCohomologyMap fA e.inv n y) :=
      congrArg (scalarCohomologyMap fA e.hom n) he.symm
    _ = y := cancel

/-- Two successive scalar pullbacks agree around a commutative square, after
the normalized composition comparison on their coefficient modules.
Source: Stacks Project, Tags 0097 and 01FD; Step 8 of lem-sc-picard-kunneth-qcoh (Tag 0BED).
(blueprint: lem-sc-scalar-cohomology-pullback-square).

Proof: The comparison of Tag 0097 is the unique isomorphism of left adjoints
intertwining their units. The definition scalarPullbackCompIso uses precisely this
isomorphism for the normalized tensor-pullback adjunctions. Consequently its
inverse identifies the successive unit with the unit of the composite morphism.
Apply this on both paths a then b, and c then d. The equality h identifies the two
composites; scalarPullbackSquareIso is the first inverse comparison followed by
this equality and the second comparison. Thus it intertwines the two composite
coefficient maps. The resolution construction of cohomology pullback in Tag 01FD
respects successive coefficient maps: compose the resolution lifts over the units;
any two such lifts are homotopic, so their maps on cohomology agree. The natural
injective-resolution comparison to Ext used by scalarCohomologyExtEquiv transports
these maps to scalarCohomologyPullback, whose inverse-image coefficient is adjoint
to the same normalized unit. Transporting the square equality back identifies its
coefficient change with scalarCohomologyMap. Proof irrelevance removes dependence
on the chosen proofs ha, hb, hc, hd and h. Identity morphisms give the unit
comparison, degree zero gives composition of section pullbacks, and zero modules
or empty schemes give zero maps. No quasi-coherence or compactness is needed.
-/
theorem scalarCohomologyPullback_square
    (k : Type w) [Field k] (A B C D : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k)) (fD : D ⟶ Spec (CommRingCat.of k))
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (ha : a ≫ fB = fA) (hb : b ≫ fD = fB)
    (hc : c ≫ fC = fA) (hd : d ≫ fD = fC) (h : a ≫ b = c ≫ d)
    (F : D.Modules) (n : ℕ) (x : scalarCohomology fD F n) :
    scalarCohomologyMap fA (scalarPullbackSquareIso a b c d h F).hom n
        (scalarCohomologyPullback fB fA a ha ((tensorPullback b).obj F) n
          (scalarCohomologyPullback fD fB b hb F n x)) =
      scalarCohomologyPullback fC fA c hc ((tensorPullback d).obj F) n
        (scalarCohomologyPullback fD fC d hd F n x) := by
  have hab := scalarCohomologyPullback_comp k A B D fA fB fD a b ha hb F n x
  have hcd := scalarCohomologyPullback_comp k A C D fA fC fD c d hc hd F n x
  have heq := scalarMap_eq_pullback (A := A) (D := D) fA fD (a ≫ b) (c ≫ d)
    (by rw [Category.assoc, hb, ha]) (by rw [Category.assoc, hd, hc]) h F n x
  exact scalarMap_three_iso (A := A) fA
    ((scalarPullbackCompIso a b).app F)
    (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj F) h))
    ((scalarPullbackCompIso c d).app F) n _ _ _ _ hab heq hcd

end
end AlgebraicGeometry.Scheme.Modules
