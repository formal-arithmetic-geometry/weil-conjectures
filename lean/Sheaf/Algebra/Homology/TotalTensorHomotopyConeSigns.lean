/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Signed tensor homotopies and mapping cones

Source: Stacks Project, Tags 06YM, 06YP, 0G6E, 0FNH and 0GWR;
derived.tex, definition-cone and definition-distinguished-triangle.
(blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex HomologicalComplex

namespace SheafOfModules.TotalTensorSigns

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The existing category of module sheaves. Source: Stacks, Modules on Sites, Section 03DA
(blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing sheafified balanced tensor. Source: Stacks, Tag 03EK
(blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
abbrev tensor := curriedTensor (Modules R)

/-- The direct-sum total tensor bifunctor, with differential d tensor 1 + (-1)^p 1 tensor d.
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
abbrev total := (tensor R).map₂CochainComplex

/-- The same bifunctor modulo homotopies, with the inherited coherent integer shifts.
Source: Stacks, Tag 06YM (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
abbrev homotopyTensor := (tensor R).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)

/-- The canonical signed comparison A tensor Cone(u) to Cone(A tensor u).
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def coneLeft (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) :
    ((total R).obj A).obj (mappingCone f) ≅ mappingCone (((total R).obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₂Iso A f (tensor R)

/-- The canonical unsigned comparison Cone(u) tensor A to Cone(u tensor A).
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def coneRight (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) :
    ((total R).flip.obj A).obj (mappingCone f) ≅
      mappingCone (((total R).flip.obj A).map f) :=
  CochainComplex.mapBifunctorMappingCone₁Iso f A (tensor R)

/-- The existing signed total flip after the presheaf-induced sheaf symmetry, without
requesting the unused associativity data of the monoidal structure on all complexes.
Source: Stacks, Tag 0GWR (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def swap (B A : CochainComplex (Modules R) ℤ) :
    ((total R).obj B).obj A ≅ ((total R).obj A).obj B :=
  HomologicalComplex₂.total.mapIso (CochainComplex.Monoidal.braidingBicomplexIso B A)
    (.up ℤ) ≪≫ HomologicalComplex.mapBifunctorFlipIso A B (tensor R) (.up ℤ)

/-- The existing inclusion of a total-tensor summand, with its endpoint type exposed.
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def ι (A B : CochainComplex (Modules R) ℤ) (p q n : ℤ) (hpq : p + q = n) :
    A.X p ⊗ B.X q ⟶ (((total R).obj A).obj B).X n :=
  CochainComplex.ιMapBifunctor A B (tensor R) p q n hpq

/-- The existing second-variable tensor homotopy, with its endpoints exposed.
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def homotopyLeft (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (((total R).obj A).map f) (((total R).obj A).map g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 A) h (tensor R) (.up ℤ)

/-- The existing first-variable tensor homotopy, with its endpoints exposed.
Source: Stacks, Tag 0G6E (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def homotopyRight (A : CochainComplex (Modules R) ℤ)
    {X Y : CochainComplex (Modules R) ℤ} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (((total R).flip.obj A).map f) (((total R).flip.obj A).map g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 A) (tensor R) (.up ℤ)

/-- The existing coherent second-factor shift, with its endpoints exposed.
Source: Stacks, Tag 0FNH (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def shiftLeft (A X : CochainComplex (Modules R) ℤ) (n : ℤ) :
    ((total R).obj A).obj (X⟦n⟧) ≅ (((total R).obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₂Iso A X (tensor R) n

/-- The existing coherent first-factor shift, with its endpoints exposed.
Source: Stacks, Tag 0FNH (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs). -/
def shiftRight (A X : CochainComplex (Modules R) ℤ) (n : ℤ) :
    ((total R).flip.obj A).obj (X⟦n⟧) ≅ (((total R).flip.obj A).obj X)⟦n⟧ :=
  CochainComplex.mapBifunctorShift₁Iso X A (tensor R) n

/-- The signed homotopy, cone and interchange formulas for total sheaf tensor, its exactness
on K(R), preservation of arbitrary quasi-isomorphisms by K-flat factors, and shift stability.
The two cone isomorphisms and the swap below are existing canonical constructions, so their
existence, inverses and chain identities are included in their types. The inr equations
specify the identity on the target summands, and the inl equations specify the source
summands. In the projection equations, the negative of triangle.mor₃ is p; triangle.mor₃
itself is -p. All sheaf tensor maps used here are the localization tensor maps induced by
balanced presheaf tensor maps, rather than arbitrary maps on the associated sheaves.

Source: Stacks Project, sites-cohomology.tex, Tags 06YM and 06YP; derived.tex,
definition-cone, definition-distinguished-triangle and Tag 0G6E; more-algebra.tex,
Tags 0FNH and 0GWR (blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs).

Proof (the node's eleven steps):
1. In Mod(R), tensor is additive in both variables by lem-pc-sheaf-modules-tensor-closed.
   Tensoring the binary biproduct identities gives the distributions over cone summands.
   All component maps are balanced and restriction compatible; the universal property of
   def-weil-presheaf-modules-sheafification descends them and their identities to sheaves.
   Specify the total maps on summands, using def-pc-tensor-complex-sheaves.
2. For h:u~v, take (-1)^p 1 tensor h on A^p tensor X^q. Expanding dk+kd gives mixed
   coefficients (-1)^p and (-1)^(p+1), which cancel, leaving 1 tensor (u-v).
3. For X tensor A, take h tensor 1. Its mixed coefficients (-1)^(i-1) and (-1)^i
   cancel, leaving (u-v) tensor 1. These homotopies give additive quotient functors
   on the homotopy category of lem-pur-homotopy-category-triangulated.
4. Use s²_n and s¹_n of lem-weil-pbc-total-tensor-integer-shifts; their zero, addition
   and naturality equations pass to homotopy classes.
5. On A tensor Cone(u), use identity on Y and (-1)^p on the X[1] summand. Its cone
   differential has Y component (-1)^p a tensor ux and X components
   (-1)^(p+1) da tensor x - a tensor dx. Both orders of applying the differential
   and comparison give these expressions. The same signs give the inverse.
6. For Cone(u) tensor A, distribution is unsigned. On x in X^(i+1), both differentials
   give ux tensor a and -dx tensor a + (-1)^i x tensor da.
7. Cone maps from commuting squares are diagonal, so these comparisons are natural.
   Inclusions are unchanged. On source summands the projection signs are (-1)^p and
   1, precisely s²_1 and s¹_1. Negating gives compatibility with the third arrow -p.
8. Every distinguished triangle is isomorphic to a cone triangle. Identity on the
   first two vertices and the cone comparison on the third identify its tensor image
   with the cone triangle of the tensor map. Hence both quotient functors are exact
   in the sense of def-weil-triangulated-category.
9. Swap b in B^i and a in A^j with (-1)^(ij). The two differential coefficients are
   (-1)^(ij+j) and (-1)^(ij) in either order. Swapping twice gives (-1)^(2ij)=1.
   Degree-zero maps preserve the bidegrees, giving naturality.
10. By lem-pur-quasi-iso-cone-acyclic, any quasi-isomorphism has acyclic cone.
    For K-flat A, tensoring this cone on the right preserves acyclicity. The cone
    comparison and the same criterion prove the tensor map a quasi-isomorphism.
    Conjugate by the signed swap for tensoring on the left. Endpoints are arbitrary.
11. The second shift comparison identifies F tensor A[n] with (F tensor A)[n].
    Shifts preserve acyclicity, proving K-flat stability. Separately, every term
    (A[n])^i is A^(i+n), proving flat-term stability without an unbounded-flat
    implies K-flat assertion. No boundedness or flat-cohomology assumption is used.
-/
theorem totalTensorHomotopyConeSigns :
    (∀ A : CochainComplex (Modules R) ℤ,
      ((total R).obj A).Additive ∧ ((total R).flip.obj A).Additive ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).Additive ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).Additive) ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated) ∧
      (NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ ∧
        NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyFlipObjIso
          (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f g : X ⟶ Y) (h : Homotopy f g)
        (p q n : ℤ) (hpq : p + q = n),
      (ι R A X p q n hpq ≫
        (homotopyLeft R A h).hom n (n - 1) =
        p.negOnePow • (A.X p ◁ h.hom q (q - 1) ≫
          ι R A Y p (q - 1) (n - 1) (by omega))) ∧
      (ι R X A q p n (by omega) ≫
        (homotopyRight R A h).hom n (n - 1) =
        h.hom q (q - 1) ▷ A.X p ≫
          ι R Y A (q - 1) p (n - 1) (by omega))) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
      (((total R).obj A).map (mappingCone.inr f) ≫ (coneLeft R A f).hom =
        mappingCone.inr (((total R).obj A).map f)) ∧
      (((total R).flip.obj A).map (mappingCone.inr f) ≫ (coneRight R A f).hom =
        mappingCone.inr (((total R).flip.obj A).map f)) ∧
      (∀ (p q n : ℤ) (hpq : p + q = n),
        (A.X p ◁ (mappingCone.inl f).v (q + 1) q (by omega) ≫
            ι R A (mappingCone f) p q n hpq ≫
            (coneLeft R A f).hom.f n =
          p.negOnePow • (ι R A X
            p (q + 1) (n + 1) (by omega) ≫
              (mappingCone.inl (((total R).obj A).map f)).v (n + 1) n (by omega))) ∧
        ((mappingCone.inl f).v (q + 1) q (by omega) ▷ A.X p ≫
            ι R (mappingCone f) A q p n (by omega) ≫
            (coneRight R A f).hom.f n =
          ι R X A (q + 1) p (n + 1) (by omega) ≫
            (mappingCone.inl (((total R).flip.obj A).map f)).v (n + 1) n (by omega))) ∧
      ((coneLeft R A f).hom ≫ (-(mappingCone.triangle (((total R).obj A).map f)).mor₃) =
        ((total R).obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (-(mappingCone.triangle (((total R).flip.obj A).map f)).mor₃) =
        ((total R).flip.obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftRight R A X 1).hom) ∧
      ((coneLeft R A f).hom ≫ (mappingCone.triangle (((total R).obj A).map f)).mor₃ =
        ((total R).obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (mappingCone.triangle (((total R).flip.obj A).map f)).mor₃ =
        ((total R).flip.obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftRight R A X 1).hom)) ∧
    (∀ (A X Y X' Y' : CochainComplex (Modules R) ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y')
        (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f'),
      (((total R).obj A).map (mappingCone.map f f' a b comm) ≫ (coneLeft R A f').hom =
        (coneLeft R A f).hom ≫ mappingCone.map (((total R).obj A).map f) (((total R).obj A).map f')
          (((total R).obj A).map a) (((total R).obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp])) ∧
      (((total R).flip.obj A).map (mappingCone.map f f' a b comm) ≫ (coneRight R A f').hom =
        (coneRight R A f).hom ≫
          mappingCone.map (((total R).flip.obj A).map f) (((total R).flip.obj A).map f')
          (((total R).flip.obj A).map a) (((total R).flip.obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp]))) ∧
    (∀ (A B : CochainComplex (Modules R) ℤ),
      (swap R B A).inv = (swap R A B).hom ∧
      ∀ (i j n : ℤ) (hij : i + j = n),
        ι R B A i j n hij ≫
            (swap R B A).hom.f n =
          (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
            ι R A B j i n (by omega))) ∧
    (∀ (A A' B B' : CochainComplex (Modules R) ℤ) (a : A ⟶ A') (b : B ⟶ B'),
      HomologicalComplex.mapBifunctorMap b a (tensor R) (.up ℤ) ≫
          (swap R B' A').hom =
        (swap R B A).hom ≫
          HomologicalComplex.mapBifunctorMap a b (tensor R) (.up ℤ)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients A →
        (∀ (X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
          QuasiIso f → QuasiIso (((total R).obj A).map f) ∧
            QuasiIso (((total R).flip.obj A).map f)) ∧
        ∀ n : ℤ, CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X i)) →
        ∀ n i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((A⟦n⟧).X i)) := by
  sorry

end SheafOfModules.TotalTensorSigns
