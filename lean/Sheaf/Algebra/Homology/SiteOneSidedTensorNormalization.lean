/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normalized one-sided K-flat tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YU (definition-derived-tor),
the construction preceding the definition and the signed symmetry following it.
(blueprint: lem-trf-site-one-sided-tensor-normalization)

The parameters `P`, `B`, `D` and `δ` unpack the resolving subcategory, homotopy tensor,
derived tensor and specified two-sided comparison of site-derived-tensor descent.
They are supplied as data, so the normalization retains the specified comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

/-- The normalized one-sided comparison, in both tensor orders, with uniqueness among
all families natural in the unrestricted argument. The last equations express naturality
in every homotopy-category map of the fixed K-flat argument. `NatIso` includes the first
naturality equation for every map, in particular every flat-term K-flat resolution.
The final conjunct records the signed chain interchange on every direct-sum summand.

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP, 06YS and the construction
preceding Tag 06YU (definition-derived-tor); Categories, Tag 04VK.
(blueprint: lem-trf-site-one-sided-tensor-normalization)

Proof:
1. Tensor homotopies are h tensor 1 and (-1)^i 1 tensor h; their cross terms cancel.
   The signed interchange (-1)^(ij) commutes with the differential and squares to one.
   Balanced maps descend to sheafification, summandwise even for unbounded totals.
2. For a quasi-isomorphism f its cone is acyclic (lem-pur-quasi-iso-cone-acyclic).
   K-flatness kills tensor of that cone. Signed interchange and the tensor-cone
   isomorphism (lem-pc-tensor-mapping-cone-iso) imply that both tensor maps are
   quasi-isomorphisms. Every homotopy arrow has a chain representative.
3. By lem-weil-pbc-site-derived-tensor-descent, Q restricted to P is a localization.
   Fix T. The functor H(M)=Q Tot(T tensor M) inverts quasi-isomorphisms by step 2.
   Extend H along Q using clause (1) of lem-weil-pbc-localization-universal-property,
   obtaining Hbar and phi:Hbar Q ≅ H.
4. On P, phi inverse followed by delta inverse gives a natural isomorphism from
   D(QT,-) to Hbar. Extend it and its inverse by clause (2) of that universal
   property. Uniqueness makes the extensions inverse. Compose with phi to get c.
   At V in P the two phi factors cancel, so c(T,V)=delta(T,V) inverse.
5. For every M choose a flat-term K-flat quasi-isomorphism r:V→M by
   lem-pc-kflat-resolution. Naturality forces c(T,M) to be Q(1 tensor r), after
   delta(T,V) inverse, after D(1,Qr) inverse. Both outside maps are invertible.
   Thus every normalized natural family equals c, independently of all choices.
6. For any g:T→T', compare Q(g tensor 1)c(T,-) and c(T',-)D(Qg,1).
   They agree on P by naturality of delta. Naturality at r:V→M and cancellation
   of the invertible D(1,Qr) extends equality to every M, without inverting g.
7. Repeat steps 3–6 with H(M)=Q Tot(M tensor T), normalized by delta(V,T) inverse.
   Naturality at r gives the analogous formula with Q(r tensor 1) and D(Qr,1).
   This proves uniqueness and naturality in both arguments in the reversed order.
   No flatness or boundedness of the arbitrary argument is used.
-/
theorem site_one_sided_tensor_normalization
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Modules R)]
    (P : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)))
    (hP : ∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (X.as.X n))
    (B : HomotopyCategory (Modules R) (.up ℤ) ⥤
      HomotopyCategory (Modules R) (.up ℤ) ⥤ HomotopyCategory (Modules R) (.up ℤ))
    (hB : Nonempty (((HomotopyCategory.quotient (Modules R) (.up ℤ)).prod
        (HomotopyCategory.quotient (Modules R) (.up ℤ))) ⋙ Functor.uncurry.obj B ≅
      Functor.uncurry.obj (totalTensor R) ⋙ HomotopyCategory.quotient (Modules R) (.up ℤ)))
    (D : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (δ : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj B ⋙ DerivedCategory.Qh ≅
      ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ Functor.uncurry.obj D) :
    (∀ (T : P.FullSubcategory)
      (M M' : HomotopyCategory (Modules R) (.up ℤ)) (f : M ⟶ M'),
      HomotopyCategory.quasiIso (Modules R) (.up ℤ) f →
        HomotopyCategory.quasiIso (Modules R) (.up ℤ) ((B.obj T.obj).map f) ∧
        HomotopyCategory.quasiIso (Modules R) (.up ℤ) ((B.flip.obj T.obj).map f)) ∧
    (∃ c : ∀ T : P.FullSubcategory,
        DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.obj T.obj ⋙ DerivedCategory.Qh,
      (∀ T V : P.FullSubcategory, (c T).app V.obj = (δ.app (T, V)).symm) ∧
      (∀ c' : ∀ T : P.FullSubcategory,
          DerivedCategory.Qh ⋙ D.obj (DerivedCategory.Qh.obj T.obj) ≅
            B.obj T.obj ⋙ DerivedCategory.Qh,
        (∀ T V : P.FullSubcategory, (c' T).app V.obj = (δ.app (T, V)).symm) → c' = c) ∧
      (∀ (T T' : P.FullSubcategory) (g : T ⟶ T')
        (M : HomotopyCategory (Modules R) (.up ℤ)),
        (c T).hom.app M ≫ DerivedCategory.Qh.map ((B.map g.hom).app M) =
          (D.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj M) ≫
            (c T').hom.app M)) ∧
    (∃ c : ∀ T : P.FullSubcategory,
        DerivedCategory.Qh ⋙ D.flip.obj (DerivedCategory.Qh.obj T.obj) ≅
          B.flip.obj T.obj ⋙ DerivedCategory.Qh,
      (∀ T V : P.FullSubcategory, (c T).app V.obj = (δ.app (V, T)).symm) ∧
      (∀ c' : ∀ T : P.FullSubcategory,
          DerivedCategory.Qh ⋙ D.flip.obj (DerivedCategory.Qh.obj T.obj) ≅
            B.flip.obj T.obj ⋙ DerivedCategory.Qh,
        (∀ T V : P.FullSubcategory, (c' T).app V.obj = (δ.app (V, T)).symm) → c' = c) ∧
      (∀ (T T' : P.FullSubcategory) (g : T ⟶ T')
        (M : HomotopyCategory (Modules R) (.up ℤ)),
        (c T).hom.app M ≫ DerivedCategory.Qh.map ((B.flip.map g.hom).app M) =
          (D.flip.map (DerivedCategory.Qh.map g.hom)).app (DerivedCategory.Qh.obj M) ≫
            (c T').hom.app M)) ∧
    (∀ (K L : CochainComplex (Modules R) ℤ) (i j n : ℤ) (h : i + j = n),
      HomologicalComplex.ιTensorObj K L i j n h ≫
          (CochainComplex.Monoidal.braiding K L).hom.f n =
        ((i * j).negOnePow : ℤ) • ((β_ (K.X i) (L.X j)).hom ≫
          HomologicalComplex.ιTensorObj L K j i n (add_comm j i |>.trans h))) := by
  sorry

end SheafOfModules
