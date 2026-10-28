/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel


/-! Models used in the global derived Hom and inverse-limit comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

/-- A-linear K-injective representatives and all cohomology groups of global RHom.

Source: Stacks Project, sites-cohomology.tex, Tags 0B6E and 08JA, and Tag 0A96.
(blueprint: lem-sfb-global-rhom-coefficient-model).

Proof: Choose a K-flat resolution P of L. The internal-Hom sections model identifies
RHom(E,QI) with ordinary global Hom(P,I) for K-injective I: Hom(P,I) is K-injective,
so the unit of the right derived sections functor is invertible. Precomposition with
P → L is a quasi-isomorphism on both sheaf Hom and global Hom complexes, because I
is K-injective. Invert this map and transport along eL to obtain β for the arbitrary
representative L. All chain maps preserve the section-ring action, and restriction
along φ preserves the comparisons. Thus the comparison is in D(A), and naturality
of the derived unit and precomposition gives the displayed naturality in I.
For N take a K-injective representative I. The cohomology of the global Hom complex
is the group of homotopy classes L → I[q]. K-injectivity identifies this with
Hom(E,N[q]). Postcomposition gives naturality in N, and multiplication by φ(b) on
the target gives the scalar equation. The formulas hold in every integer degree,
including negative degrees, and for zero complexes, the empty site and the zero ring. -/
theorem coefficient_model
    (E : DerivedCategory (Modules.{c, v, max c v r} R))
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    (eL : DerivedCategory.Q.obj L ≅ E) :
    ∃ β : ∀ (I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (_hI : I.IsKInjective),
        DerivedCategory.Q.obj ((representative.{c, v, r, a} R A φ L).obj I) ≅
          (globalHom.{c, v, r, a, w, z} R A φ E).obj (DerivedCategory.Q.obj I),
      (∀ (I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (hI : I.IsKInjective)
        (hI' : I'.IsKInjective) (f : I ⟶ I'),
        DerivedCategory.Q.map ((representative.{c, v, r, a} R A φ L).map f) ≫ (β I' hI').hom =
          (β I hI).hom ≫ (globalHom.{c, v, r, a, w, z} R A φ E).map (DerivedCategory.Q.map f)) ∧
      ∃ e : ∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ),
          ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)) ≃+ (E ⟶ N⟦q⟧),
        (∀ (N N' : DerivedCategory (Modules.{c, v, max c v r} R)) (f : N ⟶ N') (q : ℤ)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N' q ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).map
            ((globalHom.{c, v, r, a, w, z} R A φ E).map f) x) = e N q x ≫ f⟦q⟧') ∧
        (∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ) (b : A)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N q (b • x) = (φ b) • e N q x) := by sorry

end CategoryTheory.RingedSiteGlobalRHom
