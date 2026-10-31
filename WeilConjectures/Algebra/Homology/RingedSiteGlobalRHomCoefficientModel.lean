/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomCoefficientComparison
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomRepresentativeCohomology
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomDescent

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

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

section Lifting
variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

private theorem exists_chainMap
    {L I : CochainComplex D ℤ} [I.IsKInjective]
    (f : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj I) :
    ∃ g : L ⟶ I, DerivedCategory.Q.map g = f := by
  let q := HomotopyCategory.quotient D (.up ℤ)
  let α := DerivedCategory.quotientCompQhIso D
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) I).surjective
    (α.hom.app L ≫ f ≫ α.inv.app I)
  obtain ⟨g, hg⟩ := q.map_surjective a
  refine ⟨g, ?_⟩
  have hn := α.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [hg, ha] at hn
  apply (cancel_epi (α.hom.app L)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm

private theorem injectives_full
    (P : ObjectProperty (CochainComplex D ℤ))
    (hP : ∀ I, P I → I.IsKInjective) : (P.ι ⋙ DerivedCategory.Q).Full where
  map_surjective := by
    intro L I f
    have : (P.ι.obj I).IsKInjective := hP I.obj I.property
    obtain ⟨g, hg⟩ := exists_chainMap f
    exact ⟨ObjectProperty.homMk g, hg⟩

private theorem injectives_essSurj
    [Abelian.HasKInjectiveResolutions D]
    (P : ObjectProperty (CochainComplex D ℤ))
    (hP : ∀ I, I.IsKInjective → P I) : (P.ι ⋙ DerivedCategory.Q).EssSurj where
  mem_essImage X := by
    obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage X)
    have := hi
    exact ⟨⟨I, hP I hI⟩,
      ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

end Lifting

private def globalHomSourceIso
    {E E' : DerivedCategory (Modules.{c, v, max c v r} R)} (e : E ≅ E') :
    globalHom.{c, v, r, a, w, z} R A φ E ≅ globalHom.{c, v, r, a, w, z} R A φ E' := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact Functor.isoWhiskerRight
    ((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso e.symm.op)
    (sections.{c, v, max c v r} R A φ).rightDerivedFunctor

private def coefficientComparisonAt
    (E : DerivedCategory (Modules.{c, v, max c v r} R))
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    (eL : DerivedCategory.Q.obj L ≅ E) :
    (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙
        representative.{c, v, r, a} R A φ L ⋙ DerivedCategory.Q ≅
      (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q.{w} ⋙
        globalHom.{c, v, r, a, w, z} R A φ E := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact Classical.choice (representative_comparison.{c, v, r, a, w, z} R A φ L) ≪≫
    Functor.isoWhiskerLeft
      ((DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q)
      (globalHomSourceIso.{c, v, r, a, w, z} R A φ eL)

private def cohomologyIso
    (E : DerivedCategory (Modules.{c, v, max c v r} R))
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    (eL : DerivedCategory.Q.obj L ≅ E) (q : ℤ) :
    globalHom.{c, v, r, a, w, z} R A φ E ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q ⋙
        ModuleCat.uliftFunctor.{w} A ≅
      shiftedHomFunctor.{c, v, r, a, w} R A φ E q := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let P := DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R
  let T := P.ι ⋙ DerivedCategory.Q.{w}
  have : T.Full := injectives_full P (fun _ h ↦ h)
  have : T.EssSurj := injectives_essSurj P (fun _ h ↦ h)
  let U := ModuleCat.uliftFunctor.{w, max c v r} A
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q
  let b := coefficientComparisonAt.{c, v, r, a, w, z} R A φ E L eL
  let η : T ⋙ globalHom.{c, v, r, a, w, z} R A φ E ⋙ H ⋙ U ≅
      P.ι ⋙ representative.{c, v, r, a} R A φ L ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max c v r} A) (.up ℤ) q ⋙ U :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight b.symm H ≪≫
        Functor.isoWhiskerLeft (P.ι ⋙ representative.{c, v, r, a} R A φ L)
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max c v r} A) q)) U
  let ξ := Functor.isoWhiskerLeft (shiftFunctor _ q)
    (Functor.isoWhiskerRight
      ((linearCoyoneda (Scalars.{c, v, max c v r} R) _).mapIso eL.symm.op)
      (ModuleCat.restrictScalars φ ⋙ ModuleCat.uliftFunctor.{max c v r} A))
  exact descendIso T (η ≪≫
    Classical.choice (representative_cohomology_comparison.{c, v, r, a, w} R A φ L q) ≪≫
    Functor.isoWhiskerLeft T ξ)

attribute [local irreducible] cohomologyIso

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
          e N q (b • x) = (φ b) • e N q x) := by
  let β := coefficientComparisonAt.{c, v, r, a, w, z} R A φ E L eL
  refine ⟨fun I hI ↦ β.app ⟨I, hI⟩, ?_, ?_⟩
  · intro I I' hI hI' f
    exact β.hom.naturality (ObjectProperty.homMk
      (X := ⟨I, hI⟩) (Y := ⟨I', hI'⟩) f)
  · let γ := cohomologyIso.{c, v, r, a, w, z} R A φ E L eL
    let e := fun N q ↦
      ((ULift.moduleEquiv (R := A)).symm.toAddEquiv.trans
        ((γ q).app N).toLinearEquiv.toAddEquiv).trans
          (ULift.moduleEquiv (R := A)).toAddEquiv
    refine ⟨e, ?_, ?_⟩
    · intro N N' f q x
      have h := ConcreteCategory.congr_hom ((γ q).hom.naturality f) (ULift.up x)
      exact congrArg ULift.down h
    · intro N q b x
      have h := ((γ q).app N).hom.hom.map_smul b (ULift.up x)
      exact congrArg ULift.down h

end CategoryTheory.RingedSiteGlobalRHom
