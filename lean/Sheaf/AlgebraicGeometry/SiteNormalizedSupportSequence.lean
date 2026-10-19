/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Sheaf.AlgebraicGeometry.SupportComparisonBoundaryMaps
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.CategoryTheory.DerivedInjectiveBoundary

/-! # Normalized support localization on a site

Source: Stacks Project, etale-cohomology.tex Tag 09XP, and sites-cohomology.tex
Tag 093X (blueprint: lem-pur-site-normalized-support-sequence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem restriction_surjective
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]
    (M : Sheaf J (ModuleCat.{u + 1} R)) [Injective M]
    {V W : C} (a : V ⟶ W) [Mono a] :
    Function.Surjective (M.obj.map a.op) := by
  let P (T : C) : Sheaf J (ModuleCat.{u + 1} R) :=
    (presheafToSheaf J _).obj (Sheaf.freeModuleYoneda.{u + 1} R T)
  let t : Sheaf.freeModuleYoneda.{u + 1} R V ⟶
      Sheaf.freeModuleYoneda.{u + 1} R W :=
    Functor.whiskerRight (uliftYoneda.{u + 1}.map a) (ModuleCat.free R)
  have ht : Mono t := by
    have (T : Cᵒᵖ) : Mono (t.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y hxy
      apply ULift.ext
      apply (cancel_mono a).1
      exact congrArg ULift.down hxy
    exact NatTrans.mono_of_mono_app t
  let f : P V ⟶ P W := (presheafToSheaf J _).map t
  have : Mono f := inferInstance
  let e (T : C) (g : P T ⟶ M) : M.obj.obj (Opposite.op T) :=
    g.hom.app (Opposite.op T) ((toSheafify J (Sheaf.freeModuleYoneda.{u + 1} R T)).app
      (Opposite.op T) (Sheaf.freeModuleYonedaGen.{u + 1} T))
  intro x
  let b : P V ⟶ M :=
    ⟨sheafifyLift J (Sheaf.freeModuleYonedaHom.{u + 1} V M.obj x) M.property⟩
  let g := Injective.factorThru b f
  refine ⟨e W g, ?_⟩
  have hg : f ≫ g = b := Injective.comp_factorThru b f
  have he : e V b = x := by
    change ((toSheafify J _ ≫ sheafifyLift J
      (Sheaf.freeModuleYonedaHom.{u + 1} V M.obj x) M.property).app
        (Opposite.op V)) _ = x
    rw [toSheafify_sheafifyLift]
    exact Sheaf.freeModuleYonedaHom_gen V M.obj x
  rw [← he, ← hg]
  dsimp [e]
  rw [← ConcreteCategory.comp_apply, ← g.hom.naturality]
  rw [ConcreteCategory.comp_apply]
  congr 1
  change ((toSheafify J _).app (Opposite.op W) ≫ (P W).obj.map a.op)
      (Sheaf.freeModuleYonedaGen.{u + 1} W) =
    ((toSheafify J _).app (Opposite.op V) ≫ f.hom.app (Opposite.op V))
      (Sheaf.freeModuleYonedaGen.{u + 1} V)
  rw [← (toSheafify J _).naturality]
  rw [ConcreteCategory.comp_apply]
  have hgen : (Sheaf.freeModuleYoneda.{u + 1} R W).map a.op
      (Sheaf.freeModuleYonedaGen.{u + 1} W) = Finsupp.single (ULift.up a) 1 := by
    simp [Sheaf.freeModuleYonedaGen, Sheaf.freeModuleYoneda, ModuleCat.free]
  rw [hgen]
  change _ = ((toSheafify J _ ≫ f.hom).app (Opposite.op V))
    (Sheaf.freeModuleYonedaGen.{u + 1} V)
  change _ = ((toSheafify J _ ≫ sheafifyMap J t).app (Opposite.op V))
    (Sheaf.freeModuleYonedaGen.{u + 1} V)
  rw [← toSheafify_naturality]
  dsimp [t]
  simp [Sheaf.freeModuleYonedaGen, ModuleCat.free]
  rfl

/-- The kernel/restriction sequence on injective sheaves induces a normalized
localization sequence on all bounded-below derived coefficients.
Source: Stacks Project, Tag 09XP, injective restriction sequence; Tag 093X,
restriction along a monomorphism; homology.tex Tag 0117.
(blueprint: lem-pur-site-normalized-support-sequence).

Proof: restriction along a monomorphism is surjective on injective module
sheaves. Indeed, the free module presheaves on the two representables form a
monomorphism, as postcomposition is injective on each Hom set. Sheafification
preserves this monomorphism. The sheafification adjunction and free Yoneda
identify extension of a map into an injective sheaf with extension of a section.
Consequently the kernel, ambient sections and restricted sections of any
bounded-below injective complex form a short exact complex. Its snake boundary
is natural in chain maps, by HomologySequence.δ_naturality. Chain homotopies
induce equal maps on homology. The equivalence between the homotopy category of
bounded-below injectives and the bounded-below derived category therefore
transports these boundaries to natural transformations on the derived category.
Use the right-derived units to identify the three homology functors with the
three functors in the statement. The three exactness assertions follow from
the three homology exactness assertions of a short exact complex, transported
along these isomorphisms. On every injective representative the construction
recovers the original snake boundary: use its comparison with the chosen
injective representative and naturality of the derived units. Thus the
normalization holds for every injective model, with the stated sign. -/
theorem exists_site_normalized_support_sequence
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (A : Type (u + 1)) [CommRing A]
    {V W : C} (j : W ⟶ V) [Mono j] :
    ∃ δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤,
      supportBoundaryNormalization J A j δ ∧
        Sheaf.SupportSequenceExact J (ModuleCat.{u + 1} A) j ⊤ δ := by
  let S : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j
  let E : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op V)
  let G : Sheaf J (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
    sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)
  let ι : S ⟶ E := Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j
  let π : E ⟶ G := (sheafSections J (ModuleCat.{u + 1} A)).map j.op
  have w : ι ≫ π = 0 := by
    apply NatTrans.ext
    funext M
    exact kernel.condition (M.obj.map j.op)
  have h (M : Sheaf J (ModuleCat.{u + 1} A)) [Injective M] :
      (ShortComplex.mk (ι.app M) (π.app M) (NatTrans.congr_app w M)).ShortExact := by
    have : Epi (M.obj.map j.op) :=
      (ModuleCat.epi_iff_surjective _).2 (restriction_surjective J A M j)
    change (ShortComplex.mk (kernel.ι (M.obj.map j.op)) (M.obj.map j.op) _).ShortExact
    exact { exact := ShortComplex.exact_kernel (M.obj.map j.op)
            mono_f := inferInstance
            epi_g := inferInstance }
  obtain ⟨δ, hδ⟩ := Functor.exists_injectiveBoundary.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 1}
    S E G ι π w h
  refine ⟨(fun q ↦ Functor.whiskerLeft (⊤ : ObjectProperty _).ι (δ q)), ?_, ?_⟩
  · intro I hI
    refine ⟨_, Functor.injectiveBoundaryRow_shortExact S E G ι π w h I, ?_⟩
    intro q
    exact hδ I (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q
  · intro K q
    let Q := (InjectiveObject.ι (Sheaf J (ModuleCat.{u + 1} A))).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh
    let M := Q.objPreimage K.obj
    obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
    let I := (InjectiveObject.ι (Sheaf J (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj L
    have (n : ℤ) : Injective (I.obj.X n) := inferInstanceAs (Injective (L.obj.X n).obj)
    let e : DerivedCategory.Plus.Q.obj I ≅ K.obj :=
      Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K.obj
    exact Functor.injectiveBoundary_exact S E G ι π w h δ hδ I K.obj e q

end AlgebraicGeometry
