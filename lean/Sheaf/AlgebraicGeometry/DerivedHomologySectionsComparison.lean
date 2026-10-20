/-
Copyright (c) 2026 Bin Wu and the SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, SHEAF group H5
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-! # A canonical comparison from derived sections to homology sections
Source: Stacks Project, Tags 072W and 03Q8. The construction and proofs are
specializations of the comparison used for cartesian higher images. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] AbelianComparison.freeSheaf

/-- The raw degree-q section presheaf, functorial in the derived complex.
Its value at U is Hom(Z[U][0], K[q]); naming the functor caches its abelian groups.
Source: Stacks Project, Tags 072W and 03Q8.
(blueprint: def-kun-derived-homology-sections-functor). -/
@[irreducible]
noncomputable def derivedHomologySectionsFunctor (S : Scheme.{u}) (q : ℤ) :
    DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (shiftFunctor _ q) ⋙ preadditiveYoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (AbelianComparison.freeSheaf S.smallEtaleTopology ⋙
        DerivedCategory.Plus.singleFunctor _ 0).op

/-- Evaluate degree-q homology on the identity generator of the free sheaf.
This is a concrete natural transformation, with no choice of a representative.
Source: Stacks Project, Tags 072W and 03Q8.
(blueprint: def-kun-derived-homology-sections-comparison). -/
@[irreducible]
noncomputable def derivedHomologySectionsComparison
    (S : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedHomologySectionsFunctor S q).obj K ⟶
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj := by
  unfold derivedHomologySectionsFunctor
  exact (AbelianComparison.derivedHomToHomology (K⟦q⟧) ≫
    AbelianComparison.freeSheafSections _) ≫
      (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app K).hom

private theorem comparison_locally_bijective
    (S : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (derivedHomologySectionsComparison S q K) ∧
      Presheaf.IsLocallySurjective S.smallEtaleTopology
        (derivedHomologySectionsComparison S q K) := by
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  obtain ⟨_, _⟩ := AbelianComparison.isLocallyBijective_derivedHomToHomology
    (J := S.smallEtaleTopology) (K⟦q⟧)
  let raw := (AbelianComparison.derivedHomToHomology (K⟦q⟧) ≫
    AbelianComparison.freeSheafSections _) ≫
      (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app K).hom
  have hr : Presheaf.IsLocallyInjective S.smallEtaleTopology raw ∧
      Presheaf.IsLocallySurjective S.smallEtaleTopology raw := by
    dsimp only [raw]
    constructor <;> infer_instance
  unfold derivedHomologySectionsComparison derivedHomologySectionsFunctor
  exact hr

private theorem comparison_naturality
    (S : Scheme.{u}) (q : ℤ)
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : K ⟶ L) (U : S.Etale)
    (z : ((derivedHomologySectionsFunctor S q).obj K).obj (op U)) :
    ((DerivedCategory.Plus.homologyFunctor _ q).map m).hom.app (Opposite.op U)
      ((derivedHomologySectionsComparison S q K).app (Opposite.op U) z) =
      (derivedHomologySectionsComparison S q L).app (Opposite.op U)
        (((derivedHomologySectionsFunctor S q).map m).app (op U) z) := by
  unfold derivedHomologySectionsFunctor at z ⊢
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  let σ := H₀.shiftIso q 0 q (add_zero q)
  have hn := σ.hom.naturality m
  change H₀.map ((shiftFunctor _ q).map m) ≫ σ.hom.app L =
    σ.hom.app K ≫ Hq.map m at hn
  have he :
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        H₀.map z ≫ σ.hom.app K) ≫ Hq.map m =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        H₀.map (z ≫ (shiftFunctor _ q).map m) ≫ σ.hom.app L := by
    rw [Category.assoc, Category.assoc, ← hn, ← H₀.map_comp_assoc]
  unfold derivedHomologySectionsComparison
  let generator : ((AbelianComparison.freeSheaf S.smallEtaleTopology).obj U).obj.obj
      (op U) := by
    unfold AbelianComparison.freeSheaf
    exact ((toSheafify S.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U))
        (FreeAbelianGroup.of (ULift.up (𝟙 U)))
  exact congrArg (fun g ↦ (g.hom.app (Opposite.op U))
    generator) he

/-- The canonical comparison is locally bijective and natural in the complex.
Source: Stacks Project, Tags 072W and 03Q8.
(blueprint: lem-kun-derived-homology-sections-comparison).

Proof: The degree-zero derived-Hom comparison is locally bijective by local
cycle representatives and local boundary detection. Evaluation at the free
sheaf generator is an isomorphism; the shift-homology comparison is also an
isomorphism. Their composite is therefore locally bijective. For naturality,
apply homology to z followed by the shift of m. Functoriality moves this
composition through H^0, and naturality of the shift comparison identifies the
result with H^q(m) applied to the original section. Evaluate this equality of
sheaf morphisms at the represented generator. No special property of a direct
image, coefficient system, or cohomological degree is used. -/
theorem derivedHomologySectionsComparison_spec (S : Scheme.{u}) (q : ℤ) :
    (∀ K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Presheaf.IsLocallyInjective S.smallEtaleTopology
          (derivedHomologySectionsComparison S q K) ∧
        Presheaf.IsLocallySurjective S.smallEtaleTopology
          (derivedHomologySectionsComparison S q K)) ∧
    (∀ {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
      (m : K ⟶ L) (U : S.Etale)
      (z : ((derivedHomologySectionsFunctor S q).obj K).obj (op U)),
      ((DerivedCategory.Plus.homologyFunctor _ q).map m).hom.app (op U)
        ((derivedHomologySectionsComparison S q K).app (op U) z) =
      (derivedHomologySectionsComparison S q L).app (op U)
        (((derivedHomologySectionsFunctor S q).map m).app (op U) z)) :=
  ⟨comparison_locally_bijective S q, fun m U z ↦ comparison_naturality S q m U z⟩

end AlgebraicGeometry.Etale
