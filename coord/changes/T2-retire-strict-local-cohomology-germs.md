# Strict-local cohomology germs: adopted common constructions and explicit small-model maps

## Reason

The retirement assignment is coord/retire-items.tsv row 797 (DIFFERENT). The item has
zero sorry bodies. Six of its eight definitions are literally the adopted library's
constructions; keeping them under the same public names prevents importing both APIs.
The other two have genuinely different targets: the existing live consumers use
strictHenselizationScheme, whereas the adopted source uses strictLocalization. Substituting
the latter changes their maps and invalidates the preserved small-model mate calculations.

The packet removes the entire twin module, reuses all six common definitions from
WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms, and gives only the two
necessary small-model maps explicit smallModel_ names in a focused module. It does not
copy the six common definitions into that module. Their bodies are identical, including
the free generator, degree-zero homology and shift comparison. The two model-specific
maps preserve the same chosen uniquely characterized restriction, inverse-image homology
comparison and presheaf-fibre legs. A disposable Lean probe checks all eight old/new
identities by rfl (its result is recorded in report.md). No canonical source definition,
public source import or source theorem is modified.

## Old

The withdrawn module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
import Sheaf.AlgebraicGeometry.PointedEtaleSectionConeStalkIso
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

section DerivedSections

variable {C : Type (v + 1)} [Category.{v} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v + 1}]

/-- The free sheaf `ℤ[W]` of abelian groups on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ ℤ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(ℤ[W], F)` is the étale cohomology `H^q(W, F|_W)`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalFreeSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v + 1}] :
    C ⥤ Sheaf J (AddCommGrpCat.{v + 1}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (AddCommGrpCat.free) ⋙
    presheafToSheaf _ _

/-- Evaluation at the generator: for a sheaf `G` of abelian groups on `X_ét`, the natural map
`Hom(ℤ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `ℤ[W]` given by
the identity of `W`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalFreeSheafSections
    (G : Sheaf J (AddCommGrpCat.{v + 1})) :
    (strictLocalFreeSheaf J).op ⋙ preadditiveYoneda.obj G ⟶
      G.obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality J
        (Functor.whiskerRight (uliftYoneda.{v + 1}.map g.unop) (AddCommGrpCat.free)))
    have h₂ := congr_arg (fun k ↦ k.hom (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      ((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify J
        (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((AddCommGrpCat.free).map ((uliftYoneda.{v + 1}.map g.unop).app W')).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))) =
        ((AddCommGrpCat.free).map ((uliftYoneda.{v + 1}.obj W.unop).map g)).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify J
          (uliftYoneda.{v + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))


variable [HasDerivedCategory.{v + 1} (Sheaf J AddCommGrpCat.{v + 1})]

/-- For `L ∈ D⁺(X_ét)`, the map `Hom(ℤ[W][0], L) ⟶ Hom(ℤ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`.
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalDerivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{v + 1}))) :
    (strictLocalFreeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (strictLocalFreeSheaf J).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf J (AddCommGrpCat.{v + 1})) 0).inv.naturality
        ((strictLocalFreeSheaf J).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f :
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf J).map g.unop) ≫ f) =
      (strictLocalFreeSheaf J).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((strictLocalFreeSheaf J).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

end DerivedSections

/-- The degree-n derived-sections presheaf of a bounded below derived sheaf.
Source: Stacks, Tag 03Q8
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyPresheaf {S : Scheme.{v}}
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v + 1} :=
  (strictLocalFreeSheaf S.smallEtaleTopology ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (L⟦n⟧)

/-- The canonical map from derived sections to sections of the cohomology sheaf.
It takes a derived morphism to its degree-zero homology, evaluates the free generator,
and uses the homology shift isomorphism. No sheafification isomorphism is chosen.
Source: Stacks, Tag 03Q8
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyGermMap {S : Scheme.{v}}
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) : strictLocalCohomologyPresheaf L n ⟶
      ((DerivedCategory.Plus.homologyFunctor _ n).obj L).obj :=
  strictLocalDerivedHomToHomology (L⟦n⟧) ≫
    strictLocalFreeSheafSections _ ≫
    (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n 0 n (add_zero n)).hom.app L).hom

/-- The stalk-to-source isomorphism for the strict-local mate, using the unique germ
restriction and commutation of exact inverse image with homology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1
  letI : IsIso r := by
    let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
      strictHenselizationResidue s rfl
    let := hlocal
    let y := Spec.map (CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
    have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
      rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
      change PrimeSpectrum.comap
        ((((IntermediateField.val
          (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
            σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
        (IsLocalRing.closedPoint Ω) = _
      rw [PrimeSpectrum.comap_comp]
      exact IsLocalRing.PrimeSpectrum.comap_residue _ _
    refine (strictLocalSectionCone s).isIso_restriction y hbase ?_
      G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
    intro i
    let n := (equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i
    change y ≫ (strictLocalNeighbourhoodSection s i).left ≫
      pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom
        (Scheme.strictHenselizationStructuralMap s) = n.2.left
    dsimp only [n]
    simp only [strictLocalNeighbourhoodSection,
      MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
    simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)) n).app L)

/-- Restrict the derived-sections presheaf to the small pointed affine representatives.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologyNeighbourhoodFunctor {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))ᵒᵖ ⥤
      AddCommGrpCat.{v + 1} :=
  (strictLocalNeighbourhoods s).op ⋙ strictLocalCohomologyPresheaf L n

/-- Canonical source legs: a presheaf germ, the canonical map to the cohomology-sheaf
stalk, and the unique strict-local germ restriction transported through exact inverse image.
Source: Stacks, Tags 03Q8 and 03Q9
(blueprint: def-weil-pbc-canonical-derived-cohomology-germs). -/
noncomputable def strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    strictLocalCohomologyNeighbourhoodFunctor s L n ⟶
      (Functor.const _).obj
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((upperStar AddCommGrpCat.{v + 1}
              (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L))) where
  app i :=
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((strictLocalNeighbourhoods s).obj i.unop)
      ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        i.unop).2 (strictLocalCohomologyPresheaf L n) ≫
      (Scheme.pointSmallEtale s).presheafFiber.map (strictLocalCohomologyGermMap L n) ≫
        (strictLocalCohomologySourceIso s L n).hom
  naturality i j a := by
    dsimp [strictLocalCohomologyNeighbourhoodFunctor]
    simp only [Category.comp_id, ← Category.assoc]
    congr 1
    congr 1
    let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
    exact (Scheme.pointSmallEtale s).presheafFiberCocone
      (strictLocalCohomologyPresheaf L n) |>.w (N.map a.unop).op

end AlgebraicGeometry.Etale
```

## New

The canonical DAG node def-weil-pbc-canonical-derived-cohomology-germs is attached to
the adopted module, including its full eight-declaration list. Its canonical source
isomorphism and source legs remain those on strictLocalization. The distinct small-model
maps are attached to def-weil-pbc-small-model-cohomology-germs. Their complete new module,
verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
public import Sheaf.AlgebraicGeometry.StrictLocalSectionCone
import Sheaf.AlgebraicGeometry.PointedEtaleSectionConeStalkIso
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-! # Cohomology germs on the small coordinate-ring colimit model

The free sheaf, derived-sections presheaf, germ comparison and neighbourhood functor
are the adopted library's constructions. Only their source comparison and source legs
on `strictHenselizationScheme` are defined here. The adopted source comparison instead
has target on `strictLocalization`, so it cannot replace these maps definitionally.

Source: Stacks Project, Tags 03Q8, 03Q9 and 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The source isomorphism on the small coordinate-ring colimit model, using its unique germ
restriction and commutation of exact inverse image with homology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-small-model-cohomology-germs).

Construction: choose the uniquely specified restriction of `strictLocalSectionCone`.
The pointed residue identification supplies a compatible geometric lift to the closed point.
Global sections there compute the geometric stalk, so the general section-cone criterion
proves invertibility of this same restriction. Compose with the global-sections image of
the exact inverse-image/homology comparison. The restriction is uniquely determined;
no arbitrary witness or sheafification isomorphism supplies its data. -/
@[irreducible] noncomputable def smallModel_strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1
  letI : IsIso r := by
    let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
      strictHenselizationResidue s rfl
    let := hlocal
    let y := Spec.map (CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
    have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
      rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
      change PrimeSpectrum.comap
        ((((IntermediateField.val
          (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
            σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
        (IsLocalRing.closedPoint Ω) = _
      rw [PrimeSpectrum.comap_comp]
      exact IsLocalRing.PrimeSpectrum.comap_residue _ _
    refine (strictLocalSectionCone s).isIso_restriction y hbase ?_
      G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
    intro i
    let n := (equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i
    change y ≫ (strictLocalNeighbourhoodSection s i).left ≫
      pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom
        (Scheme.strictHenselizationStructuralMap s) = n.2.left
    dsimp only [n]
    simp only [strictLocalNeighbourhoodSection,
      MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
    simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)) n).app L)

/-- The forward map is the uniquely specified restriction followed by exact homology.
Source: Stacks Project, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-small-model-cohomology-germs).
Proof: unfold the construction; the forward map of `asIso r` is `r`. -/
theorem smallModel_strictLocalCohomologySourceIso_hom {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (smallModel_strictLocalCohomologySourceIso s L n).hom =
      Classical.choose ((strictLocalSectionCone s).existsUnique_restriction
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L)) ≫
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        (((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlusHomologyFunctorIso
            n).hom.app L) := by
  unfold smallModel_strictLocalCohomologySourceIso
  rfl

/-- Canonical source legs: a presheaf germ, the canonical map to the cohomology-sheaf
stalk, and the unique strict-local germ restriction transported through exact inverse image.
Source: Stacks, Tags 03Q8 and 03Q9
(blueprint: def-weil-pbc-small-model-cohomology-germs).

Construction: use the adopted derived-sections presheaf and its canonical homology germ
map, followed by the source isomorphism for this small model. Naturality is the cocone
identity for presheaf germs on the pointed affine representative diagram. -/
noncomputable def smallModel_strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    strictLocalCohomologyNeighbourhoodFunctor s L n ⟶
      (Functor.const _).obj
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((upperStar AddCommGrpCat.{v + 1}
              (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L))) where
  app i :=
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((strictLocalNeighbourhoods s).obj i.unop)
      ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        i.unop).2 (strictLocalCohomologyPresheaf L n) ≫
      (Scheme.pointSmallEtale s).presheafFiber.map (strictLocalCohomologyGermMap L n) ≫
        (smallModel_strictLocalCohomologySourceIso s L n).hom
  naturality i j a := by
    dsimp [strictLocalCohomologyNeighbourhoodFunctor]
    simp only [Category.comp_id, ← Category.assoc]
    congr 1
    congr 1
    let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
    exact (Scheme.pointSmallEtale s).presheafFiberCocone
      (strictLocalCohomologyPresheaf L n) |>.w (N.map a.unop).op

set_option backward.isDefEq.respectTransparency false in
/-- A source leg is the homology section restricted along its fixed cone section.
Source: Stacks Project, Tag 03Q9, restriction from pointed neighbourhoods
(blueprint: def-weil-pbc-small-model-cohomology-germs).
Proof: naturality moves the homology comparison across the presheaf germ. The defining
equation of the unique section-cone restriction then gives the asserted section map. -/
theorem smallModel_strictLocalCohomologySourceLegs_app {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    (smallModel_strictLocalCohomologySourceLegs s K n).app (op i) =
      (strictLocalCohomologyGermMap K n).app (op ((strictLocalNeighbourhoods s).obj i)) ≫
        (strictLocalSectionCone s).restriction
          ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).map
          (((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlusHomologyFunctorIso
              n).hom.app K) := by
  classical
  dsimp only [smallModel_strictLocalCohomologySourceLegs]
  rw [smallModel_strictLocalCohomologySourceIso_hom]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality_assoc]
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction
    ((DerivedCategory.Plus.homologyFunctor _ n).obj K))).1 i
  change _ ≫ (_ ≫ Classical.choose _) ≫ _ = _
  erw [hr]

end AlgebraicGeometry.Etale
```

The small-model module publicly imports the adopted canonical module and the existing
pointed section cone. The residue-identification, closed-stalk criterion and section-cone
invertibility modules are private proof imports. It has two definitions and two proved defining equations, no theorem hole,
and no arbitrary existence choice: the stalk restriction is uniquely specified.

The seven parent-node statement clarifications explicitly name this existing small model,
its source comparison and legs. Their hypotheses, target objects and conclusions remain
the same. Each statement_change contains the prior statement and complete citer checks.
The remaining parents use only the six common constructions and keep the canonical node.
The unit record has no realization at this node; the unit and chapter routes are untouched.
Challenge.lean is untouched. Since this is a definition-interface retirement, the independent
review should check the affected target meanings as usual; the defining equalities explain
why none changes.

The full consumer compilation initially reached the previously reported timeout in
StrictLocalSmallModel.StrictLocalLocalizedHomGerm. The small-model source isomorphism
is now irreducible, with a proved hom equation and a proved source-leg component equation.
The localized-Hom helper uses this API directly, preserving its statement and avoiding
repeated unfolding of the closed-point/invertibility construction. This changes reduction
policy, not any map or target object. No file or proof is split to evade the time limit.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms | T2 | Withdraw the eight-declaration twin; attach the canonical node to the adopted source. |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Migrate the direct public import to the small-model module; use its explicit names where the target is the small model. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | Migrate the direct public import to the small-model module; use its explicit names where the target is the small model. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.DerivedCohomologyGermIso | unclaimed | Migrate the direct public import to the small-model module; use its explicit names where the target is the small model. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeSourceTransport | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturality | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturalityCore | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceLocalizedCocycleHomology | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceStageSectionsNaturality | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit | unclaimed | Migrate the direct public import to the small-model module; use its explicit names where the target is the small model. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Use the explicit small-model source map/leg names; the old maps and all other calculations are unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Use the explicit small-model source map/leg names; the old maps and all other calculations are unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Use the explicit small-model source map/leg names; the old maps and all other calculations are unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Use the explicit small-model source map/leg names; the old maps and all other calculations are unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Unchanged consumer of the preserved constructions and maps; no source adaptation is needed. |

The user list comes from tools/downstream.py and whole-name searches of both source roots.
All eight adapted consumers were unclaimed in the shared claim records when prepared.
No source module imports the withdrawn module. The archived predecessors
quarantine/Sheaf/AlgebraicGeometry/StrictLocalInjectiveSourceSections.lean,
quarantine/Sheaf/AlgebraicGeometry/StrictLocalInjectiveSourceRestriction.lean, and
quarantine/Sheaf/AlgebraicGeometry/StrictLocalInjectiveSourceDerivedRestriction.lean
still mention the former small-model names. Their current live realizations are the
adapted StrictLocalSmallModel modules attached to the same DAG nodes. These old archives
are not active importers or rework rows, and are preserved without modification. No
quarantined module is withdrawn, and no archived dependency is used to justify pruning.

The continuity presentation uses the adopted neighbourhood geometry existence theorem
directly: the former small-model wrapper is exactly its application. Its small-model
cone continues to use the existing transport API. It also explicitly imports its
injective-source-sections proof dependency, so all adapted modules in the projection
formula chain compile before this consumer. The first delivery attempt found the
old compiled wrapper still loading the retired geometry twin; this removes that
unnecessary wrapper import without copying or modifying it. No additional consumer
statement or map is changed.

## Consumer diffs

### lean/Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean
@@ -8,9 +8,10 @@
 public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
-public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
-import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
+import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas
 
 /-! # Presenting the strict-local mate as projection restriction
@@ -76,7 +77,7 @@
                 (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                 |>.natTrans.app K)))) := by
   classical
-  obtain ⟨Q⟩ := smallModel_nonempty_strictLocalNeighbourhoodGeometry f s
+  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
   obtain ⟨E⟩ := smallModel_nonempty_strictLocalMateProjectionData f s K n Q
   let := (Scheme.strictHenselization_properties s).2.1
   obtain ⟨hsource⟩ := smallModel_isColimit_strictLocalCohomologySourceLegs s
@@ -96,7 +97,7 @@
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
     e := E.e
     transition := E.transition
-    sourceLegs := strictLocalCohomologySourceLegs s
+    sourceLegs := smallModel_strictLocalCohomologySourceLegs s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
     sourceIsColimit := hsource
     limitIso := strictLocalBaseChangeTargetIso f s K n
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalMateProjectionData.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalMateProjectionData.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalMateProjectionData.lean
@@ -8,7 +8,7 @@
 public import Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
-public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
 public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
 
 /-! # Projection restriction formulas for the strict-local mate
@@ -129,7 +129,7 @@
         a))).inv.app K.obj) ≫
       (e i).inv
   restriction : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
-        ((strictLocalCohomologySourceLegs s
+        ((smallModel_strictLocalCohomologySourceLegs s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
         ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
         AddCommGrpCat.{v + 1}).map
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/DerivedCohomologyGermIso.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/DerivedCohomologyGermIso.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/DerivedCohomologyGermIso.lean
@@ -6,7 +6,7 @@
 
 module
 
-public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
 import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
 import Mathlib.CategoryTheory.Sites.EpiMono
 
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalCohomologySourceColimit.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalCohomologySourceColimit.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalCohomologySourceColimit.lean
@@ -6,7 +6,7 @@
 
 module
 
-public import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
+public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.DerivedCohomologyGermIso
 
 /-! # Canonical derived sections and strict-local cohomology germs
@@ -41,7 +41,7 @@
     {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
     (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
     (n : ℤ) :
-    Nonempty (IsColimit (Cocone.mk _ (strictLocalCohomologySourceLegs s L n))) := by
+    Nonempty (IsColimit (Cocone.mk _ (smallModel_strictLocalCohomologySourceLegs s L n))) := by
   let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
     Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
       (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
@@ -52,7 +52,7 @@
     (Functor.Final.isColimitWhiskerEquiv N.op _).symm
       ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P)
   let u := (Scheme.pointSmallEtale s).presheafFiber.map
-    (strictLocalCohomologyGermMap L n) ≫ (strictLocalCohomologySourceIso s L n).hom
+    (strictLocalCohomologyGermMap L n) ≫ (smallModel_strictLocalCohomologySourceIso s L n).hom
   have := smallModel_isIso_strictLocalCohomologyGermMap s L n
   have : IsIso u := by dsimp [u]; infer_instance
   refine ⟨hc.ofIsoColimit (Cocone.ext (asIso u) (fun j ↦ ?_))⟩
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceDerivedRestriction.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceDerivedRestriction.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceDerivedRestriction.lean
@@ -9,6 +9,7 @@
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison
 public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
 import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm
 
 /-! # The derived mate on a neighbourhood germ -/
 
@@ -65,7 +66,7 @@
     (q : K.obj ≅ DerivedCategory.Q.obj
       (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
     ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
-        ((strictLocalCohomologySourceLegs s
+        ((smallModel_strictLocalCohomologySourceLegs s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
         ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
         AddCommGrpCat.{v + 1}).map
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceRestriction.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceRestriction.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceRestriction.lean
@@ -65,7 +65,7 @@
     (q : K.obj ≅ DerivedCategory.Q.obj
       (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
     ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
-        ((strictLocalCohomologySourceLegs s
+        ((smallModel_strictLocalCohomologySourceLegs s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
         ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
         AddCommGrpCat.{v + 1}).map
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceSections.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceSections.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalInjectiveSourceSections.lean
@@ -91,7 +91,7 @@
               (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
             (e i).inv) ∧
       (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
-        ((strictLocalCohomologySourceLegs s
+        ((smallModel_strictLocalCohomologySourceLegs s
       ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
         ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
         AddCommGrpCat.{v + 1}).map
```

### lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalLocalizedHomGerm.lean

```diff
--- lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalLocalizedHomGerm.lean
+++ lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/StrictLocalLocalizedHomGerm.lean
@@ -144,7 +144,7 @@
     {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
     (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
     (n : ℤ) (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
-    (strictLocalCohomologySourceLegs s K n).app (op i) =
+    (smallModel_strictLocalCohomologySourceLegs s K n).app (op i) =
       (strictLocalCohomologyGermMap K n).app (op ((strictLocalNeighbourhoods s).obj i)) ≫
         (strictLocalSectionCone s).restriction
           ((DerivedCategory.Plus.homologyFunctor _ n).obj K) i ≫
@@ -153,15 +153,7 @@
           (((upperStar AddCommGrpCat.{v + 1}
             (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlusHomologyFunctorIso
               n).hom.app K) := by
-  classical
-  dsimp only [strictLocalCohomologySourceLegs, strictLocalCohomologySourceIso,
-    Iso.trans_hom, Functor.mapIso_hom]
-  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality_assoc]
-  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction
-    ((DerivedCategory.Plus.homologyFunctor _ n).obj K))).1 i
-  change _ ≫ ( _ ≫ Classical.choose _ ) ≫ _ = _ at ⊢
-  erw [hr]
-  rfl
+  exact smallModel_strictLocalCohomologySourceLegs_app s K n i
 
 set_option backward.isDefEq.respectTransparency true in
 /-- Localizing Hom into a K-injective representative and then restricting its sections
@@ -192,7 +184,7 @@
     (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
     [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ)
     (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
-    (strictLocalCohomologySourceLegs s K n).app (op i) =
+    (smallModel_strictLocalCohomologySourceLegs s K n).app (op i) =
       (sourceLocalizedSectionsIso K L r n ((strictLocalNeighbourhoods s).obj i)).hom ≫
         strictLocalComplexSectionRestriction s K L r n i := by
   rw [sourceLeg_eq_sectionRestriction]
```

All eight adapted consumers were unclaimed in the shared claim records when this
packet was prepared. Source-library declarations and quarantined archives stay intact.
The explicit private proof imports supply dependencies already used by the projection
and restriction proofs; they do not add hypotheses or change public imports.

A final focused Lean equality probe compiled against the final irreducible definition:
explicit unfolding and rfl identify both retained model-specific constructions with
the original ones. The earlier eight-definition probe also compiled, checking all six
adopted common constructions. Both probes remain scratch artifacts outside delivery.

## Status

landed 20261022T002439-L-1931164 2026-10-22 (merge of deliver/T2/Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms)
