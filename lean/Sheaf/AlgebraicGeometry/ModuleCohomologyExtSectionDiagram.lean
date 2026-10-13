/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison

/-! # The abelian Ext map in the common section-complex diagram

Source: Stacks Project, Tags 01FB, 01F7 and 03FD.
(blueprint: new-module-cohomology-ext-section-diagram)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

/-- The map on abelian Ext cohomology induced by inverse image and the counit.
Source: Stacks Project, Tag 01F7. -/
def abelianEdgeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    AddCommGrpCat.of (H ((pushforward f).obj F) p) ⟶ AddCommGrpCat.of (H F p) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p).comp
    (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p))

/-- The Ext map and the horizontal section map agree after the vertical section map.
This is a square between abelian Ext and section homology; neither the module
edge map nor the module/Ext equivalence occurs in the assertion.
Source: Stacks Project, Tag 01FB, the common section diagram;
Tag 01F7, its functorial cohomology map; Tag 03FD, forgotten injective acyclicity.
(blueprint: new-module-cohomology-ext-section-diagram)

Proof: Forget modules in I,J,K and in the augmentation equation D.compatible.
The forgotten I and J are resolutions by abelian-section-acyclic objects;
their canonical acyclic comparisons give abelianResolutionIso. The forgotten
f_*I computes the derived abelian direct image, because injective module terms
are abelian-cohomology acyclic on every open (03FD). The quasi-isomorphism
lambda into K compares this complex with its injective replacement. The
augmentation lift beta represents the map from the abelian sheaf f_*F into
this derived direct image. Evaluating the derived adjunction at the constant
integer sheaf identifies that map with exact inverse image on Ext followed
by the counit coeff(f,identity). The terminal-source comparison evaluates
the free generator at 1, so its inverse-image identification is constIso(f).
The global-section identification f_*I(Y)=I(X) is precisely D.a, pinned by
D.sections. Consequently both composites into H(Γ(Y,K)) are H(Γ(beta)).
Homotopy invariance removes the choices of augmentation lifts; naturality of
the acyclic comparison removes the choices of resolutions. This proves the
displayed square before any cancellation of its vertical map. Degree zero
is the section identity; empty schemes and zero coefficients give the same
square. No acyclicity of f_*F or exactness of module pullback is used. -/
theorem abelianEdge_section_diagram {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (D : ModuleCohomologyFMapData f ((pushforward f).obj F) F
      (𝟙 ((pushforward f).obj F))) (p : ℕ) :
    (abelianResolutionIso Y D.J p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) =
      abelianEdgeHom f F p ≫ (abelianResolutionIso X D.I p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
          (D.a.hom ≫
            ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
