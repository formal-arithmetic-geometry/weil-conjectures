module

public import Sheaf.AlgebraicGeometry.SpaceZariskiOrdinaryComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Canonical Zariski comparisons on represented algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 071Q and 08GH; descent.tex, Tag 03FH
(blueprint: def-sfb-space-zariski-derived-comparison).

The right functor is actual restriction to opens. The ordinary square is normalized
by its projection to the preimage open, and all derived comparisons retain their units.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]
variable [∀ T : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]

/-- Normalized presentations of exact epsilon pullback and its derived adjunction.
The right derived functor is the fixed K-injective derived restriction. The
representative Hom equation pins the derived adjunction to the ordinary one.
Source: Stacks 071Q, 08H8 and 08GH
(blueprint: def-sfb-space-zariski-derived-comparison). -/
structure SpaceZariskiDerivedData (Y : Over S) where
  context : SpaceZariskiContext Y
  [additive : context.extension.Additive]
  exact_limits : PreservesFiniteLimits context.extension
  exact_colimits : PreservesFiniteColimits context.extension
  extension : schemeDerivedCategory Y.left ⥤ (schemeSpace Y).DerivedModules
  factors : DerivedCategory.Qh.{w} ⋙ extension ≅
    context.extension.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  adjunction : extension ⊣ (spaceZariskiRestriction Y).rightDerivedFunctor
  normalized :
    ∀ (P : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.left.toRingedSpace)) (.up ℤ))
      (I : HomotopyCategory (schemeSpace Y).SmallModules (.up ℤ))
      (t : (context.extension.mapHomotopyCategory (.up ℤ)).obj P ⟶ I),
      adjunction.homEquiv (DerivedCategory.Qh.{w}.obj P) (DerivedCategory.Qh.{w}.obj I)
        (factors.hom.app P ≫ DerivedCategory.Qh.{w}.map t) =
      DerivedCategory.Qh.{w}.map
        ((context.adjunction.mapHomotopyCategory (.up ℤ)).homEquiv P I t) ≫
          (spaceZariskiRestriction Y).rightDerivedFunctorUnit.app I

attribute [instance] SpaceZariskiDerivedData.additive

/-- The universal comparison for a composite of two right-derived functors,
using the specified complex units. Source: Stacks 0B6C and 08GH
(blueprint: def-sfb-space-zariski-derived-comparison). -/
def spaceZariskiCompositeUnit
    {C D E : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (P : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P) ≫
    spaceRightDerivedComplexUnit G ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
    G.rightDerivedFunctor.map (spaceRightDerivedComplexUnit F P)

/-- The derived right square, normalized by the ordinary comparison and universal
right-derived units. It determines the derived left square by adjunction conjugation.
Source: Stacks 08GH (blueprint: def-sfb-space-zariski-derived-comparison). -/
structure SpaceZariskiDerivedSquare {Y' Y : Over S} (g : Y' ⟶ Y)
    (d : SpaceZariskiDerivedData Y) (d' : SpaceZariskiDerivedData Y') where
  ordinary : SpaceZariskiOrdinarySquare g
  comparison : derivedDirectImage (traceSchemeMap g) ⋙
      (spaceZariskiRestriction Y).rightDerivedFunctor ≅
    (spaceZariskiRestriction Y').rightDerivedFunctor ⋙ schemeDerivedDirectImage g.left
  representatives : ∀ P : CochainComplex (schemeSpace Y').SmallModules ℤ,
    spaceZariskiCompositeUnit (smallModuleDirectImage (traceSchemeMap g))
        (spaceZariskiRestriction Y) P ≫ comparison.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary.comparison (.up ℤ)).hom.app P) ≫
        spaceZariskiCompositeUnit (spaceZariskiRestriction Y')
          (RingedSpace.moduleDirectImage g.left.toLRSHom.toShHom) P

/-- The canonical derived pullback comparison is the mate of the preceding right
square. Source: Stacks 08GH (blueprint: def-sfb-space-zariski-derived-comparison). -/
def spaceZariskiDerivedPullback {Y' Y : Over S} (g : Y' ⟶ Y)
    (d : SpaceZariskiDerivedData Y) (d' : SpaceZariskiDerivedData Y')
    (r : SpaceZariskiDerivedSquare g d d') :
    AlgebraicGeometry.derivedPullback g.left ⋙ d'.extension ≅
      d.extension ⋙ spaceDerivedPullback (traceSchemeMap g) :=
  ((conjugateIsoEquiv ((canonicalSchemeDerivedAdjunction g.left).comp d'.adjunction)
    (d.adjunction.comp (spaceDerivedAdjunction (traceSchemeMap g)))).symm r.comparison.symm).symm

end AlgebraicGeometry.AlgebraicSpace
