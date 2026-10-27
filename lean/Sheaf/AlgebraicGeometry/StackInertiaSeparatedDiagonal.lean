/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.SeparatedRepresentableModuliMap
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Separated inertia and separated stack diagonal

Source: Stacks Project, Morphisms of Stacks, Tags 0CL0(1) and 050Q
(blueprint: lem-sfb-stack-inertia-separated-diagonal).

The same criterion applies to the relative diagonal and the absolute diagonal over the
integers. There is no separatedness assumption on the base scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- The canonical neutral section of absolute inertia sends an object to its identity
vertical automorphism. It is the existing relative neutral section for the structure
map, followed by the canonical inclusion into absolute inertia.
Source: Stacks Project, Tags 034H and 0CL0, paragraph preceding the lemma
(blueprint: lem-sfb-stack-inertia-separated-diagonal). -/
def moduliInertiaNeutral {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) :
    BasedFunctor F (moduliInertia F) :=
  (relativeModuliInertiaNeutral (moduliBaseStructure F)).comp
    (relativeModuliInertiaToAbsolute (moduliBaseStructure F))

/-- For a DM stack the inertia projection is separated exactly when its diagonal is
separated, exactly when the neutral section is a closed immersion. The criterion is
unchanged for the absolute diagonal over the integers.

Source: Stacks Project, Morphisms of Stacks, Tags 0CL0(1), 050Q, and Categories,
Tag 034H (blueprint: lem-sfb-stack-inertia-separated-diagonal).

Proof:
1. A DM atlas is smooth, since representable etale maps are smooth. Apply
   lem-sfb-relative-inertia-second-diagonal-geometry to the structure map to S.
   Its diagonal and inertia projection are representable, and its second diagonal
   identifies with the neutral section. Scheme tests of the second diagonal are
   equalizers of the two sections of the corresponding algebraic-space base change.
   Thus separatedness of the first diagonal is equivalent to closedness of the section.
2. For an object x over T the inertia base change is Aut(x). Conjugation sends
   (y,beta,v:y~x) to v beta v⁻¹, with inverse g ↦ (x,g,1). The pullback of the neutral
   section along (x,alpha) is the identity locus alpha=1. These descriptions commute
   with every base change and retain all nilpotent structure.
3. If inertia is separated, pull back the closed diagonal of Aut(x)/T along (alpha,1).
   The resulting closed identity locus represents the scheme test of the neutral
   section, proving it is a closed immersion. Form the algebraic-space fibre products
   using lem-trf-space-fibre-products-etale-covers.
4. Conversely pull back the closed neutral section along (x,g⁻¹h). The closed locus
   g⁻¹h=1 is exactly g=h, the scheme test of the diagonal of Aut(x)/T. Hence all
   inertia base changes are separated. Combine this with step 1.
5. Regard the total category over Spec Z. The relative product maps to the absolute
   product by base change of the scheme diagonal of S, so the absolute diagonal is
   representable by algebraic spaces. Its second self-product has objects (x,y,(a,b));
   send them to (x,b⁻¹a), with inverse (x,alpha) ↦ (x,x,(alpha,1)). This again identifies
   the second diagonal with the same neutral section. Automorphisms and scheme tests
   are unchanged on forgetting S, so steps 1--4 give the absolute criterion as well.
   No separatedness of S is used. -/
theorem stack_inertia_separated_diagonal {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsDeligneMumfordModuliStack F) :
    (IsSeparatedRepresentableModuliMap (moduliInertiaProjection F) ↔
      IsSeparatedRepresentableModuliMap (moduliRelativeDiagonal (moduliBaseStructure F))) ∧
    (IsSeparatedRepresentableModuliMap (moduliInertiaProjection F) ↔
      ModuliSchemeTest @IsClosedImmersion (moduliInertiaNeutral F)) ∧
    (IsSeparatedRepresentableModuliMap (moduliInertiaProjection F) ↔
      IsSeparatedRepresentableModuliMap (moduliRelativeDiagonal
        (moduliBaseStructure
          (BasedCategory.ofFunctor
            (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))))) ∧
    (IsSeparatedRepresentableModuliMap
        (moduliInertiaProjection
          (BasedCategory.ofFunctor
            (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))) ↔
      IsSeparatedRepresentableModuliMap (moduliRelativeDiagonal
        (moduliBaseStructure
          (BasedCategory.ofFunctor
            (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))))) ∧
    (IsSeparatedRepresentableModuliMap
        (moduliInertiaProjection
          (BasedCategory.ofFunctor
            (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))) ↔
      ModuliSchemeTest @IsClosedImmersion
        (moduliInertiaNeutral
          (BasedCategory.ofFunctor
            (F.p ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S))))) := by
  sorry

end CategoryTheory
