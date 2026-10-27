/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Algebraicity of coherent families on algebraic spaces

Source: Stacks Project, quot.tex, Situation 08KB, Theorem 09DS and Lemma 08KD;
stacks-limits.tex, Tag 0CMY (blueprint: lem-sfb-space-coherent-stack-general).

The total category retains actual modules, pullback isomorphisms and their base maps.
The scheme-base clause retains the structural map to B through the forgetful functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An object is a scheme mapping to B and a finitely presented quasi-coherent module
on X_T, flat over T with proper support in the closed-pushforward convention.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
structure CoherentModuli (f : X ⟶ B) where
  base : ProperQuotTest B
  module : (properQuotFibre f base).Modules
  quasiCoherent : module.IsQuasicoherent
  finitePresentation : module.IsFinitePresentation
  flat : ∀ U : (properQuotFibre f base).EtaleSite,
    ((schemeRestriction (properQuotFibre f base) U).obj module).IsFlatOver
      (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f base).hom.hom)).left
  properSupport : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ properQuotFibre f base),
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
    MapIsProper (i ≫ properQuotSnd f base) ∧ ∃ G : Z.Modules,
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ module)

namespace CoherentModuli

/-- Arrows retain a map over B and the actual tensor-pullback isomorphism.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
structure Hom {f : X ⟶ B} (A C : CoherentModuli f) where
  base : A.base ⟶ C.base
  iso : (moduleTensorPullback (properQuotFibreMap f base)).obj C.module ≅ A.module

/-- Fibre maps preserve identities and composition.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general).
Proof: compose with both sheaf fibre-product projections. The first component is the
identity on X, the second is the specified test-scheme map. The identity and composite
laws in the base give equal components; the pullback universal property gives equality. -/
theorem fibreMap_laws (f : X ⟶ B) :
    (∀ T : ProperQuotTest B, properQuotFibreMap f (𝟙 T) = 𝟙 (properQuotFibre f T)) ∧
    (∀ {T₀ T₁ T₂ : ProperQuotTest B} (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂),
      properQuotFibreMap f (a ≫ b) = properQuotFibreMap f a ≫ properQuotFibreMap f b) := by
  sorry

/-- Identity uses the existing multiplication-normalized tensor identity.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
def identity {f : X ⟶ B} (A : CoherentModuli f) : Hom A A where
  base := 𝟙 A.base
  iso := eqToIso (congrArg (fun p ↦ (moduleTensorPullback p).obj A.module)
    ((fibreMap_laws f).1 A.base)) ≪≫ (moduleTensorPullbackId _).app A.module

/-- Composition uses the existing pure-tensor-normalized associativity comparison.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
def composition {f : X ⟶ B} {A C D : CoherentModuli f} (a : Hom A C) (b : Hom C D) :
    Hom A D where
  base := a.base ≫ b.base
  iso := eqToIso (congrArg (fun p ↦ (moduleTensorPullback p).obj D.module)
      ((fibreMap_laws f).2 a.base b.base)) ≪≫
    ((moduleTensorComposition (properQuotFibreMap f a.base)
      (properQuotFibreMap f b.base)).app D.module).symm ≪≫
    (moduleTensorPullback (properQuotFibreMap f a.base)).mapIso b.iso ≪≫ a.iso

/-- The concrete identity and composition satisfy the category laws.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general).
Proof: the base maps satisfy the category laws. For modules the identity comparison
acts by multiplication and the composition comparison by tensor associativity. On
local generating tensors these satisfy the two unit laws and the associativity law.
Naturality moves the given module isomorphisms through those comparisons. Equality
on the generating tensors implies equality after sheafification, hence of the isos. -/
theorem category_laws (f : X ⟶ B) :
    (∀ {A C : CoherentModuli f} (a : Hom A C), composition (identity A) a = a) ∧
    (∀ {A C : CoherentModuli f} (a : Hom A C), composition a (identity C) = a) ∧
    (∀ {A C D E : CoherentModuli f} (a : Hom A C) (b : Hom C D) (c : Hom D E),
      composition (composition a b) c = composition a (composition b c)) := by
  sorry

/-- The category of the specified modules and cartesian module isomorphisms.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
instance instCategory {f : X ⟶ B} : Category (CoherentModuli f) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := (category_laws f).1
  comp_id := (category_laws f).2.1
  assoc := (category_laws f).2.2

/-- Forget the module while retaining its specified test-scheme map to B.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
def forgetTest (f : X ⟶ B) : CoherentModuli f ⥤ ProperQuotTest B where
  obj A := A.base
  map a := a.base

/-- Projection to schemes over S.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-stack-general). -/
def category (f : X ⟶ B) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forgetTest f ⋙ CostructuredArrow.proj yoneda B.obj.obj)

/-- The canonical structural morphism remembering the map to B.
Source: Stacks, Remark 08LP (blueprint: lem-sfb-space-coherent-stack-general). -/
def toBase (f : X ⟶ B) : BasedFunctor (category f) (discreteModuli B.obj.obj) where
  toFunctor := forgetTest f
  w := rfl

end CoherentModuli

/-- Algebraicity without ambient flatness or Noetherian hypotheses, and local finite
presentation over a scheme base. The 2-isomorphism ties q to the actual structural map.
Source: Stacks, Theorem 09DS and Lemma 08KD, with Tag 0CMY
(blueprint: lem-sfb-space-coherent-stack-general).
Proof:
1. lem-sfb-space-coherent-fppf-stack gives etale stack descent, and
   lem-sfb-space-coherent-diagonal gives the algebraic-space diagonal.
2. First let B be affine of finite type over Z. Use
   lem-sfb-space-coherent-limit-preserving, lem-sfb-space-coherent-pushout,
   lem-sfb-space-coherent-tangent-finite and lem-sfb-space-coherent-formal-effectivity
   for the corresponding Artin axioms.
   lem-weil-pbc-finite-type-over-noetherian and pqf-lem-lft-fp-locnoeth give the base
   finiteness hypotheses. Apply lem-sfb-artin-representable-diagonal-criterion.
3. For openness of versality, compatible maps from the affine base into a square-zero
   tower induce a map into its inverse limit. Separated finite presentation persists
   after base change (lem-sfb-space-separated-fp-composition and
   lem-sfb-space-flat-proper-fp-locality). Apply
   lem-sfb-space-flat-proper-support-inverse-effectivity, then
   lem-sfb-artin-square-zero-effectivity-openness. No flatness of X is needed.
4. Finite presentations and their gluing data in the fixed universes give the size
   bound. The Artin criterion gives algebraicity; use
   lem-sfb-algebraic-stack-change-base-to-integers to regard it over B.
5. Coherent families commute with base change by the explicit fibre-product
   identification. Write an arbitrary affine base as the colimit of its finitely
   generated integer subalgebras (lem-weil-pbc-directed-subalgebra-ring-colimit).
   Descend X and separatedness by lem-sfb-fp-space-limit-category and
   lem-sfb-space-descend-separated; algebraicity follows by
   lem-sfb-algebraic-stack-fibre-products and change of base.
6. Assemble atlas families using lem-weil-pbc-scheme-coproduct-family,
   lem-trf-algebraic-space-coproduct and lem-sfb-scheme-etale-source-target-properties.
   Stack descent glues the objects; their base changes are the corresponding
   coproducts of smooth algebraic spaces, and joint surjectivity gives an atlas.
7. For a scheme B, use an affine open cover. For a space B use an etale scheme cover.
   lem-sfb-fibred-groupoid-representable-smooth-calculus makes the resulting composites
   representable smooth and jointly surjective. Step 6 supplies the atlas over S.
8. When B is a scheme, change the ambient base to B. Apply
   lem-sfb-space-coherent-limit-preserving with the identity B to obtain continuity,
   then lem-sfb-stack-limit-preserving-lfp to obtain a locally finitely presented
   atlas composite. Return to S by change of base. The natural 2-isomorphism records
   that this composite is precisely the map remembering b. -/
theorem coherent_stack_general (f : X ⟶ B) (hsep : MapIsSeparated f)
    (hfp : ProperQuotFinitePresentation f) :
    IsAlgebraicModuliStack (CoherentModuli.category f) ∧
      ∀ (B₀ : Over S) (e : schemeSpace B₀ ≅ B),
        ∃ (U : Over S)
          (a : BasedFunctor (discreteModuli (yoneda.obj U)) (CoherentModuli.category f))
          (q : U ⟶ B₀),
          IsSmoothModuliAtlas (CoherentModuli.category f) U a ∧
          LocallyOfFinitePresentation q.left ∧
          Nonempty (ModuliTwoIso (BasedFunctor.comp a (CoherentModuli.toBase f))
            (discreteModuliMap (yoneda.map q ≫ e.hom.hom.hom))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
