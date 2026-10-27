/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp
import Sheaf.AlgebraicGeometry.StackInfinitesimalSmoothCriterion
import Sheaf.AlgebraicGeometry.CurveLimitPreservation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections

/-! # The Picard stack of a proper flat algebraic-space family

Source: Stacks Project, quot.tex, Tag 0D04; moduli.tex, Tags 0DPJ and 0DMB
(blueprint: lem-sfb-space-picard-stack-smooth).

The total category retains line modules on the small etale site, base maps and the
actual canonical tensor-pullback isomorphisms. Algebraicity does not require a dimension
bound. The conditional smooth atlas includes field-extension lifting of its objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Objects are scheme tests of the base and actual line modules on their fibre products.
There are no coherence, flatness or support fields imposed on the modules.
Source: Stacks, quot.tex, section-picard-stack, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
structure PicardModuli (f : X ⟶ B) where
  base : ProperQuotTest B
  module : (properQuotFibre f base).Modules
  line : (properQuotFibre f base).IsLineModule module

namespace PicardModuli

/-- Arrows over u : T' → T are isomorphisms u_X^* M ≅ M'.
Source: Stacks, Examples of Stacks, section-picard-stack; quot.tex, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
structure Hom {f : X ⟶ B} (A C : PicardModuli f) where
  base : A.base ⟶ C.base
  iso : (moduleTensorPullback (properQuotFibreMap f base)).obj C.module ≅ A.module

/-- Identity uses the canonical multiplication comparison for module tensor pullback.
Source: Stacks, Modules on Sites, Tag 03D7; quot.tex, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
def identity {f : X ⟶ B} (A : PicardModuli f) : Hom A A where
  base := 𝟙 A.base
  iso := eqToIso (congrArg (fun p ↦ (moduleTensorPullback p).obj A.module)
    ((CoherentModuli.fibreMap_laws f).1 A.base)) ≪≫
      (moduleTensorPullbackId _).app A.module

/-- Composition is the canonical tensor associativity comparison followed by the two isos.
Source: Stacks, Modules on Sites, Tag 03D7; quot.tex, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
def composition {f : X ⟶ B} {A C D : PicardModuli f} (a : Hom A C) (b : Hom C D) :
    Hom A D where
  base := a.base ≫ b.base
  iso := eqToIso (congrArg (fun p ↦ (moduleTensorPullback p).obj D.module)
      ((CoherentModuli.fibreMap_laws f).2 a.base b.base)) ≪≫
    ((moduleTensorComposition (properQuotFibreMap f a.base)
      (properQuotFibreMap f b.base)).app D.module).symm ≪≫
    (moduleTensorPullback (properQuotFibreMap f a.base)).mapIso b.iso ≪≫ a.iso

/-- The specified Picard arrows satisfy the category laws.
Source: Stacks, Examples of Stacks, section-picard-stack; Modules on Sites, Tag 03D7
(blueprint: lem-sfb-space-picard-stack-smooth).
Proof: base arrows satisfy the ordinary category laws. The canonical tensor identity
acts by multiplication and the composition comparison by tensor associativity. On
local generating pure tensors the two unit laws and associativity are the corresponding
ring-module identities. Naturality moves the supplied isomorphisms through these
comparisons. Equality on local generators gives equality after sheafification, hence
of the module isomorphisms. Proof irrelevance identifies the commuting-triangle proofs. -/
theorem category_laws (f : X ⟶ B) :
    (∀ {A C : PicardModuli f} (a : Hom A C), composition (identity A) a = a) ∧
    (∀ {A C : PicardModuli f} (a : Hom A C), composition a (identity C) = a) ∧
    (∀ {A C D E : PicardModuli f} (a : Hom A C) (b : Hom C D) (c : Hom D E),
      composition (composition a b) c = composition a (composition b c)) := by
  sorry

/-- The total category with its specified cartesian line-module isomorphisms.
Source: Stacks, quot.tex, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
instance instCategory {f : X ⟶ B} : Category (PicardModuli f) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := (category_laws f).1
  comp_id := (category_laws f).2.1
  assoc := (category_laws f).2.2

/-- Forget the line module and retain the actual test scheme and its map to B.
Source: Stacks, quot.tex, section-picard-stack, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
def forgetTest (f : X ⟶ B) : PicardModuli f ⥤ ProperQuotTest B where
  obj A := A.base
  map a := a.base

/-- The Picard groupoid over schemes over S, retaining all module automorphisms.
Source: Stacks, quot.tex, section-picard-stack, Tag 0D04
(blueprint: lem-sfb-space-picard-stack-smooth). -/
def category (f : X ⟶ B) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forgetTest f ⋙ CostructuredArrow.proj yoneda B.obj.obj)

end PicardModuli

/-- The Picard stack is algebraic for every proper flat finitely presented family.
If all geometric fibres have dimension at most one, it has a smooth surjective scheme
atlas whose structural map to S is smooth. Surjectivity also has the field-extension
lifting formulation. The chartwise dimension bound is exactly the supremum convention,
including dimension bottom for the empty fibre. No other family hypotheses are imposed.
Source: Stacks, quot.tex, Tag 0D04; moduli.tex, Tags 0DPJ and 0DMB
(blueprint: lem-sfb-space-picard-stack-smooth).

Proof:
1. Apply lem-sfb-space-coherent-stack-general: properness implies separatedness by
   lem-sfb-space-flat-proper-fp-locality. Identify PicardModuli with the invertible
   subcategory in lem-sfb-space-invertible-open-coherent, using the same modules,
   tensor pullbacks and isomorphisms. This is an open substack of the coherent stack.
   lem-sfb-open-stack-algebraic-lfp gives algebraicity and local finite presentation,
   without a fibre-dimension restriction.
2. Under the dimension bound, use lem-sfb-stack-infinitesimal-smooth-criterion. For an
   arbitrary affine first-order thickening T ⊂ T', let I = ker(A' → A), with I² = 0.
   A line module L on Z = X_T must extend to Z' = X_T'. Base change preserves flatness,
   properness and finite presentation; geometric fibres retain the given bound.
3. Order the finitely generated integer subalgebras A'_i of A' by inclusion. Put
   I_i = I ∩ A'_i and A_i = A'_i/I_i. Then I_i² = 0, both rings have the required
   directed colimits, and the spectra give the two affine inverse systems. Use
   lemma-nagata-noetherian-inverse-system-affine and
   lem-weil-pbc-finite-type-over-noetherian. No cartesian-stage-thickening claim is made.
4. Descend Z' and its family properties to a Noetherian stage by
   lem-sfb-curve-limit-preservation. At subsequent stages set Z_i = Z'_i ×_{T'_i} T_i.
   Their affine-transition limit is Z, and they are quasi-compact and quasi-separated.
   lem-sfb-space-invertible-limit-descent descends L to some line module L_i on Z_i.
5. lem-sfb-space-thickening-base-change makes Z_i ⊂ Z'_i a square-zero thickening.
   On Noetherian affine etale charts its ideal is I_i B', finitely generated by
   lem-trf-noetherian-submodule-finitely-presented. By
   lem-sfb-space-closed-immersion-quasi-coherent-modules its quotient-action ideal
   J_i is a coherent module on Z_i. The base T_i is Noetherian as a quotient of T'_i.
6. lem-sfb-noetherian-space-fibre-cohomology-bound gives R²p_* J_i = 0. Since T_i is
   affine, lem-sfb-space-affine-base-higher-image-sections gives H²(Z_i,J_i) = 0.
   lem-sfb-space-square-zero-picard-obstruction extends L_i to a line module L'_i.
7. Pull L'_i back to Z'. Pulling back its local trivializations makes it a line module.
   Canonical tensor composition identifies its restriction with L. This proves lifting
   even for non-Noetherian T'. Together with step 1,
   lem-sfb-stack-infinitesimal-smooth-criterion gives a smooth atlas with smooth
   structural map. lem-sfb-stack-chartwise-smooth-etale-calculus gives its precise
   field-extension surjectivity. Empty, nonreduced and disconnected fibres are allowed. -/
theorem picard_stack_smooth {S : Scheme.{u}} (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 S)))
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hfp : ProperQuotFinitePresentation f) :
    IsAlgebraicModuliStack (PicardModuli.category f) ∧
      ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ S)
          (U : (properQuotFibre f
            (CostructuredArrow.mk (yoneda.map
              (Over.homMk (U := Over.mk a) (V := Over.mk (𝟙 S)) a
                (Category.comp_id a))))).EtaleSite),
          IsAffine U.obj.left.left → topologicalKrullDim U.obj.left.left ≤ 1) →
        ∃ (V : Over S)
          (a : BasedFunctor (discreteModuli (yoneda.obj V)) (PicardModuli.category f)),
          IsSmoothModuliAtlas (PicardModuli.category f) V a ∧ Smooth V.hom ∧
            IsSurjectiveModuliMap a) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
