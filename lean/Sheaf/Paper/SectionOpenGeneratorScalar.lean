/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.SectionModuleOperationsData

/-! # The scalar action on the canonical open-extension generator

Source: Stacks Project, Modules on Sites, Tag 03DI, lemma-extension-by-zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing inclusion of the open pro-etale site in the ambient site.
Source: Stacks 03DI and pro-etale localization, Part (1)
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
abbrev openSectionObject {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V : U.ProEt) : X.ProEt :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj V

/-- The canonical generator of the sheafified extension presheaf. The abelian
open-adjunction unit, followed by the canonical restriction identification, is
exactly the image of the summand injection indexed by the structure map of V.
Source: Stacks 03DI, the direct-sum construction and its unit
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def internalOpenGenerator {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : internalModules Λ U) (V : U.ProEt) (m : F.X.obj.obj (op V)) :
    ((equivalence Λ X).functor.obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj F)).val.obj
        (op (openSectionObject j V)) :=
  ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).hom.app
      ((ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj F.X)).hom.app (op V)
    (((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app
      F.X).hom.app (op V) m)

/-- Restrict a coefficient section to the open and apply the actual alpha_j.
Source: blueprint coefficient morphisms and Stacks 03DI, summand action
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def openCoefficientSection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V : U.ProEt) (r : (ring Λ X).obj.obj (op (openSectionObject j V))) :
    (ring Λ U).obj.obj (op V) :=
  (condensedPullbackHom Λ j).hom.app (op V)
    (((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).inv.app
      (condensedRingObj Λ X)).hom.app (op V) r)

/-- The canonical abelian open-adjunction generator is semilinear for the actual
coefficient isomorphism. This concerns only ordinary internal modules and their
sections, and makes no assertion about section-module comparison isomorphisms or
ordinary or derived Hom bijections.

Source: Stacks Project, Modules on Sites, Tag 03DI, lemma-extension-by-zero,
first proof paragraph; the projection-formula action of
`CondensedRing.linearOpenImmersionLowerShriek`.
(blueprint: lem-pd-section-open-generator-scalar).

Proof: identify the open site with the ambient site localized at the open.
The abelian adjunction unit followed by the restriction isomorphism sends m to
the summand injection indexed by the given structure map V to U. Put a equal
to the inverse restriction comparison applied to r. The canonical projection
map, defined as the adjunct of the tensor of the pullback unit and the open
unit, sends the generator of a tensor m to r tensor the generator of m.
The internal extension action is the inverse of this very projection map,
followed by extension of the action on the module restricted along alpha_j.
Consequently acting by r on the generator of m gives the generator of
alpha_j(a) acting on m. Equality is checked on these pure tensors before
sheafification and descends by the sheafification adjunction. This includes
the empty open, where all the sections concerned are zero, and the identity
open, where it is the scalar law for the ordinary module action. -/
theorem sectionOpenGenerator_scalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : internalModules Λ U) (V : U.ProEt)
    (r : (ring Λ X).obj.obj (op (openSectionObject j V)))
    (m : ((equivalence Λ U).functor.obj F).val.obj (op V)) :
    r • internalOpenGenerator Λ j F V m =
      internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m) := by sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
