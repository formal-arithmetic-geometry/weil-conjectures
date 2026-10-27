/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.CategoryTheory.InternalRestrictionModuleTensorData
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Normalized exact module restriction on internal action sites

Source: Stacks 03D7, 03CY and 03DA; steps 1--3 of the internal restriction argument.
(blueprint: lem-sfb-internal-restriction-module-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The non-tensor part of internal restriction: scalar extension, multiplication,
exactness, and the section-pinned inflation identifications.

Source: Stacks Project, Modules on Sites, Tags 03D7, 03CY and 03DA;
steps 1--3 of lem-sfb-internal-restriction-module-tensor.
(blueprint: lem-sfb-internal-restriction-module-pullback).

Proof: precompose the underlying module presheaf with projection or Fθ. Its sections
and linear maps are the original sections and maps. The given set inverse image
identification proves the sheaf condition and transports addition and scalars, giving
an AlgebraicInverseImage with its underlying comparison and all graph equations.
The identity structural map gives the scalar-extension pullback and its adjunction
by the module pullback/pushforward adjunction. Multiplication r tensor m ↦ r • m
and insertion m ↦ 1 tensor m descend through module sheafification and are inverse:
one composite is 1 • m = m, and the other is 1 tensor (r • m) = r tensor m by
balancing. Bilinear universality extends the latter calculation to the sheaf tensor.
These maps are natural because module maps are linear. Kernels and addition are
sectionwise; cokernels are sheafified sectionwise quotients. Trivial action and
substitution θ(a) preserve these constructions, including their sheafification
units, by Presentation.baseComparison and siteComparison. This proves additivity
and preservation of finite limits and colimits.
For the inflation isomorphisms, apply the section identifications of PK and PL.
Projection forgets the label and Fθ replaces a by θ(a); their restriction formulas
therefore agree with trivialSheafAction and inflateSheaf. Forward and inverse
morphism naturality of the presentations makes the section identifications natural
in modules, so they assemble to ep and eq. Their defining section equations are the
two displayed equations. Zero rings, trivial groups, and empty covers use the same
module constructions without any nonzero or flatness assumption. -/
theorem internalRestrictionModulePullback [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u})) (θ : L ⟶ K)
    (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (Fθ : Object L ⥤ Object K)
    (hθobj : ∀ X : Object L, Fθ.obj X = Object.mk X.base)
    (hθmap : ∀ (X Y : Object L) (a : X ⟶ Y),
      HEq (Fθ.map a) (Arrow.mk a.base (θ.app (op X.base) a.label) :
        Object.mk (K := K) X.base ⟶ Object.mk (K := K) Y.base)) :
    ∀ (PK : Presentation K J hJ R) (PL : Presentation L J hJ R)
      (hp : Presheaf.IsSheaf (topology K J) ((projection K).op ⋙ R.obj))
      (hq : Presheaf.IsSheaf (topology L J)
        (Fθ.op ⋙ (coefficientSheaf K J hJ R).obj))
      (p : InternalPrecompositionMorphism J.toGrothendieck (topology K J)
        (projection K) R hp)
      (hqR : (⟨Fθ.op ⋙ (coefficientSheaf K J hJ R).obj, hq⟩ :
        Sheaf (topology L J) CommRingCat.{u}) = coefficientSheaf L J hJ R)
      (q : InternalPrecompositionMorphism (topology K J) (topology L J)
        Fθ (coefficientSheaf K J hJ R) hq),
      ∃ (P : InternalModulePullback p) (Q : InternalModulePullback q),
        ∃ (ep : P.pullback ≅
          trivialSheafAction (baseRing J.toGrothendieck R) K ⋙ PK.sheafEquivalence.functor)
          (eq : Q.pullback ≅ PK.sheafEquivalence.inverse ⋙
          inflateSheaf J.toGrothendieck (baseRing J.toGrothendieck R) θ ⋙
            PL.sheafEquivalence.functor ⋙
              SheafOfModules.restrictScalars
                ((sheafCompose (topology L J) (forget₂ CommRingCat RingCat)).map
                  (eqToIso hqR).hom)),
        InternalModulePullbackLaws P ∧ InternalModulePullbackLaws Q ∧
        (∀ (M : ringedSiteModules.{u} (baseRing J.toGrothendieck R)) (X : C)
          (m : (P.pullback.obj M).val.obj (op (Object.mk (K := K) X))),
          internalPresentationSection PK
            ((trivialSheafAction (baseRing J.toGrothendieck R) K).obj M) X
            ((ep.hom.app M).val.app (op (Object.mk X)) m) =
            P.sections M (op (Object.mk X))
              ((P.unitor.hom.app M).val.app (op (Object.mk X)) m)) ∧
        (∀ (M : ringedSiteModules.{u} (twistedRing K J hJ R)) (X : C)
          (m : (Q.pullback.obj M).val.obj (op (Object.mk (K := L) X))),
          PK.inverseSections M X
            (internalPresentationSection PL
              ((inflateSheaf J.toGrothendieck (baseRing J.toGrothendieck R) θ).obj
                (PK.sheafEquivalence.inverse.obj M)) X
              ((eq.hom.app M).val.app (op (Object.mk X)) m)) =
            cast (congrArg (fun Z : Object K ↦ ↥(M.val.obj (op Z)))
              (hθobj (Object.mk (K := L) X)))
              (Q.sections M (op (Object.mk X))
                ((Q.unitor.hom.app M).val.app (op (Object.mk X)) m))) := by
  sorry

end CategoryTheory.InternalActionSite
