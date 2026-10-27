/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.CategoryTheory.InternalRestrictionModuleTensorData
import Sheaf.CategoryTheory.InternalRestrictionModulePullback
import Sheaf.CategoryTheory.InternalActionDiagonalTensor
import Sheaf.CategoryTheory.NormalizedPrecompositionTensor
import Sheaf.CategoryTheory.SheafActionGrothendieckInflation

/-! # Exact, normalized tensor pullback for internal action restriction

Source: internal-action infrastructure for paragraph (3) of
sk-thm-sf-ctf-stability-direct-images; Stacks 03D7, 03CY, 03DA, 03EK.
(blueprint: lem-sfb-internal-restriction-module-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem actionForgetExact_pair [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (θ : L ⟶ K) :
    ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck R) K ∧
      ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck R) L := by
  have h := sheaf_action_grothendieck_inflation J hJ K L hK hL R θ
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- Exact internal-action module restriction and inflation, with their canonical
regular-ring, diagonal tensor, and symmetric monoidal normalizations.

Source: paragraph (3), internal-action infrastructure; Stacks 03D7, 03CY, 03DA, 03EK
(blueprint: lem-sfb-internal-restriction-module-tensor).

Proof:
1. The section-pinned action-site equivalence identifies module inverse image with
   trivial inflation or substitution theta(a) in the linear action. The identity
   structural ring map makes module pullback R tensor_R F(M) (03D7).
2. Multiplication sends r tensor m to rm and its inverse sends m to 1 tensor m.
   The balancing relation proves both inverse identities. Bilinear universality
   extends these identities through module sheafification; linearity proves naturality.
3. Kernels are sectionwise and cokernels are sheafified sectionwise quotients, by
   the action-site presentation (03DA). Substitution and trivial action leave these
   underlying constructions unchanged, including sheafification. Addition of maps
   is unchanged too. Thus both functors preserve kernels and cokernels and are exact.
4. On presheaf tensors use the diagonal action a(x tensor y)=ax tensor ay.
   Balancing, identity and composition are checked on pure tensors; sheafification
   gives the base sheaf tensor with this action (03EK).
5. The identity on these presheaf tensors sheafifies to the comparison isomorphism.
   The scalar insertion becomes the identity under step 2. This verifies the full
   generalized pure-tensor normalization of CanonicalRingedTensorComparison, so it
   is the canonical comparison. The regular-ring unit comparison is the identity.
6. Naturality and symmetry agree on pure tensors; both unit equations are scalar
   multiplication. Bilinear universality proves these equations. Associativity is
   checked on (x tensor y) tensor z by the trilinear universal property. Forgetting
   the action is faithful, so all equations hold in the action category as well. -/
theorem internalRestrictionModuleTensor [HasFiniteLimits C]
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
      ∃ (P : InternalExactTensorPullback p) (Q : InternalExactTensorPullback q),
        ∃ (ep : P.core.pullback ≅
          trivialSheafAction (baseRing J.toGrothendieck R) K ⋙ PK.sheafEquivalence.functor)
          (eq : Q.core.pullback ≅ PK.sheafEquivalence.inverse ⋙
          inflateSheaf J.toGrothendieck (baseRing J.toGrothendieck R) θ ⋙
            PL.sheafEquivalence.functor ⋙
              SheafOfModules.restrictScalars
                ((sheafCompose (topology L J) (forget₂ CommRingCat RingCat)).map
                  (eqToIso hqR).hom)),
        (∀ (M : ringedSiteModules.{u} (baseRing J.toGrothendieck R)) (X : C)
          (m : (P.core.pullback.obj M).val.obj (op (Object.mk (K := K) X))),
          internalPresentationSection PK
            ((trivialSheafAction (baseRing J.toGrothendieck R) K).obj M) X
            ((ep.hom.app M).val.app (op (Object.mk X)) m) =
            P.core.sections M (op (Object.mk X))
              ((P.core.unitor.hom.app M).val.app (op (Object.mk X)) m)) ∧
        (∀ (M : ringedSiteModules.{u} (twistedRing K J hJ R)) (X : C)
          (m : (Q.core.pullback.obj M).val.obj (op (Object.mk (K := L) X))),
          PK.inverseSections M X
            (internalPresentationSection PL
              ((inflateSheaf J.toGrothendieck (baseRing J.toGrothendieck R) θ).obj
                (PK.sheafEquivalence.inverse.obj M)) X
              ((eq.hom.app M).val.app (op (Object.mk X)) m)) =
            cast (congrArg (fun Z : Object K ↦ ↥(M.val.obj (op Z)))
              (hθobj (Object.mk (K := L) X)))
              (Q.core.sections M (op (Object.mk X))
                ((Q.core.unitor.hom.app M).val.app (op (Object.mk X)) m))) ∧
        ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck R) K ∧
        ActionForgetExact J.toGrothendieck (baseRing J.toGrothendieck R) L ∧
        InternalDiagonalTensor J hJ K R PK ∧ InternalDiagonalTensor J hJ L R PL := by
  intro PK PL hp hq p hqR q
  obtain ⟨cp, cq, ep, eq, hpLaws, hqLaws, hep, heq⟩ :=
    internalRestrictionModulePullback J hJ K L hK hL θ R Fθ hθobj hθmap
      PK PL hp hq p hqR q
  obtain ⟨P, hP⟩ := normalizedPrecompositionTensor p cp hpLaws
  obtain ⟨Q, hQ⟩ := normalizedPrecompositionTensor q cq hqLaws
  subst cp
  subst cq
  refine ⟨P, Q, ep, eq, hep, heq, ?_, ?_, ?_, ?_⟩
  · exact (actionForgetExact_pair J hJ K L hK hL R θ).1
  · exact (actionForgetExact_pair J hJ K L hK hL R θ).2
  · exact internalActionDiagonalTensor J hJ K hK R PK
  · exact internalActionDiagonalTensor J hJ L hL R PL

end CategoryTheory.InternalActionSite
