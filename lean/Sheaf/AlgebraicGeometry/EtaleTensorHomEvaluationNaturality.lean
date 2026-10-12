/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Naturality of the tensor-sections evaluation map

Source: Stacks Project, Tags 03DT and 03DR
(blueprint: lem-sc-etale-tensor-sections-evaluation-naturality).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The comparison of tensor pullback with abstract pullback normalized by their units.
Source: Stacks Project, Tag 0096; uniqueness of left adjoints. -/
def tensorSectionsPullbackComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    tensorPullback f ≅ pullback f :=
  Adjunction.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
    (pullbackPushforwardAdjunction f)

/-- Evaluate a pulled-back module map at one after identifying its source with the
structure sheaf and its target with tensor pullback.
Source: Stacks Project, Tag 03DT, proof of Lemma 35.8.1. -/
def etaleTensorHomEvaluation {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)
    (φ : (etaleHom (unitObj X) F).obj (.op U)) :
    Γ((tensorPullback U.hom).obj F, ⊤) :=
  ((pullbackObjUnitIso U.hom).inv ≫ φ ≫
    (tensorSectionsPullbackComparison U.hom).inv.app F).app ⊤ (1 : Γ(U.left, ⊤))

/-- Evaluation of a pulled-back module map commutes with restriction on the etale site.
Source: Stacks Project, Tag 03DT, proof of Lemma 35.8.1, and Tag 03DR, (35.8.0.1).
(blueprint: lem-sc-etale-tensor-sections-evaluation-naturality).

Proof: Write e_f for the unit-normalized comparison between tensor and abstract
pullback. The conjugates of the two sides of
  e_(a b).inv ≫ tensorSectionsComp(a,b).inv =
  pullbackComp(a,b).inv ≫ whiskerLeft(pullback b,e_a.inv) ≫
  whiskerRight(e_b.inv,tensorPullback a)
are equal: conjugation takes e_f.inv to the identity, takes both composition
comparisons to pushforwardComp(a,b).hom, and respects composition and whiskering.
Injectivity of conjugation therefore proves this equation. Inverting it gives the
forward comparison equation. The unit equation of leftAdjointUniq identifies
 e_a.hom(tensorSectionsUnit a s) with pullbackSection a s. Naturality of the
adjunction unit also shows that tensorSectionsUnit commutes with any module map.
Thus applying e_(a b).hom to tensor restriction gives abstract restriction after
applying e_b.hom. Evaluation as defined here is e_b.inv applied to homSection b:
this follows from pullbackSection_one_eq. The existing homSection_comp theorem
then proves the desired equation for a composite a followed by b. Substitute the
equality g.left followed by U.hom equals V.hom to obtain the same equality
transport on both sides. Finally, etaleHom.map is precisely pullHom restricted
from the category of schemes over X. No quasi-coherence assumption or sheaf
condition is used. Identity arrows and empty schemes are included by the same
adjunction equations; the argument requires no nonempty set of sections. -/
theorem etaleTensorHomEvaluation_naturality {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (etaleHom (unitObj X) F).map g ≫
        TypeCat.ofHom (etaleTensorHomEvaluation F V.unop) =
      TypeCat.ofHom (etaleTensorHomEvaluation F U.unop) ≫
        (etaleTensorSectionsPresheaf F ⋙ CategoryTheory.forget AddCommGrpCat).map g := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
