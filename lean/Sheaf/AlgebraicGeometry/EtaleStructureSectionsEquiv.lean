/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import Mathlib.Algebra.Category.Grp.Ulift
import Sheaf.AlgebraicGeometry.EtaleTensorSections

/-!
# Canonical sections of the lifted étale structure-module sheaf

Source: Stacks Tags 0096, 01CA, 03DR, 03DU; the restriction-identification step of
blueprint `lem-sc-as-sequence-construction-helper`.
-/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate the adjoint structure-module isomorphism on the top open.
Source: Stacks Tags 0096 and 01CA
(blueprint: lem-sc-as-sequence-construction-helper-restriction). -/
noncomputable def tensorStructureSectionsEquiv {A B : Scheme.{u}} (f : A ⟶ B) :
    Γ((Scheme.Modules.tensorPullback f).obj (SheafOfModules.unit B.ringCatSheaf), ⊤) ≃+
      Γ(A, ⊤) := by
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit f) :=
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).1
  exact AddEquiv.ofBijective
    ((Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤).hom
    (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.tensorPullbackObjUnitToUnit f).app ⊤))

/-- Remove the universe lift and identify pullback sections with regular functions.
Source: Stacks Tags 0096, 01CA, 03DR, 03DU
(blueprint: lem-sc-as-sequence-construction-helper-restriction). -/
noncomputable def etaleStructureSectionsEquiv (C : Scheme.{u}) (U : C.Etaleᵒᵖ) :
    ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.obj U ≃+
        Γ(U.unop.left, ⊤) :=
  AddEquiv.ulift.trans (tensorStructureSectionsEquiv U.unop.hom)

/-- The canonical section identifications commute with étale restrictions.
Source: blueprint `lem-sc-as-sequence-construction-helper`, proof step 3;
Stacks Tags 0096 and 01CA (adjoint structure map), 03DR equation (35.8.1),
and 03DU item 4 (the étale sections presheaf).
(blueprint: lem-sc-as-sequence-construction-helper-restriction)

Proof: Write epsilon_u for the adjoint structure-module map. The normalized
composition isomorphism c_{g,u} is the conjugate of the pushforward composition
identification. Its unit equation and the defining adjunction equation of epsilon
show that c_{g,u} followed by epsilon_{g >> u} equals g^*(epsilon_u) followed by
epsilon_g: apply the composite adjunction Hom bijection; use unit naturality and
then the two equations eta_u >> u_*(epsilon_u) = u-sharp and
eta_g >> g_*(epsilon_g) = g-sharp. The resulting composite structure map is
(g >> u)-sharp, so injectivity of the Hom bijection proves equality. Transport
along the site relation g >> u = v preserves epsilon by equality elimination.
Evaluate at the top open, where inverse image of top is top and the induced
restriction is the identity. Naturality of eta_g moves epsilon_u past section
pullback. The equation for epsilon_g then identifies the remaining composite
with g-sharp. Finally, ULift.down commutes with the lifted map, giving the
stated identity. This also covers the empty scheme, identities and composites;
no nonemptiness or characteristic assumption is used. -/
theorem etaleStructureSectionsEquiv_naturality (C : Scheme.{u})
    (U V : C.Etaleᵒᵖ) (g : U ⟶ V)
    (x : ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.obj U) :
    etaleStructureSectionsEquiv C V
      (((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C))).obj.map g x) =
      g.unop.left.appTop (etaleStructureSectionsEquiv C U x) := by
  sorry

end AlgebraicGeometry
