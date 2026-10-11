/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Sections of tensor pullbacks on the small étale site

Source: Stacks Project, Descent, Tag 03DR, equation (35.8.1), restricted to the small
étale site as in Tag 03DU (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The composition isomorphism normalized by the canonical tensor-pullback units.
It is the conjugate of the sectionwise pushforward composition identification.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def tensorSectionsComp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    tensorPullback b ⋙ tensorPullback a ≅ tensorPullback (a ≫ b) :=
  (conjugateIsoEquiv (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))
    ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
      (Classical.choose (exists_tensorPullbackAdjunction a)))).symm
    (pushforwardComp a b).symm

/-- Pullback of global sections by the canonical unit, evaluated at the whole scheme.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def tensorSectionsUnit {A B : Scheme.{u}} (a : A ⟶ B) (G : B.Modules) :
    Γ(G, ⊤) ⟶ Γ((tensorPullback a).obj G, ⊤) :=
  ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app G).app ⊤ ≫
    ((tensorPullback a).obj G).presheaf.map (homOfLE a.preimage_top.ge).op

/-- The restriction `ρ_g(s) = c_{g,u}(g^*s)`, with transport along `g ≫ u = u'`.
The map is an abelian group homomorphism by its type.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def etaleTensorSectionsRestriction {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj F, ⊤) :=
  tensorSectionsUnit g.left ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp g.left U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) g.w)).app ⊤

/-- Restriction is semilinear over the map on global functions.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: the unit is a module morphism into pushforward, whose scalar action is through
`g^♯`. Thus section pullback is additive and semilinear. The composition isomorphism
and the transport are module morphisms on the source scheme, hence are linear there. -/
theorem etaleTensorSectionsRestriction_smul {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (g : V ⟶ U) (a : Γ(U.left, ⊤))
    (s : Γ((tensorPullback U.hom).obj F, ⊤)) :
    etaleTensorSectionsRestriction F g (a • s) =
      g.left.appTop a • etaleTensorSectionsRestriction F g s := by
  sorry

/-- Identity restrictions are identities.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: the unit equation for `c_{id,u}` says that `c_{id,u} ∘ η^{id}` and the identity
of `u^*` have the same conjugate under `u^* ⊣ u_*`. Uniqueness of conjugates makes them
equal. Evaluation on global sections gives the identity law. -/
theorem etaleTensorSectionsRestriction_id {X : Scheme.{u}} (F : X.Modules) (U : X.Etale) :
    etaleTensorSectionsRestriction F (𝟙 U) = 𝟙 _ := by
  sorry

/-- Restrictions compose contravariantly.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial).
Proof: naturality of the unit of `h^* ⊣ h_*` moves `c_{g,u}` past section pullback by
`h`. Evaluating the unit equation of `c_{h,g}` identifies successive section pullbacks
with pullback along `h ≫ g`. The associativity of normalized left-adjoint composition
isomorphisms (lem-sc-left-adjoint-composition-iso-associativity) identifies the two maps
from `h^*g^*u^*F` to `(h ≫ g ≫ u)^*F`. These give `ρ_{h≫g} = ρ_g ≫ ρ_h`. -/
theorem etaleTensorSectionsRestriction_comp {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Etale} (h : W ⟶ V) (g : V ⟶ U) :
    etaleTensorSectionsRestriction F (h ≫ g) =
      etaleTensorSectionsRestriction F g ≫ etaleTensorSectionsRestriction F h := by
  sorry

/-- The presheaf `u ↦ Γ(U,u^*F)`, with the unit-normalized pullback restrictions.
Source: Stacks, Tag 03DR, equation (35.8.1), and Tag 03DU, item 4
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
def etaleTensorSectionsPresheaf {X : Scheme.{u}} (F : X.Modules) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := Γ((tensorPullback U.unop.hom).obj F, ⊤)
  map g := etaleTensorSectionsRestriction F g.unop
  map_id U := etaleTensorSectionsRestriction_id F U.unop
  map_comp g h := etaleTensorSectionsRestriction_comp F h.unop g.unop

end
end AlgebraicGeometry.Scheme.Modules
