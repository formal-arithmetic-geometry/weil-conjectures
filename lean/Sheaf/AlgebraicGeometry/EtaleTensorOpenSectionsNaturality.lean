/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Canonical open-section comparisons and restriction compatibility

Source: Stacks Project, Tags 03DR, 0095 and 0096.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The canonical tensor-to-restriction comparison on the whole open subscheme.
Source: Stacks, Tags 0095 and 0096; uniqueness of left adjoints and
Mathlib `restrictAppIso` (blueprint: new-etale-tensor-open-section-iso). -/
def tensorOpenSectionIso (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) :
    Γ((tensorPullback U.ι).obj F, ⊤) ≅ Γ(F, U) :=
  ((CategoryTheory.evaluation _ AddCommGrpCat).obj (op ⊤)).mapIso
      ((toPresheaf U.toScheme).mapIso
        (((Classical.choose (exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
          (restrictAdjunction U.ι)).app F)) ≪≫
    F.restrictAppIso U.ι ⊤ ≪≫
    F.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- Transport the canonical open-section comparison along the equality of
underlying over-scheme objects. No section is chosen from an existence assertion.
Source: Stacks, Tag 03DR (blueprint: new-etale-tensor-open-section-iso). -/
def etaleTensorOpenSectionIso (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules)
    (U : X.Opensᵒᵖ) :
    (i.op ⋙ etaleTensorSectionsPresheaf F).obj U ≅
      (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).obj U :=
  eqToIso (congrArg (fun T : Over X ↦ Γ((tensorPullback T.hom).obj F, ⊤))
      (congrArg (fun k : X.Opens ⥤ Over X ↦ k.obj U.unop) hi)) ≪≫
    tensorOpenSectionIso X F U.unop

/-- The constructed comparisons commute with the unit-normalized tensor restrictions.
Source: Stacks, Tag 03DR, equation (35.8.0.1), and Tags 0095 and 0096.
(blueprint: new-etale-tensor-open-section-naturality).

Proof: First use hi on objects and arrows to replace the underlying objects i(U)
by the inclusions U.ι and each underlying arrow by the inclusion between opens.
Write a for the inclusion V into U and b for U.ι. Let e_b be the unique comparison
from tensor pullback to restriction defined by leftAdjointUniq. Its unit equation
is η_b followed by b_* e_b = the restriction-adjunction unit. The composition
comparison c_{a,b} is the mate of the inverse pushforward-composition isomorphism.
Its unit equation identifies η_b followed by b_* η_a and the pushforward of
c_{a,b} with η_{a≫b}, after the pushforward composition identification.
Combine these equations: section pullback along a, followed by c_{a,b} and e_{a≫b},
is e_b followed by the restriction unit along a and the restriction-composition
comparison. Equality follows by injectivity of the adjunction Hom equivalence;
both mates are the same composite restriction unit. Evaluate at the whole source
open. Mathlib restrictAdjunction_unit_app_app expresses the restriction unit as
the ordinary presheaf restriction, while restrictAppIso identifies the whole-open
sections with F(U) and F(V). The transports of image-top and a≫b=V.ι commute with
these maps by functoriality of F.presheaf. This gives the displayed square. Empty
opens, identity inclusions, and zero modules obey the same unit equations. -/
theorem etaleTensorOpenSectionIso_naturality
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (i.op ⋙ etaleTensorSectionsPresheaf F).map f ≫
        (etaleTensorOpenSectionIso X i hi F V).hom =
      (etaleTensorOpenSectionIso X i hi F U).hom ≫
        (F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map f := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
