/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Mathlib.Topology.Category.Profinite.Limits
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf

/-! # Free restriction and right translations

Source: direct-image stability, paragraph (3), agent-formulated profinite-action
infrastructure, free restriction; Stacks Sites, Tag 00WW for sheaf restriction.
(blueprint: lem-sfb-profinite-action-free-restriction).

The parameter sites, represented group and internal-action category are the existing
ones in `Profinite.CondensedAction.CoherentPresentation`. Only their definitions are
used here, not the existence of a coherent presentation or its equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction.CoherentPresentation

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]

/-- Right translation has continuous coordinates and commutes with left translation.
Source: auxiliary free-restriction construction, paragraph (3), proof step 4
(blueprint: lem-sfb-profinite-action-free-restriction).
Proof: continuity follows from continuous multiplication and the continuous map g.
Equivariance is (a*j)*g(s)=a*(j*g(s)), the associativity law of J. -/
theorem freeRightTranslation_wellDefined (S : Base.{u}) (g : C(parameter S, J)) :
    Continuous (fun x : J × parameter S ↦ (x.1 * g x.2, x.2)) ∧
    (∀ (a j : J) (s : parameter S), (a * j) * g s = a * (j * g s)) := by
  sorry

/-- The actual equivariant continuous map (j,s) ↦ (j*g(s),s).
Source: auxiliary free-restriction construction, paragraph (3), proof step 4
(blueprint: lem-sfb-profinite-action-free-restriction). -/
def freeRightTranslation (S : Base.{u}) (g : C(parameter S, J)) :
    (freeParameter J).obj S ⟶ (freeParameter J).obj S :=
  AsSmall.up.map (ObjectProperty.homMk
    { hom := CompHausLike.ofHom _
        ⟨fun x ↦ (x.1 * g x.2, x.2), (freeRightTranslation_wellDefined J S g).1⟩
      comm := fun a ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact Prod.ext ((freeRightTranslation_wellDefined J S g).2 a x.1 x.2) rfl })

/-- Free parameters carry covering presieves to covering presieves and preserve pullbacks.
The explicit pullback cone has coordinates (j,(a,b)) ↦ (j,a) and (j,(a,b)) ↦ (j,b).
Thus its inverse comparison sends ((j,a),(j,b)) to (j,(a,b)); uniqueness of pullback
maps makes these comparisons natural in the maps to S.
Source: auxiliary free-restriction construction, paragraph (3), proof step 2
(blueprint: lem-sfb-profinite-action-free-restriction).
Proof: in the pullback of H(a) and H(b), equality in J×S says that the two J
coordinates agree and the parameter coordinates lie in A×_S B. The two displayed
coordinate maps are continuous and equivariant and inverse, and commute with both
projections. A lift s_i of s gives a lift (j,s_i) of (j,s), proving covering
preservation. For an empty covering the target and its product with J are empty. -/
theorem freeParameter_site :
    (∀ (S : Base.{u}) (W : Presieve S), W ∈ baseCoverage S →
      W.map (freeParameter J) ∈ coverage J ((freeParameter J).obj S)) ∧
    (∀ (A B S : Profinite.{u}) (a : A ⟶ S) (b : B ⟶ S),
      IsPullback
        ((ContinuousActionParameter.freeAction J).map (CompHausLike.pullback.fst a b))
        ((ContinuousActionParameter.freeAction J).map (CompHausLike.pullback.snd a b))
        ((ContinuousActionParameter.freeAction J).map a)
        ((ContinuousActionParameter.freeAction J).map b)) := by
  sorry

/-- The prescribed free restriction presheaf is already a sheaf.
Source: auxiliary free-restriction construction, paragraph (3), proof step 3;
Stacks Sites, Tag 00WW (blueprint: lem-sfb-profinite-action-free-restriction).
Proof: freeParameter_site identifies all covering pullbacks and preserves covers.
A compatible family in F(H(S_i)) is therefore a matching family on the corresponding
cover of H(S). The sheaf condition of F glues it uniquely. For the empty cover,
H(empty)=empty, and the value of F there is a singleton. -/
theorem freeRestriction_isSheaf
    (F : Sheaf (coverage J).toGrothendieck (Type (u + 1))) :
    Presheaf.IsSheaf baseCoverage.toGrothendieck ((freeParameter J).op ⋙ F.obj) := by
  sorry

/-- Right translations give the unit, multiplication and naturality equations of the
internal left action; composition is written in categorical (left-to-right) order.
Source: auxiliary free-restriction construction, paragraph (3), proof step 4
(blueprint: lem-sfb-profinite-action-free-restriction).
Proof: r_1=id, r_g followed by r_h is r_(gh), and H(f) followed by r_g is
r_(g∘f) followed by H(f), by evaluation at (j,s). Contravariance of F reverses
compositions, giving F(r_g)(F(r_h)x)=F(r_(gh))x and the stated restriction equation. -/
theorem freeRightTranslation_laws
    (F : Sheaf (coverage J).toGrothendieck (Type (u + 1))) :
    (∀ S : Base.{u}, F.obj.map (freeRightTranslation J S 1).op = 𝟙 _) ∧
    (∀ (S : Base.{u}) (g h : C(parameter S, J)),
      F.obj.map (freeRightTranslation J S h).op ≫
          F.obj.map (freeRightTranslation J S g).op =
        F.obj.map (freeRightTranslation J S (g * h)).op) ∧
    (∀ (V S : Base.{u}) (f : V ⟶ S) (g : C(parameter S, J))
        (x : F.obj.obj (op ((freeParameter J).obj S))),
      F.obj.map ((freeParameter J).map f).op
          (F.obj.map (freeRightTranslation J S g).op x) =
        F.obj.map (freeRightTranslation J V (g.comp f.down.hom.hom)).op
          (F.obj.map ((freeParameter J).map f).op x)) := by
  sorry

/-- The functor of free restriction, specified on sections, restrictions, actions and maps.
The natural section identifications exhibit precisely G(F)(S)=F(H(S)); they do not
choose an internal action or a functor from an unnormalized existence assertion.
Source: auxiliary free-restriction construction, paragraph (3), proof steps 3--5
(blueprint: lem-sfb-profinite-action-free-restriction). -/
structure FreeRestriction where
  /-- The asserted functor into the recorded category of internal actions. -/
  functor : Sheaf (coverage J).toGrothendieck (Type (u + 1)) ⥤ Actions J
  /-- The prescribed sections and restriction maps, natural in the parameter. -/
  sections (F : Sheaf (coverage J).toGrothendieck (Type (u + 1))) :
    (functor.obj F).X.obj ≅ (freeParameter J).op ⋙ F.obj
  /-- Under this identification, the action is pullback by actual right translation. -/
  action (F : Sheaf (coverage J).toGrothendieck (Type (u + 1)))
      (S : Base.{u}) (g : (groupPresheaf J).obj (op S))
      (x : (functor.obj F).X.obj.obj (op S)) :
    (sections F).hom.app (op S)
        (InternalActionSite.setAction _ _ _ (functor.obj F) (op S) g x) =
      F.obj.map (freeRightTranslation J S g.down).op ((sections F).hom.app (op S) x)
  /-- A sheaf map acts by its original components on H(S). -/
  maps {F F' : Sheaf (coverage J).toGrothendieck (Type (u + 1))} (α : F ⟶ F')
      (S : Base.{u}) (x : (functor.obj F).X.obj.obj (op S)) :
    (sections F').hom.app (op S) ((functor.map α).hom.hom.app (op S) x) =
      α.hom.app (op ((freeParameter J).obj S)) ((sections F).hom.app (op S) x)

/-- Free restriction and right translation reconstruct the asserted internal-action
functor, with all the displayed section formulas.
Source: auxiliary free-restriction construction, paragraph (3), proof steps 1--5
(blueprint: lem-sfb-profinite-action-free-restriction).
Proof: the represented group is the existing continuous-map group sheaf, by descent
of maps to a profinite space (lem-sfb-profinite-action-finite-cover-site). Step 2,
freeParameter_site, proves preservation of covers and their pullbacks. Step 3,
freeRestriction_isSheaf, applies the matching-family argument of Stacks 00WW to F.
Step 4, freeRightTranslation_laws, supplies the natural unital associative action
on these sections. The definition of InternalActionSite.SetActions packages this
as an internal action. For a sheaf map α use α_(H(S)); its naturality for H(f)
proves compatibility with restrictions, and its naturality for r_g proves
equivariance. Identity and composition hold componentwise, giving the required
functor. All section identifications are the identity, so every normalization holds. -/
theorem freeRestriction_exists : Nonempty (FreeRestriction J) := by
  sorry

end Profinite.CondensedAction.CoherentPresentation
