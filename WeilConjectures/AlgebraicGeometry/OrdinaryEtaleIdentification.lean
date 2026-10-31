/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Ordinary modules identified on an etale chart

Source: Stacks Project, Descent, Tags 03DR, 03DU and 05VG;
Properties of Spaces, Tag 03M3; Spaces, Tag 04W8
(blueprint: def-sfb-ordinary-etale-identification).

These are the existing section restriction, overlap transport, and natural linear
identification definitions, moved here without changing their names, signatures or data.
They apply to arbitrary modules; no invertibility or descent theorem is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of sections of ordinary pullbacks along a commuting scheme triangle.
The formula uses the canonical tensor-pullback unit and its unit-normalized composition
isomorphism, followed by transport along the triangle equation.
Source: Stacks, Descent, Tags 03DR and 05VG
(blueprint: def-sfb-ordinary-etale-identification). -/
noncomputable def ordinaryEtaleSectionRestriction {X Y Z : Scheme.{u}}
    (L : Z.Modules) (p : Y ⟶ Z) (f : X ⟶ Y) (p' : X ⟶ Z) (h : f ≫ p = p') :
    Γ((tensorPullback p).obj L, ⊤) ⟶ Γ((tensorPullback p').obj L, ⊤) :=
  tensorSectionsUnit f ((tensorPullback p).obj L) ≫
    ((tensorSectionsComp f p).hom.app L).app ⊤ ≫
    (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj L) h)).app ⊤

/-- Pull an overlap isomorphism back to a test scheme, identifying the two iterated
pullbacks by the canonical composition comparisons and the specified leg equations.
Source: Stacks, Spaces, Tag 04W8; Descent, Tag 03DR
(blueprint: def-sfb-ordinary-etale-identification). -/
noncomputable def atlasTransitionOn {X Y R T : Scheme.{u}}
    (L : X.Modules) (K : Y.Modules) (p : R ⟶ X) (q : R ⟶ Y)
    (α : (tensorPullback q).obj K ≅ (tensorPullback p).obj L)
    (r : T ⟶ R) (a : T ⟶ X) (b : T ⟶ Y) (ha : r ≫ p = a) (hb : r ≫ q = b) :
    (tensorPullback b).obj K ≅ (tensorPullback a).obj L :=
  (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj K) hb)).symm ≪≫
    ((tensorSectionsComp r q).app K).symm ≪≫
    (tensorPullback r).mapIso α ≪≫ (tensorSectionsComp r p).app L ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj L) ha)

/-- The same canonical transition on schemes over the fixed base, retaining the leg
identities in the over category. Source: Stacks, Spaces, Tag 04W8
(blueprint: def-sfb-ordinary-etale-identification). -/
noncomputable def atlasTransitionOver {S : Scheme.{u}} {X Y R T : Over S}
    (L : X.left.Modules) (K : Y.left.Modules) (p : R ⟶ X) (q : R ⟶ Y)
    (α : (tensorPullback q.left).obj K ≅ (tensorPullback p.left).obj L)
    (r : T ⟶ R) (a : T ⟶ X) (b : T ⟶ Y) (ha : r ≫ p = a) (hb : r ≫ q = b) :
    (tensorPullback b.left).obj K ≅ (tensorPullback a.left).obj L :=
  atlasTransitionOn L K p.left q.left α r.left a.left b.left
    (congrArg (fun f : T ⟶ X ↦ f.left) ha) (congrArg (fun f : T ⟶ Y ↦ f.left) hb)
/-- An identification of an ordinary module on the scheme `V` with the restriction of
an algebraic-space module `N` to `V`. On a test object `p : T ⟶ V` it is a linear
isomorphism `Γ(T, p*L) ≃ N(T)`, natural for every morphism in the localized étale site.
Thus it is precisely an isomorphism with the ordinary module's associated étale module,
with its scalar action included, rather than merely an isomorphism of abelian sheaves.
Source: Stacks, Descent, Tags 03DU and 05VG
(blueprint: def-sfb-ordinary-etale-identification). -/
structure OrdinaryEtaleIdentification {S : Scheme.{u}} (F : AlgebraicSpace S)
    (V : F.EtaleSite) (N : F.Modules) (L : (F.etaleForget.obj V).Modules) where
  /-- The sectionwise linear isomorphisms. -/
  app : ∀ (T : F.EtaleSite) (p : T ⟶ V),
    ((tensorPullback (F.etaleForget.map p)).obj L).val.obj (op ⊤) ≃ₗ[
      Γ(F.etaleForget.obj T, ⊤)] N.val.obj (op T)
  /-- Naturality for the canonical ordinary pullback restrictions. -/
  naturality : ∀ (T U : F.EtaleSite) (p : T ⟶ V) (f : U ⟶ T)
    (s : ((tensorPullback (F.etaleForget.map p)).obj L).val.obj (op ⊤)),
    app U (f ≫ p)
      (ordinaryEtaleSectionRestriction L (F.etaleForget.map p) (F.etaleForget.map f)
        (F.etaleForget.map (f ≫ p)) (F.etaleForget.map_comp f p).symm s) =
      N.val.presheaf.map f.op (app T p s)

end AlgebraicGeometry.AlgebraicSpace
