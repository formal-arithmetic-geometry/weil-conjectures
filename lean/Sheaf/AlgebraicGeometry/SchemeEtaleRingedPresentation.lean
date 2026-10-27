/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.LocallyRingedTopos
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-! # A small presentation of the ringed étale topos of a scheme

Source: Stacks Project, Étale Cohomology, Tags 04HZ and 04I5; Sites, Tag 03A0
(blueprint: def-sfb-scheme-etale-ringed-presentation).

The ring sheaf is restriction of regular functions. The normalization on representables
and their function evaluations specifies the geometric morphism induced by a scheme map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleRinged

/-- The small model of the affine étale basis.
Source: Stacks, Tags 0218 and 03A0
(blueprint: def-sfb-scheme-etale-ringed-presentation). -/
abbrev Site (X : Scheme.{u}) := SmallModel.{u} X.AffineEtale

/-- Inclusion of the chosen affine representatives into the actual étale site.
Source: Stacks, Tag 03A0 (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def inclusion (X : Scheme.{u}) : Site X ⥤ X.Etale :=
  (equivSmallModel X.AffineEtale).inverse ⋙ AffineEtale.Spec X

/-- The induced étale topology on the small affine basis.
Source: Stacks, Tag 03A0 (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
abbrev topology (X : Scheme.{u}) :=
  (equivSmallModel X.AffineEtale).inverse.inducedTopology (AffineEtale.topology X)

/-- Restriction of sheaves to the affine basis and then to its small model.
Source: Stacks, Tag 03A0 (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def restrict (X : Scheme.{u}) (A : Type (u + 1)) [Category.{u} A] :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (topology X) A :=
  (AffineEtale.Spec X).sheafPushforwardContinuous A (AffineEtale.topology X)
      X.smallEtaleTopology ⋙
    (equivSmallModel X.AffineEtale).inverse.sheafPushforwardContinuous A
      (topology X) (AffineEtale.topology X)

/-- The specified equivalence from the full étale topos to this small presentation.
Source: Stacks, Tag 03A0 (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def setEquivalence (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (Type u) ≌ Sheaf (topology X) (Type u) :=
  (AffineEtale.sheafEquiv X (Type u)).symm.trans
    ((equivSmallModel X.AffineEtale).sheafCongr
      (AffineEtale.topology X) (topology X) (Type u))

/-- The commutative structure sheaf, with value Γ(T, O_T) on the represented chart.
Source: Stacks, Tag 04HZ (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def commRing (X : Scheme.{u}) : Sheaf (topology X) CommRingCat.{u} :=
  (restrict X CommRingCat.{u}).obj
    ⟨X.etaleStructurePresheaf, X.isSheaf_etaleStructurePresheaf⟩

/-- The same structure sheaf with commutativity forgotten.
Source: Stacks, Tag 04HZ (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
abbrev ring (X : Scheme.{u}) : Sheaf (topology X) RingCat.{u} :=
  (sheafCompose (topology X) (forget₂ CommRingCat RingCat)).obj (commRing X)

/-- Representable sheaves on the original étale site, restricted to the small basis.
Source: Stacks, Tags 03O4 and 03A0
(blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def representables (X : Scheme.{u}) : X.Etale ⥤ Sheaf (topology X) (Type u) :=
  X.smallEtaleTopology.yoneda ⋙ restrict X (Type u)

/-- Evaluation of a regular function on a representable, by pullback of functions.
Source: Stacks, Tags 04I5 and 04LW
(blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def evaluation (X : Scheme.{u}) (T : X.Etale) (s : Γ(T.left, ⊤)) :
    (representables X).obj T ⟶ ringSheafUnderlying (ring X) :=
  ⟨{ app := fun W ↦ TypeCat.ofHom (fun t ↦ (Scheme.Γ.map t.left.op) s)
     naturality := by
       intro W Z f
       ext t
       change (Scheme.Γ.map t.left.op ≫
         Scheme.Γ.map ((inclusion X).map f.unop).left.op) s =
         (Scheme.Γ.map (((inclusion X).map f.unop).left ≫ t.left).op) s
       rw [← Functor.map_comp, op_comp] }⟩

/-- A ringed geometric morphism between the chosen presentations.
Source: Stacks, Tag 04I5 (blueprint: def-sfb-scheme-etale-ringed-presentation). -/
abbrev Morphism (U V : Scheme.{u}) := RingedToposMorphism (ring U) (ring V)

/-- The canonical normalization for the morphism induced by a scheme map.
The comparison is natural on all étale representables, and its equation fixes the
structural ring map on every regular function, rather than choosing an arbitrary map.
Source: Stacks, Tags 04I5, 03Q1 (4) and 04LW
(blueprint: def-sfb-scheme-etale-ringed-presentation). -/
def Induces {U V : Scheme.{u}} (g : Morphism U V) (a : U ⟶ V) : Prop :=
  ∃ e : representables V ⋙ g.inverse ≅ a.Etale ⋙ representables U,
    ∀ (T : V.Etale) (s : Γ(T.left, ⊤)),
      e.hom.app T ≫ evaluation U (a.Etale.obj T)
          ((Scheme.Γ.map (pullback.fst T.hom a).op) s) =
        g.inverse.map (evaluation V T s) ≫ g.ringMap

/-- A natural isomorphism of inverse images commuting with the structural maps.
Source: Stacks, Modules on Sites, Tag 04IC
(blueprint: def-sfb-scheme-etale-ringed-presentation). -/
structure TwoIso {U V : Scheme.{u}} (g h : Morphism U V) where
  iso : g.inverse ≅ h.inverse
  comm : iso.hom.app (ringSheafUnderlying (ring V)) ≫ h.ringMap = g.ringMap

end AlgebraicGeometry.Scheme.EtaleRinged
