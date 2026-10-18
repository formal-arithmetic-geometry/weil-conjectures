/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Fine log structures and their étale descent data

Source: ILO, Exposé VI 1.1 and Exposé VIII 3.3.4(ii), 3.3.8; Stacks, Tags 04TR and 04TQ
(blueprint: def-trf-fine-log-etale-descent-datum).

Overlap maps are evaluated on every étale test object with two lifts to the covering.
By the universal property of the fibre product these are exactly the objects on the
double-overlap site. Three lifts similarly describe triple overlaps. The existing
`Scheme.Etale.overToEtale` identifies localized sites with the local small étale sites.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Étale-local charts by finitely generated integral monoids. Source: ILO VI 1.1
(blueprint: def-trf-fine-log-etale-descent-datum). -/
def EtaleLogStructure.IsFine {X : Scheme.{u}} (M : EtaleLogStructure X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (W : X.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (P : Type u) (_ : CommMonoid P) (β : P →* M.monoidSheaf.obj.obj (op W)),
      Monoid.FG P ∧ Function.Injective (Algebra.GrothendieckGroup.of (M := P)) ∧ M.IsChart W β

/-- Sections on a localized étale object, using the recorded site equivalence.
Source: ILO VIII 3.3.8; Stacks, Tag 00Y0
(blueprint: def-trf-fine-log-etale-descent-datum). -/
abbrev EtalePrelogStructure.localSections {T : Scheme.{u}} {U V : T.Etale}
    (M : EtalePrelogStructure U.left) (f : V ⟶ U) : CommMonCat.{u} :=
  M.monoidSheaf.obj.obj (op ((Scheme.Etale.overToEtale U).obj (Over.mk f)))

/-- Restriction of localized sections. Source: Stacks, Tags 00Y0 and 03EH
(blueprint: def-trf-fine-log-etale-descent-datum). -/
def EtalePrelogStructure.localMap {T : Scheme.{u}} {U V W : T.Etale}
    (M : EtalePrelogStructure U.left) (f : V ⟶ U) (g : W ⟶ V) :
    M.localSections f ⟶ M.localSections (g ≫ f) :=
  M.monoidSheaf.obj.map
    ((Scheme.Etale.overToEtale U).map (Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f)).op

/-- The local structural map on precisely the same test object. Source: ILO VI 1.1
(blueprint: def-trf-fine-log-etale-descent-datum). -/
abbrev EtalePrelogStructure.localAlpha {T : Scheme.{u}} {U V : T.Etale}
    (M : EtalePrelogStructure U.left) (f : V ⟶ U) :=
  M.alpha.app (op ((Scheme.Etale.overToEtale U).obj (Over.mk f)))

/-- Fine log structures with structure-preserving overlap isomorphisms, their naturality,
diagonal normalization and triple cocycle. Source: ILO VIII 3.3.8; Stacks, Tag 04TR
(blueprint: def-trf-fine-log-etale-descent-datum). -/
structure FineLogEtaleDescentDatum {T : Scheme.{u}} {ι : Type v} (U : ι → T.Etale) where
  localLog : ∀ a, EtaleLogStructure (U a).left
  fine : ∀ a, (localLog a).IsFine
  transition : ∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b),
    (localLog a).toEtalePrelogStructure.localSections f ≃*
      (localLog b).toEtalePrelogStructure.localSections g
  naturality : ∀ (a b : ι) (V W : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b)
    (k : W ⟶ V) (s : (localLog a).toEtalePrelogStructure.localSections f),
    transition a b W (k ≫ f) (k ≫ g)
        ((localLog a).toEtalePrelogStructure.localMap f k s) =
      (localLog b).toEtalePrelogStructure.localMap g k (transition a b V f g s)
  alpha : ∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b)
    (s : (localLog a).toEtalePrelogStructure.localSections f),
    (localLog b).toEtalePrelogStructure.localAlpha g (transition a b V f g s) =
      (localLog a).toEtalePrelogStructure.localAlpha f s
  diagonal : ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a),
    transition a a V f f = MulEquiv.refl _
  cocycle : ∀ (a b c : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b) (h : V ⟶ U c)
    (s : (localLog a).toEtalePrelogStructure.localSections f),
    transition b c V g h (transition a b V f g s) = transition a c V f h s

/-- A global log structure with labelled local identifications inducing exactly the datum.
Source: ILO VIII 3.3.8; Stacks, Tag 04TR
(blueprint: def-trf-fine-log-etale-descent-datum). -/
structure FineLogEtaleDescentDatum.Gluing {T : Scheme.{u}} {ι : Type v} {U : ι → T.Etale}
    (D : FineLogEtaleDescentDatum U) (M : EtaleLogStructure T) where
  component : ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a),
    M.monoidSheaf.obj.obj (op V) ≃* (D.localLog a).toEtalePrelogStructure.localSections f
  naturality : ∀ (a : ι) (V W : T.Etale) (f : V ⟶ U a) (k : W ⟶ V)
    (s : M.monoidSheaf.obj.obj (op V)),
    component a W (k ≫ f) (M.monoidSheaf.obj.map k.op s) =
      (D.localLog a).toEtalePrelogStructure.localMap f k (component a V f s)
  alpha : ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a) (s : M.monoidSheaf.obj.obj (op V)),
    (D.localLog a).toEtalePrelogStructure.localAlpha f (component a V f s) = M.alpha.app (op V) s
  transition : ∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b)
    (s : M.monoidSheaf.obj.obj (op V)),
    D.transition a b V f g (component a V f s) = component b V g s

/-- An isomorphism of arbitrary prelog monoid sheaves over the structure sheaf.
Source: ILO VI 1.1; Stacks, Tag 04TQ
(blueprint: def-trf-fine-log-etale-descent-datum). -/
structure EtalePrelogStructure.Iso {T : Scheme.{u}} (A B : EtalePrelogStructure T) where
  iso : A.monoidSheaf.obj ≅ B.monoidSheaf.obj
  alpha : iso.hom ≫ B.alpha = A.alpha

/-- A homomorphism of arbitrary prelog monoid sheaves over the structure sheaf.
Source: ILO VI 1.1; Stacks, Tag 04TQ
(blueprint: def-trf-fine-log-etale-descent-datum). -/
structure EtalePrelogStructure.Hom {T : Scheme.{u}} (A B : EtalePrelogStructure T) where
  hom : A.monoidSheaf.obj ⟶ B.monoidSheaf.obj
  alpha : hom ≫ B.alpha = A.alpha

/-- A homomorphism on the localized site, without a log axiom on either sheaf.
Source: Stacks, Tags 00Y0 and 04TQ
(blueprint: def-trf-fine-log-etale-descent-datum). -/
structure EtalePrelogStructure.LocalHom {T : Scheme.{u}} (A B : EtalePrelogStructure T)
    (U : T.Etale) where
  hom : (A.monoidSheaf.over U).obj ⟶ (B.monoidSheaf.over U).obj
  alpha : ∀ (V : Over U) (s : A.monoidSheaf.obj.obj (op V.left)),
    B.alpha.app (op V.left) (hom.app (op V) s) = A.alpha.app (op V.left) s

end AlgebraicGeometry
