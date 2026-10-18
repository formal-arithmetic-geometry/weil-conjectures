/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fine log schemes and their morphisms

Source: ILO, Exposé VI 1.1 and VIII 3.3.8
(blueprint: def-trf-fine-log-scheme-morphisms).

The relative étale test presentation of `EtaleLogHom` is extended to fine log schemes,
without saturation. A strict étale map identifies the source log sheaf with the restriction
of the target log sheaf. Since an étale localization is a slice site, this is tested on
relative diagrams whose map between the underlying test schemes is an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A log map over a fixed scheme map, in the relative-test-object presentation of
`f⁻¹ M → N`. This is the same interface as `EtaleLogHom`, without an fs hypothesis.
Source: ILO VI 1.1 (blueprint: def-trf-fine-log-scheme-morphisms). -/
structure EtaleLogStructure.HomAlong {Y X : Scheme.{u}}
    (N : EtaleLogStructure Y) (M : EtaleLogStructure X) (f : Y ⟶ X) where
  sectionMap : ∀ (W : X.Etale) (V : Y.Etale)
    (k : V.left ⟶ W.left) (_hk : k ≫ W.hom = V.hom ≫ f),
    M.monoidSheaf.obj.obj (op W) →* N.monoidSheaf.obj.obj (op V)
  naturality : ∀ (W₁ W₂ : X.Etale) (V₁ V₂ : Y.Etale)
    (a : W₁ ⟶ W₂) (c : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ W₁.left)
    (k₂ : V₂.left ⟶ W₂.left)
    (h₁ : k₁ ≫ W₁.hom = V₁.hom ≫ f) (h₂ : k₂ ≫ W₂.hom = V₂.hom ≫ f),
    c.left ≫ k₂ = k₁ ≫ a.left →
      (N.monoidSheaf.obj.map c.op).hom.comp (sectionMap W₂ V₂ k₂ h₂) =
        (sectionMap W₁ V₁ k₁ h₁).comp (M.monoidSheaf.obj.map a.op).hom
  compatibility : ∀ (W : X.Etale) (V : Y.Etale)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f)
    (s : M.monoidSheaf.obj.obj (op W)),
    N.alpha.app (op V) (sectionMap W V k hk s) = k.appTop (M.alpha.app (op W) s)

/-- Equality with a composite, including the underlying scheme-map equation.
It suffices to test composable relative diagrams, since every test diagram factors
through the base change of its target neighbourhood.
Source: ILO VI 1.1, VIII 3.3.8 (blueprint: def-trf-fine-log-scheme-morphisms). -/
def EtaleLogStructure.HomAlong.CompEq {Z Y X : Scheme.{u}}
    {P : EtaleLogStructure Z} {N : EtaleLogStructure Y} {M : EtaleLogStructure X}
    {h : Z ⟶ Y} {b : Y ⟶ X} {f : Z ⟶ X}
    (H : P.HomAlong N h) (B : N.HomAlong M b) (F : P.HomAlong M f) : Prop :=
  h ≫ b = f ∧
    ∀ (W : X.Etale) (V : Y.Etale) (T : Z.Etale)
      (k : V.left ⟶ W.left) (l : T.left ⟶ V.left) (m : T.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ b)
      (hl : l ≫ V.hom = T.hom ≫ h) (hm : m ≫ W.hom = T.hom ≫ f),
      l ≫ k = m → (H.sectionMap V T l hl).comp (B.sectionMap W V k hk) =
        F.sectionMap W T m hm

/-- Strictness for an étale underlying morphism. An isomorphism of the test schemes
identifies the restricted structural rings, so bijectivity is exactly strictness,
including the associated-log-structure unit normalization.
Source: ILO VI 1.1 (blueprint: def-trf-fine-log-scheme-morphisms). -/
def EtaleLogStructure.HomAlong.IsStrictEtale {Y X : Scheme.{u}}
    {N : EtaleLogStructure Y} {M : EtaleLogStructure X} {f : Y ⟶ X}
    (H : N.HomAlong M f) : Prop :=
  Etale f ∧ ∀ (W : X.Etale) (V : Y.Etale) (k : V.left ⟶ W.left)
    [IsIso k] (hk : k ≫ W.hom = V.hom ≫ f),
    Function.Bijective (H.sectionMap W V k hk)

/-- Fine log schemes, with the locally Noetherian convention of ILO VI 1.1.
Source: ILO VI 1.1 (blueprint: def-trf-fine-log-scheme-morphisms). -/
structure FineLogScheme where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  logStructure : EtaleLogStructure scheme
  fine : logStructure.IsFine

/-- A morphism of fine log schemes. Source: ILO VI 1.1
(blueprint: def-trf-fine-log-scheme-morphisms). -/
structure FineLogScheme.Hom (Y X : FineLogScheme.{u}) where
  base : Y.scheme ⟶ X.scheme
  logMap : Y.logStructure.HomAlong X.logStructure base

/-- Equality with a composite of fine log morphisms. Source: ILO VI 1.1
(blueprint: def-trf-fine-log-scheme-morphisms). -/
def FineLogScheme.Hom.CompEq {Z Y X : FineLogScheme.{u}}
    (h : Z.Hom Y) (b : Y.Hom X) (f : Z.Hom X) : Prop :=
  h.logMap.CompEq b.logMap f.logMap

/-- Equality of two composites through possibly different middle schemes, tested on
all relative étale diagrams. Source: ILO VI 1.1, VIII 3.3.8
(blueprint: def-trf-fine-log-scheme-morphisms). -/
def FineLogScheme.Hom.CompositesEq {T Y Y' Z : FineLogScheme.{u}}
    (a : T.Hom Y) (b : Y.Hom Z) (a' : T.Hom Y') (b' : Y'.Hom Z) : Prop :=
  a.base ≫ b.base = a'.base ≫ b'.base ∧
    ∀ (W : Z.scheme.Etale) (V : Y.scheme.Etale) (V' : Y'.scheme.Etale)
      (Q : T.scheme.Etale) (k : V.left ⟶ W.left) (l : Q.left ⟶ V.left)
      (k' : V'.left ⟶ W.left) (l' : Q.left ⟶ V'.left)
      (hk : k ≫ W.hom = V.hom ≫ b.base) (hl : l ≫ V.hom = Q.hom ≫ a.base)
      (hk' : k' ≫ W.hom = V'.hom ≫ b'.base) (hl' : l' ≫ V'.hom = Q.hom ≫ a'.base),
      l ≫ k = l' ≫ k' →
        (a.logMap.sectionMap V Q l hl).comp (b.logMap.sectionMap W V k hk) =
          (a'.logMap.sectionMap V' Q l' hl').comp (b'.logMap.sectionMap W V' k' hk')

/-- Sections on an étale test scheme, using the recorded small étale site.
Source: ILO VI 1.1 (blueprint: def-trf-fine-log-scheme-morphisms). -/
abbrev EtaleLogStructure.sectionsAt {X T : Scheme.{u}} (M : EtaleLogStructure X)
    (p : T ⟶ X) [Etale p] : CommMonCat.{u} :=
  M.monoidSheaf.obj.obj (op (Scheme.Etale.mk p))

/-- Restriction along a map between étale test schemes, using the original sheaf map.
Source: ILO VI 1.1 (blueprint: def-trf-fine-log-scheme-morphisms). -/
def EtaleLogStructure.restrictAt {X T T' : Scheme.{u}} (M : EtaleLogStructure X)
    (p : T ⟶ X) [Etale p] (h : T' ⟶ T) [Etale (h ≫ p)] :
    M.sectionsAt p ⟶ M.sectionsAt (h ≫ p) :=
  M.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk h rfl : Scheme.Etale.mk (h ≫ p) ⟶ Scheme.Etale.mk p).op

end AlgebraicGeometry
