module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-! # Relative rational and birational maps

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.5 and 5.2, printed pp.118--119
(blueprint: def-sfb-relative-birational-maps).

Relative partial maps use fibrewise density, unlike Mathlib's absolute partial maps.
Birational charts are actual isomorphisms of open subschemes. Their quotient uses agreement
on a fibrewise dense common open. The composition and pullback predicates specify the
canonical operations without choosing representatives or postponing any data construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace RelativeBirational

variable {S : Scheme.{u}}

/-- Fibrewise density of an open. Source: BLR 2.5 and 5.2
(blueprint: def-sfb-relative-birational-maps). -/
def FibrewiseDense {X : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) : Prop :=
  ∀ s : S, Dense ((p.fiberι s) ⁻¹' (U : Set X))

/-- A relative partial map, with a fibrewise dense open domain and a base equation.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-maps). -/
structure PartialMap (X Y : Over S) where
  domain : X.left.Opens
  dense_fibres : FibrewiseDense X.hom domain
  hom : domain.toScheme ⟶ Y.left
  over : hom ≫ Y.hom = domain.ι ≫ X.hom

/-- Agreement on a fibrewise dense common open. Source: BLR 2.5
(blueprint: def-sfb-relative-birational-maps). -/
def PartialMap.Agrees {X Y : Over S} (f g : PartialMap X Y) : Prop :=
  ∃ (H : X.left.Opens) (_ : FibrewiseDense X.hom H)
    (hf : H ≤ f.domain) (hg : H ≤ g.domain),
    X.left.homOfLE hf ≫ f.hom = X.left.homOfLE hg ≫ g.hom

/-- Relative rational maps are partial maps modulo dense agreement. `Quot` takes the
same quotient as the equivalence relation of common-open agreement; it requires no
choice of representatives. Source: BLR 2.5
(blueprint: def-sfb-relative-birational-maps). -/
def RationalMap (X Y : Over S) : Type u := Quot (@PartialMap.Agrees _ X Y)

/-- An isomorphism of two fibrewise dense opens, over the base.
Source: BLR 2.5 and 5.2 (blueprint: def-sfb-relative-birational-maps). -/
structure Chart (X : Over S) where
  domain : X.left.Opens
  codomain : X.left.Opens
  dense_domain : FibrewiseDense X.hom domain
  dense_codomain : FibrewiseDense X.hom codomain
  iso : domain.toScheme ≅ codomain.toScheme
  over : iso.hom ≫ codomain.ι ≫ X.hom = domain.ι ≫ X.hom

/-- Agreement of birational charts as scheme morphisms on a common dense open.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-maps). -/
def Chart.Agrees {X : Over S} (f g : Chart X) : Prop :=
  ∃ (H : X.left.Opens) (_ : FibrewiseDense X.hom H)
    (hf : H ≤ f.domain) (hg : H ≤ g.domain),
    X.left.homOfLE hf ≫ f.iso.hom ≫ f.codomain.ι =
      X.left.homOfLE hg ≫ g.iso.hom ≫ g.codomain.ι

/-- Birational self-maps modulo fibrewise dense agreement.
Source: BLR 5.2, construction preceding Lemma 4
(blueprint: def-sfb-relative-birational-maps). -/
def SelfMap (X : Over S) : Type u := Quot (@Chart.Agrees _ X)

/-- The class of a specified chart. Source: BLR 5.2, preceding Lemma 4
(blueprint: def-sfb-relative-birational-maps). -/
def Chart.toSelfMap {X : Over S} (f : Chart X) : SelfMap X := Quot.mk _ f

/-- `h` represents `f ∘ g`: on a common fibrewise dense open, the image under `g`
lifts into the domain of `f`, and the composite equals `h` as a scheme morphism.
Source: BLR 2.5 and 5.2 (blueprint: def-sfb-relative-birational-maps). -/
def IsComposite {X : Over S} (f g h : Chart X) : Prop :=
  ∃ (H : X.left.Opens) (_ : FibrewiseDense X.hom H)
    (hg : H ≤ g.domain) (hh : H ≤ h.domain) (v : H.toScheme ⟶ f.domain.toScheme),
    X.left.homOfLE hg ≫ g.iso.hom ≫ g.codomain.ι = v ≫ f.domain.ι ∧
    X.left.homOfLE hh ≫ h.iso.hom ≫ h.codomain.ι = v ≫ f.iso.hom ≫ f.codomain.ι

/-- A chart is the scheme-theoretic pullback of another chart. Domain and codomain
are the full inverse-image opens; both inclusions and the isomorphism commute with
base change. Source: BLR 2.5 and 5.2
(blueprint: def-sfb-relative-birational-maps). -/
def IsPullback (Y : Over S) {T T' : Over S} (g : T' ⟶ T)
    (f : Chart ((Over.pullback T.hom).obj Y))
    (f' : Chart ((Over.pullback T'.hom).obj Y)) : Prop :=
  f'.domain = (baseChangeMap Y.hom g) ⁻¹ᵁ f.domain ∧
  f'.codomain = (baseChangeMap Y.hom g) ⁻¹ᵁ f.codomain ∧
  ∃ (a : f'.domain.toScheme ⟶ f.domain.toScheme)
    (b : f'.codomain.toScheme ⟶ f.codomain.toScheme),
    a ≫ f.domain.ι = f'.domain.ι ≫ baseChangeMap Y.hom g ∧
    b ≫ f.codomain.ι = f'.codomain.ι ≫ baseChangeMap Y.hom g ∧
    f'.iso.hom ≫ b = a ≫ f.iso.hom

end RelativeBirational

end AlgebraicGeometry
