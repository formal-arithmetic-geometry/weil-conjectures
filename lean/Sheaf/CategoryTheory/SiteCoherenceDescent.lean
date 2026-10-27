/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of comparison pastes on witnessed inputs

Source: Stacks Project, more-etale.tex, Tags 0F7I, 0F7J and 0F7K; the agent's
categorical transport argument (blueprint: lem-sp-site-coherence-descent).

`SiteComparisonData` and `SiteComparisonLaws` package exactly the supplied functors,
refinements, towers and etale coherence. Pro-side maps are natural transformations
only after precomposition with N. `atWitness` extends them by the specified witness;
it does not assert naturality on all pro-side objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vB uB vE uE vP uP vI uI uT

namespace CategoryTheory
namespace WitnessedSiteCoherence

open CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B]
  {E : B → Type uE} [∀ X, Category.{vE} (E X)]
  {P : B → Type uP} [∀ X, Category.{vP} (P X)]
  {I : ∀ {X Y : B}, (X ⟶ Y) → Type uI}
  [∀ {X Y : B} (f : X ⟶ Y), Category.{vI} (I f)]

/-- The supplied comparison, refinement and tower data. Towers have projections
onto the three candidate sets; their common-refinement condition is in the laws.
The equality `w` merely names the composite arrow, allowing both associations of a
triple to have literally the same target candidate.
Source: Stacks Tags 0F7I--0F7K (blueprint: lem-sp-site-coherence-descent). -/
structure SiteComparisonData (B : Type uB) [Category.{vB} B]
    (E : B → Type uE) [∀ X, Category.{vE} (E X)]
    (P : B → Type uP) [∀ X, Category.{vP} (P X)]
    (I : ∀ {X Y : B}, (X ⟶ Y) → Type uI)
    [∀ {X Y : B} (f : X ⟶ Y), Category.{vI} (I f)] where
  N : ∀ X, E X ⥤ P X
  Fe : ∀ {X Y : B} (f : X ⟶ Y), I f → E X ⥤ E Y
  Fp : ∀ {X Y : B} (f : X ⟶ Y), I f → P X ⥤ P Y
  C : ∀ {X Y : B} (f : X ⟶ Y) (c : I f), (Fe f c ⋙ N Y) ≅ (N X ⋙ Fp f c)
  re : ∀ {X Y : B} {f : X ⟶ Y} {c d : I f}, (d ⟶ c) → (Fe f c ≅ Fe f d)
  rp : ∀ {X Y : B} {f : X ⟶ Y} {c d : I f},
    (d ⟶ c) → (N X ⋙ Fp f c ⟶ N X ⋙ Fp f d)
  te : ∀ {X Y : B} (f : X ⟶ Y) (c d : I f), Fe f c ≅ Fe f d
  ae : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z},
    (f ≫ g = k) → ∀ (c : I f) (d : I g) (e : I k), (Fe f c ⋙ Fe g d) ≅ Fe k e
  ue : ∀ (X : B) (c : I (𝟙 X)), Fe (𝟙 X) c ≅ 𝟭 (E X)
  up : ∀ (X : B) (c : I (𝟙 X)), Fp (𝟙 X) c ≅ 𝟭 (P X)
  Tower : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z},
    (f ≫ g = k) → Type uT
  first : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k}, Tower f g w → I f
  second : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k}, Tower f g w → I g
  output : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k}, Tower f g w → I k
  ap : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k} (t : Tower f g w),
    ((N X ⋙ Fp f (first t)) ⋙ Fp g (second t) ⟶ N X ⋙ Fp k (output t))

variable (S : SiteComparisonData.{vB, uB, vE, uE, vP, uP, vI, uI, uT} B E P I)

/-- Extension of an image-component map to an explicitly witnessed object.
Source: Stacks Tags 0F7I--0F7K, witness convention of the categorical argument
(blueprint: lem-sp-site-coherence-descent). -/
def atWitness {X Y : B} {U V : P X ⥤ P Y}
    (a : S.N X ⋙ U ⟶ S.N X ⋙ V) (A : E X) {M : P X}
    (ξ : (S.N X).obj A ≅ M) : U.obj M ⟶ V.obj M :=
  U.map ξ.inv ≫ a.app A ≫ V.map ξ.hom

/-- The canonical comparison on image inputs, with actual inverse data.
Source: Stacks Tag 0F7I (blueprint: lem-sp-site-coherence-descent). -/
def change {X Y : B} (f : X ⟶ Y) (c d : I f) :
    (S.N X ⋙ S.Fp f c) ≅ (S.N X ⋙ S.Fp f d) :=
  (S.C f c).symm ≪≫ isoWhiskerRight (S.te f c d) (S.N Y) ≪≫ S.C f d

/-- Input comparison for a binary composite on the image of N.
Source: Stacks Tag 0F7J (blueprint: lem-sp-site-coherence-descent). -/
def binaryComparison {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : I f) (d : I g) :
    ((S.Fe f c ⋙ S.Fe g d) ⋙ S.N Z) ≅ ((S.N X ⋙ S.Fp f c) ⋙ S.Fp g d) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (S.C g d) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (S.C f c) _

/-- Transport of the descended etale compositor through C. This is a comparison
object, not the definition of the computed tower paste.
Source: Stacks Tag 0F7J (blueprint: lem-sp-site-coherence-descent). -/
def transportedComposition {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (c : I f) (d : I g) (e : I k) :
    (S.N X ⋙ (S.Fp f c ⋙ S.Fp g d)) ≅ (S.N X ⋙ S.Fp k e) :=
  (Functor.associator _ _ _).symm ≪≫ (binaryComparison S f g c d).symm ≪≫
    isoWhiskerRight (S.ae f g w c d e) _ ≪≫ S.C k e

/-- Changing the two input candidates; the second change is evaluated at the
specified C_f witness, rather than at an unwitnessed pro-side object.
Source: Stacks Tags 0F7I and 0F7J (blueprint: lem-sp-site-coherence-descent). -/
def inputChange {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : I f) (d d' : I g) (A : E X) :
    (S.Fp g d).obj ((S.Fp f c).obj ((S.N X).obj A)) ⟶
      (S.Fp g d').obj ((S.Fp f c').obj ((S.N X).obj A)) :=
  atWitness S (change S g d d').hom ((S.Fe f c).obj A) ((S.C f c).app A) ≫
    (S.Fp g d').map ((change S f c c').hom.app A)

/-- The computed paste obtained by moving the chosen candidates to a supplied
compatible tower, applying its computed pro map, and returning to the output.
Source: Stacks Tag 0F7J (blueprint: lem-sp-site-coherence-descent). -/
def towerPaste {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w)
    (A : E X) : (S.Fp g d).obj ((S.Fp f c).obj ((S.N X).obj A)) ⟶
      (S.Fp k e).obj ((S.N X).obj A) :=
  inputChange S f g c (S.first t) d (S.second t) A ≫ (S.ap t).app A ≫
    (change S k (S.output t) e).hom.app A

/-- The computed tower paste at a specified witness, by the node's conjugation
convention, without replacing the computed map by a transported etale map.
Source: Stacks Tags 0F7I--0F7K (blueprint: lem-sp-site-coherence-descent). -/
def towerAtWitness {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M) :=
  (S.Fp g d).map ((S.Fp f c).map ξ.inv) ≫ towerPaste S f g c d e t A ≫
    (S.Fp k e).map ξ.hom

/-- A chosen common source produces the literal pro-side refinement paste. Each
leg is inverted through C and the supplied etale refinement, using actual data.
Source: Stacks Tag 0F7I (blueprint: lem-sp-site-coherence-descent). -/
def commonPaste {X Y : B} {f : X ⟶ Y} {c d r : I f}
    (a : r ⟶ c) (b : r ⟶ d) : S.N X ⋙ S.Fp f c ⟶ S.N X ⋙ S.Fp f d :=
  S.rp a ≫ (S.C f r).inv ≫ whiskerRight (S.re b).inv (S.N Y) ≫ (S.C f d).hom

/-- The triple comparison D, in diagrammatic order.
Source: Stacks Tag 0F7K (blueprint: lem-sp-site-coherence-descent). -/
def tripleComparison {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (A : E X) :=
  (S.C h e).hom.app ((S.Fe g d).obj ((S.Fe f c).obj A)) ≫
    (S.Fp h e).map ((S.C g d).hom.app ((S.Fe f c).obj A)) ≫
    (S.Fp h e).map ((S.Fp g d).map ((S.C f c).hom.app A))

/-- Precisely the node's hypotheses: cofilteredness, etale choice independence,
descent, associativity and units, the refinement/tower squares, and C_id=1 under
its given unit identifications. No full/faithful/essentially-surjective assumption.
Source: Stacks Tags 0F7I--0F7K (blueprint: lem-sp-site-coherence-descent). -/
structure SiteComparisonLaws : Prop where
  cofiltered : ∀ {X Y : B} (f : X ⟶ Y), IsCofiltered (I f)
  te_id : ∀ {X Y : B} (f : X ⟶ Y) (c : I f), S.te f c c = Iso.refl _
  te_comp : ∀ {X Y : B} (f : X ⟶ Y) (c d e : I f),
    S.te f c d ≪≫ S.te f d e = S.te f c e
  te_refine : ∀ {X Y : B} {f : X ⟶ Y} {c d : I f} (a : d ⟶ c),
    S.re a = S.te f c d
  refinement_square : ∀ {X Y : B} {f : X ⟶ Y} {c d : I f} (a : d ⟶ c) (A : E X),
    (S.N Y).map ((S.re a).hom.app A) ≫ (S.C f d).hom.app A =
      (S.C f c).hom.app A ≫ (S.rp a).app A
  tower_nonempty : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k), Nonempty (S.Tower f g w)
  common_tower : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k} (t t' : S.Tower f g w), ∃ r : S.Tower f g w,
      Nonempty (S.first r ⟶ S.first t) ∧ Nonempty (S.first r ⟶ S.first t') ∧
      Nonempty (S.second r ⟶ S.second t) ∧ Nonempty (S.second r ⟶ S.second t') ∧
      Nonempty (S.output r ⟶ S.output t) ∧ Nonempty (S.output r ⟶ S.output t')
  etale_descent : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (c c' : I f) (d d' : I g) (e e' : I k),
    isoWhiskerRight (S.te f c c') (S.Fe g d) ≪≫
        isoWhiskerLeft (S.Fe f c') (S.te g d d') ≪≫ S.ae f g w c' d' e' =
      S.ae f g w c d e ≪≫ S.te k e e'
  tower_square : ∀ {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    {w : f ≫ g = k} (t : S.Tower f g w) (A : E X),
    (S.N Z).map ((S.ae f g w (S.first t) (S.second t) (S.output t)).hom.app A) ≫
        (S.C k (S.output t)).hom.app A =
      (binaryComparison S f g (S.first t) (S.second t)).hom.app A ≫ (S.ap t).app A
  etale_assoc : ∀ {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (a : I (f ≫ g)) (b : I (g ≫ h))
    (q : I ((f ≫ g) ≫ h)) (A : E X),
    (S.Fe h e).map ((S.ae f g rfl c d a).hom.app A) ≫
        (S.ae (f ≫ g) h rfl a e q).hom.app A =
      (S.ae g h rfl d e b).hom.app ((S.Fe f c).obj A) ≫
        (S.ae f (g ≫ h) (Category.assoc f g h).symm c b q).hom.app A
  etale_left_unit : ∀ {X Y : B} (f : X ⟶ Y) (i : I (𝟙 X)) (c : I f),
    (S.ae (𝟙 X) f (Category.id_comp f) i c c).hom =
      whiskerRight (S.ue X i).hom (S.Fe f c)
  etale_right_unit : ∀ {X Y : B} (f : X ⟶ Y) (c : I f) (i : I (𝟙 Y)),
    (S.ae f (𝟙 Y) (Category.comp_id f) c i c).hom =
      whiskerLeft (S.Fe f c) (S.ue Y i).hom
  identity_square : ∀ (X : B) (i : I (𝟙 X)) (A : E X),
    (S.C (𝟙 X) i).hom.app A ≫ (S.up X i).hom.app ((S.N X).obj A) =
      (S.N X).map ((S.ue X i).hom.app A)


/-- Left triple path, extended to an arbitrary specified witness.
Source: Stacks Tag 0F7K (blueprint: lem-sp-site-coherence-descent). -/
def tripleLeft {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (a : I (f ≫ g)) (q : I ((f ≫ g) ≫ h))
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M) :=
  (S.Fp h e).map
      (atWitness S (transportedComposition S f g rfl c d a).hom A ξ) ≫
    atWitness S (transportedComposition S (f ≫ g) h rfl a e q).hom A ξ

/-- Right triple path, retaining the intermediate witness P_f(ξ) C_f(A).
Source: Stacks Tag 0F7K (blueprint: lem-sp-site-coherence-descent). -/
def tripleRight {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (b : I (g ≫ h)) (q : I ((f ≫ g) ≫ h))
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M) :=
  atWitness S (transportedComposition S g h rfl d e b).hom ((S.Fe f c).obj A)
      ((S.C f c).app A ≪≫ (S.Fp f c).mapIso ξ) ≫
    atWitness S
      (transportedComposition S f (g ≫ h) (Category.assoc f g h).symm c b q).hom A ξ

/-- The full descent and coherence conclusion, only on image or witnessed inputs.
The transport comparisons in these clauses are identified with the computed tower
pastes by `descent`; no pro-side coherence is built into the hypotheses.
Source: Stacks Tags 0F7I--0F7K (blueprint: lem-sp-site-coherence-descent). -/
structure SiteComparisonConclusion : Prop where
  refinement : ∀ {X Y : B} {f : X ⟶ Y} {c d : I f} (r : d ⟶ c) (A : E X),
    IsIso ((S.rp r).app A) ∧
      (S.rp r).app A = (S.C f c).inv.app A ≫
        (S.N Y).map ((S.re r).hom.app A) ≫ (S.C f d).hom.app A
  common_refinement : ∀ {X Y : B} {f : X ⟶ Y} {c d r : I f}
    (a : r ⟶ c) (b : r ⟶ d), commonPaste S a b = (change S f c d).hom
  change_identity : ∀ {X Y : B} (f : X ⟶ Y) (c : I f),
    change S f c c = Iso.refl _
  change_cocycle : ∀ {X Y : B} (f : X ⟶ Y) (c d e : I f),
    change S f c d ≪≫ change S f d e = change S f c e
  refinement_identity : ∀ {X Y : B} {f : X ⟶ Y} (c : I f),
    S.rp (𝟙 c) = 𝟙 _
  refinement_composition : ∀ {X Y : B} {f : X ⟶ Y} {c d e : I f}
    (a : d ⟶ c) (b : e ⟶ d), S.rp (b ≫ a) = S.rp a ≫ S.rp b
  descent : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w) (A : E X),
    towerPaste S f g c d e t A = (transportedComposition S f g w c d e).hom.app A
  witnessed_descent : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    towerAtWitness S f g c d e t A ξ =
      atWitness S (transportedComposition S f g w c d e).hom A ξ ∧
    IsIso (towerAtWitness S f g c d e t A ξ)
  tower_independence : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k)
    (t t' : S.Tower f g w) (A : E X),
    towerPaste S f g c d e t A = towerPaste S f g c d e t' A
  composition_square : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w) (A : E X),
    (binaryComparison S f g c d).hom.app A ≫ towerPaste S f g c d e t A =
      (S.N Z).map ((S.ae f g w c d e).hom.app A) ≫ (S.C k e).hom.app A
  composition_invertible : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w) (A : E X),
    IsIso (towerPaste S f g c d e t A)
  naturality : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k) (t : S.Tower f g w)
    {A A' : E X} (a : A ⟶ A'),
    (S.Fp g d).map ((S.Fp f c).map ((S.N X).map a)) ≫
        towerPaste S f g c d e t A' =
      towerPaste S f g c d e t A ≫ (S.Fp k e).map ((S.N X).map a)
  triple_formula : ∀ {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (a : I (f ≫ g)) (b : I (g ≫ h))
    (q : I ((f ≫ g) ≫ h)) (A : E X),
    tripleComparison S f g h c d e A ≫
        tripleLeft S f g h c d e a q A (Iso.refl _) =
      (S.N W).map ((S.Fe h e).map ((S.ae f g rfl c d a).hom.app A) ≫
        (S.ae (f ≫ g) h rfl a e q).hom.app A) ≫ (S.C ((f ≫ g) ≫ h) q).hom.app A ∧
    tripleComparison S f g h c d e A ≫
        tripleRight S f g h c d e b q A (Iso.refl _) =
      (S.N W).map ((S.Fe h e).map ((S.ae f g rfl c d a).hom.app A) ≫
        (S.ae (f ≫ g) h rfl a e q).hom.app A) ≫ (S.C ((f ≫ g) ≫ h) q).hom.app A
  witnessed_associativity : ∀ {X Y Z W : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (a : I (f ≫ g)) (b : I (g ≫ h))
    (q : I ((f ≫ g) ≫ h)) (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    tripleLeft S f g h c d e a q A ξ = tripleRight S f g h c d e b q A ξ
  witnessed_left_unit : ∀ {X Y : B} (f : X ⟶ Y) (i : I (𝟙 X)) (c : I f)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    atWitness S (transportedComposition S (𝟙 X) f (Category.id_comp f) i c c).hom A ξ =
      (S.Fp f c).map ((S.up X i).hom.app M)
  witnessed_right_unit : ∀ {X Y : B} (f : X ⟶ Y) (c : I f) (i : I (𝟙 Y))
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    atWitness S (transportedComposition S f (𝟙 Y) (Category.comp_id f) c i c).hom A ξ =
      (S.up Y i).hom.app ((S.Fp f c).obj M)
  witnessed_change_identity : ∀ {X Y : B} (f : X ⟶ Y) (c : I f)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    atWitness S (change S f c c).hom A ξ = 𝟙 _
  witnessed_change_cocycle : ∀ {X Y : B} (f : X ⟶ Y) (c d e : I f)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    atWitness S (change S f c d).hom A ξ ≫ atWitness S (change S f d e).hom A ξ =
      atWitness S (change S f c e).hom A ξ
  witnessed_change_invertible : ∀ {X Y : B} (f : X ⟶ Y) (c d : I f)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    IsIso (atWitness S (change S f c d).hom A ξ)
  witnessed_composition_invertible : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (c : I f) (d : I g) (e : I k)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M),
    IsIso (atWitness S (transportedComposition S f g w c d e).hom A ξ)
  witness_naturality : ∀ {X Y : B} {U V : P X ⥤ P Y}
    (a : S.N X ⋙ U ⟶ S.N X ⋙ V) {A A' : E X} (e : A ⟶ A')
    {M M' : P X} (ξ : (S.N X).obj A ≅ M) (ξ' : (S.N X).obj A' ≅ M')
    (m : M ⟶ M'), ξ.hom ≫ m = (S.N X).map e ≫ ξ'.hom →
      U.map m ≫ atWitness S a A' ξ' = atWitness S a A ξ ≫ V.map m

private lemma change_refl (laws : SiteComparisonLaws S)
    {X Y : B} (f : X ⟶ Y) (c : I f) : change S f c c = Iso.refl _ := by
  ext A
  simp [change, laws.te_id]

private lemma change_trans (laws : SiteComparisonLaws S)
    {X Y : B} (f : X ⟶ Y) (c d e : I f) :
    change S f c d ≪≫ change S f d e = change S f c e := by
  have h := congrArg (fun t => t.hom) (laws.te_comp f c d e)
  ext A
  have ha := congrArg (fun t => (S.N Y).map (t.app A)) h
  simpa [change, Functor.map_comp, Category.assoc] using
    congrArg (fun t => (S.C f c).inv.app A ≫ t ≫ (S.C f e).hom.app A) ha

private lemma refinement_eq (laws : SiteComparisonLaws S)
    {X Y : B} {f : X ⟶ Y} {c d : I f} (r : d ⟶ c) :
    S.rp r = (change S f c d).hom := by
  ext A
  apply (cancel_epi ((S.C f c).hom.app A)).1
  simpa [change, laws.te_refine, Category.assoc] using
    (laws.refinement_square r A).symm

private lemma witness_comp {X Y : B} {U V W : P X ⥤ P Y}
    (a : S.N X ⋙ U ⟶ S.N X ⋙ V) (b : S.N X ⋙ V ⟶ S.N X ⋙ W)
    (A : E X) {M : P X} (ξ : (S.N X).obj A ≅ M) :
    atWitness S a A ξ ≫ atWitness S b A ξ = atWitness S (a ≫ b) A ξ := by
  simp [atWitness, Category.assoc]

private lemma witness_iso {X Y : B} {U V : P X ⥤ P Y}
    (a : S.N X ⋙ U ≅ S.N X ⋙ V) (A : E X) {M : P X}
    (ξ : (S.N X).obj A ≅ M) : IsIso (atWitness S a.hom A ξ) := by
  dsimp [atWitness]
  infer_instance

private lemma composition_app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (c : I f) (d : I g) (e : I k) (A : E X) :
    (transportedComposition S f g w c d e).hom.app A =
      (S.Fp g d).map ((S.C f c).inv.app A) ≫
        (S.C g d).inv.app ((S.Fe f c).obj A) ≫
        (S.N Z).map ((S.ae f g w c d e).hom.app A) ≫ (S.C k e).hom.app A := by
  simp [transportedComposition, binaryComparison]

private lemma composition_square {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (c : I f) (d : I g) (e : I k) (A : E X) :
    (binaryComparison S f g c d).hom.app A ≫
        (transportedComposition S f g w c d e).hom.app A =
      (S.N Z).map ((S.ae f g w c d e).hom.app A) ≫ (S.C k e).hom.app A := by
  simp [composition_app, binaryComparison, Category.assoc,
    -Functor.map_comp, ← Functor.map_comp_assoc]

private lemma input_square {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c c' : I f) (d d' : I g) (A : E X) :
    (binaryComparison S f g c d).hom.app A ≫ inputChange S f g c c' d d' A =
      (S.N Z).map ((S.te g d d').hom.app ((S.Fe f c).obj A) ≫
        (S.Fe g d').map ((S.te f c c').hom.app A)) ≫
        (binaryComparison S f g c' d').hom.app A := by
  simp only [binaryComparison, inputChange, atWitness, change,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp, Category.assoc]
  simp only [Iso.app_hom, Iso.app_inv, ← Functor.map_comp_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (S.C g d').hom.naturality ((S.te f c c').hom.app A)
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun v => (S.N Z).map ((S.te g d d').hom.app ((S.Fe f c).obj A)) ≫
      v ≫ (S.Fp g d').map ((S.C f c').hom.app A)) hn.symm

private lemma descent_eq (laws : SiteComparisonLaws S)
    {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    {w : f ≫ g = k} (c : I f) (d : I g) (e : I k)
    (t : S.Tower f g w) (A : E X) :
    towerPaste S f g c d e t A = (transportedComposition S f g w c d e).hom.app A := by
  apply (cancel_epi ((binaryComparison S f g c d).hom.app A)).1
  rw [composition_square]
  dsimp only [towerPaste]
  rw [← Category.assoc, ← Category.assoc, input_square]
  simp only [Category.assoc]
  rw [← Category.assoc ((binaryComparison S f g (S.first t) (S.second t)).hom.app A)
    ((S.ap t).app A), ← laws.tower_square t A, change]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  have h := congrArg (fun i => (S.N Z).map (i.hom.app A))
    (laws.etale_descent f g w c (S.first t) d (S.second t) e (S.output t))
  have hc := congrArg (fun i => i.hom.app A)
    (laws.te_comp k e (S.output t) e)
  have hc' : (S.te k e (S.output t)).hom.app A ≫
      (S.te k (S.output t) e).hom.app A = 𝟙 _ := by
    simpa [laws.te_id] using hc
  have hh := congrArg (fun v => v ≫
    (S.N Z).map ((S.te k (S.output t) e).hom.app A) ≫ (S.C k e).hom.app A) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app] at hh
  rw [(S.te g d (S.second t)).hom.naturality_assoc ((S.te f c (S.first t)).hom.app A)] at hh
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [← Functor.map_comp_assoc (S.N Z) ((S.te k e (S.output t)).hom.app A)
    ((S.te k (S.output t) e).hom.app A), hc', Functor.map_id, Category.id_comp] at hh
  simpa only [Functor.map_comp, Category.assoc] using hh

private lemma identity_app (laws : SiteComparisonLaws S) (X : B)
    (i : I (𝟙 X)) (A : E X) :
    (S.C (𝟙 X) i).inv.app A ≫ (S.N X).map ((S.ue X i).hom.app A) =
      (S.up X i).hom.app ((S.N X).obj A) := by
  apply (cancel_epi ((S.C (𝟙 X) i).hom.app A)).1
  simpa [Category.assoc] using (laws.identity_square X i A).symm

private lemma triple_left_formula {X Y Z W : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (a : I (f ≫ g)) (q : I ((f ≫ g) ≫ h))
    (A : E X) :
    tripleComparison S f g h c d e A ≫
        tripleLeft S f g h c d e a q A (Iso.refl _) =
      (S.N W).map ((S.Fe h e).map ((S.ae f g rfl c d a).hom.app A) ≫
        (S.ae (f ≫ g) h rfl a e q).hom.app A) ≫
          (S.C ((f ≫ g) ≫ h) q).hom.app A := by
  simp only [Functor.comp_obj, tripleComparison, tripleLeft, atWitness, Iso.refl_inv,
    Functor.comp_map, Functor.map_id, composition_app, Iso.refl_hom, Category.comp_id,
    Category.id_comp, ← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  have hn := (S.C h e).hom.naturality ((S.ae f g rfl c d a).hom.app A)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc ((S.C h e).hom.app _) ((S.Fp h e).map _), ← hn]
  simp [Category.assoc, Functor.map_comp]

private lemma triple_right_formula {X Y Z W : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (c : I f) (d : I g) (e : I h) (b : I (g ≫ h)) (q : I ((f ≫ g) ≫ h))
    (A : E X) :
    tripleComparison S f g h c d e A ≫
        tripleRight S f g h c d e b q A (Iso.refl _) =
      (S.N W).map ((S.ae g h rfl d e b).hom.app ((S.Fe f c).obj A) ≫
        (S.ae f (g ≫ h) (Category.assoc f g h).symm c b q).hom.app A) ≫
          (S.C ((f ≫ g) ≫ h) q).hom.app A := by
  simp [tripleComparison, tripleRight, atWitness, composition_app,
    Category.assoc, -Functor.map_comp, ← Functor.map_comp_assoc]

/-- Descent, invertibility, naturality, units and associativity of comparison pastes
on the supplied witnessed inputs.
Source: Stacks Project, more-etale.tex, Tags 0F7I, 0F7J and 0F7K; agent categorical
transport argument (blueprint: lem-sp-site-coherence-descent).

Proof (the ten steps of the DAG node):
1. Work componentwise. Functors preserve inverses, and an isomorphism may be
cancelled by composing with its inverse; no cancellation through N is used.
2. Solve the refinement square: rp = C_c^{-1} N(re) C_d in diagrammatic order.
This also gives its inverse. Substitute into a zigzag; adjacent C inverses cancel.
3. A common-source paste is C_c^{-1} N(re_a re_b^{-1}) C_d. Etale independence
and cocycles therefore give pro independence, identity and cocycles.
4. On a tower, solve its square for ap using the invertible binary comparison B.
5. Under an input change, witness conjugation moves the change past C_f. Naturality
of C_g and the two refinement squares identify the input paste times B with B'
followed, in functional notation, by N of the etale input change. The output change
has the analogous square with C_gf. Inverse comparisons satisfy these squares too.
6. Substitute both squares into the computed tower paste. Etale descent leaves
exactly B^{-1} N(ae) C_gf. This proves tower independence, the composition equation
and invertibility for every candidate triple, and naturality follows by pasting.
7. Precompose the left triple path with D. Substitute the binary equation twice;
naturality of C_h at ae_gf identifies the result with C_hgf N(ae_triple).
8. For the right path, use witness naturality at C_f, then the same binary equation.
Etale associativity identifies its result with the left path's result; cancel D.
9. Identity normalization and etale units make the unit composites the specified
unit identifications. Every displayed factor and its inverse is natural in E.
10. At a witness ξ conjugate the component by the images of ξ and ξ^{-1}.
Adjacent witness factors cancel in composites. The intermediate witness is
C_f(A) followed by P_f(ξ). Thus all equations and invertibility extend to these
inputs, naturally under their specified changes of witness, without any assertion
about unrelated witnesses or arbitrary pro-side naturality.
-/
theorem siteCoherenceDescent (laws : SiteComparisonLaws S) : SiteComparisonConclusion S := by
  refine {
    refinement := ?_
    common_refinement := ?_
    change_identity := change_refl S laws
    change_cocycle := change_trans S laws
    refinement_identity := ?_
    refinement_composition := ?_
    descent := descent_eq S laws
    witnessed_descent := ?_
    tower_independence := ?_
    composition_square := ?_
    composition_invertible := ?_
    naturality := ?_
    triple_formula := ?_
    witnessed_associativity := ?_
    witnessed_left_unit := ?_
    witnessed_right_unit := ?_
    witnessed_change_identity := ?_
    witnessed_change_cocycle := ?_
    witnessed_change_invertible := ?_
    witnessed_composition_invertible := ?_
    witness_naturality := ?_ }
  · intro X Y f c d r A
    rw [refinement_eq S laws r]
    constructor
    · infer_instance
    · simp [change, laws.te_refine]
  · intro X Y f c d r a b
    calc
      commonPaste S a b = (change S f c r).hom ≫ (change S f d r).inv := by
        simp [commonPaste, refinement_eq S laws, change, laws.te_refine, Category.assoc]
      _ = (change S f c d).hom := by
        apply (cancel_mono (change S f d r).hom).1
        simpa using (congrArg Iso.hom (change_trans S laws f c d r)).symm
  · intro X Y f c
    rw [refinement_eq S laws, change_refl S laws]
    rfl
  · intro X Y f c d e a b
    simp only [refinement_eq S laws]
    exact (congrArg Iso.hom (change_trans S laws f c d e)).symm
  · intro X Y Z f g k w c d e t A M ξ
    constructor
    · simp only [towerAtWitness, descent_eq S laws, atWitness, Functor.comp_map]
    · simpa only [towerAtWitness, descent_eq S laws, atWitness, Functor.comp_map] using
        witness_iso S (transportedComposition S f g w c d e) A ξ
  · intro X Y Z f g k w c d e t t' A
    rw [descent_eq S laws, descent_eq S laws]
  · intro X Y Z f g k w c d e t A
    rw [descent_eq S laws]
    exact composition_square S f g w c d e A
  · intro X Y Z f g k w c d e t A
    rw [descent_eq S laws]
    infer_instance
  · intro X Y Z f g k w c d e t A A' a
    simp only [descent_eq S laws]
    exact (transportedComposition S f g w c d e).hom.naturality a
  · intro X Y Z W f g h c d e a b q A
    constructor
    · exact triple_left_formula S f g h c d e a q A
    · rw [triple_right_formula, ← laws.etale_assoc f g h c d e a b q A]
  · intro X Y Z W f g h c d e a b q A M ξ
    have hi : tripleLeft S f g h c d e a q A (Iso.refl _) =
        tripleRight S f g h c d e b q A (Iso.refl _) := by
      have : IsIso (tripleComparison S f g h c d e A) := by
        dsimp [tripleComparison]
        infer_instance
      apply (cancel_epi (tripleComparison S f g h c d e A)).1
      rw [triple_left_formula, triple_right_formula,
        ← laws.etale_assoc f g h c d e a b q A]
    simpa [tripleLeft, tripleRight, atWitness, Category.assoc,
      -Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp_assoc] using
      congrArg (fun t => (S.Fp h e).map ((S.Fp g d).map ((S.Fp f c).map ξ.inv)) ≫
        t ≫ (S.Fp ((f ≫ g) ≫ h) q).map ξ.hom) hi
  · intro X Y f i c A M ξ
    have hl := congrArg (fun t => t.app A) (laws.etale_left_unit f i c)
    simp only [whiskerRight_app] at hl
    simp only [atWitness, composition_app, hl, Functor.comp_map, Category.assoc]
    have hn := (S.C f c).hom.naturality_assoc ((S.ue X i).hom.app A)
      ((S.Fp f c).map ξ.hom)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp only [Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp]
    rw [← Category.assoc ((S.C (𝟙 X) i).inv.app A), identity_app S laws]
    rw [← Category.assoc, (S.up X i).hom.naturality ξ.inv]
    simp
  · intro X Y f c i A M ξ
    have hr := congrArg (fun t => t.app A) (laws.etale_right_unit f c i)
    simp only [whiskerLeft_app] at hr
    simp only [atWitness, composition_app, hr, Functor.comp_map, Category.assoc]
    rw [← Category.assoc ((S.C (𝟙 Y) i).inv.app _) ((S.N Y).map _),
      identity_app S laws]
    have hn := (S.up Y i).hom.naturality ((S.C f c).inv.app A)
    dsimp only [Functor.comp_obj, Functor.id_map] at hn
    rw [← Category.assoc ((S.Fp (𝟙 Y) i).map ((S.C f c).inv.app A)), hn]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc, (S.up Y i).hom.naturality ((S.Fp f c).map ξ.inv)]
    simp [Category.assoc, ← Functor.map_comp]
  · intro X Y f c A M ξ
    simp [change_refl S laws, atWitness, ← Functor.map_comp]
  · intro X Y f c d e A M ξ
    rw [witness_comp]
    rw [← Iso.trans_hom, change_trans S laws]
  · intro X Y f c d A M ξ
    exact witness_iso S (change S f c d) A ξ
  · intro X Y Z f g k w c d e A M ξ
    exact witness_iso S (transportedComposition S f g w c d e) A ξ
  · intro X Y U V a A A' e M M' ξ ξ' m h
    have hu : m ≫ ξ'.inv = ξ.inv ≫ (S.N X).map e := by
      apply (cancel_epi ξ.hom).1
      simpa [Category.assoc] using congrArg (fun t => t ≫ ξ'.inv) h
    have hv : ξ.hom ≫ m = (S.N X).map e ≫ ξ'.hom := h
    dsimp only [atWitness]
    rw [← Category.assoc, ← U.map_comp, hu, U.map_comp]
    simp only [Category.assoc]
    have hn := a.naturality_assoc e (V.map ξ'.hom)
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [← V.map_comp, hv]


end WitnessedSiteCoherence
end CategoryTheory
