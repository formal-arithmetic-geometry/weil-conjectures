/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.SpaceUniversalConormal
public import Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.AlgebraicGeometry.SpaceStalkIdealPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Universal conormal transitivity and etale charts

Source: Stacks Project, More on Morphisms of Spaces, Tags 060A, 060D, 0605(1), 06BF
(blueprint: lem-sfb-universal-conormal-chart-transitivity).

Universal thickenings are arbitrary specified representatives. Their maps and conormal
maps are selected only from unique, normalized universal properties. The quotient arrow
is normalized on ideal sections, without inserting an identity tensor pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A specified universal thickening, packaging the existing universal-property predicate.
Source: Stacks, Tag 0601 (blueprint: lem-sfb-universal-conormal-chart-transitivity). -/
structure UniversalConormalThickening {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) where
  ambient : AlgebraicSpace S
  inclusion : Z ⟶ ambient
  projection : ambient ⟶ X
  universal : IsUniversalSpaceFirstOrderThickening f inclusion projection

/-- The conormal of this specified universal thickening, using the existing ideal kernel.
Source: Stacks, Tag 0607 (blueprint: lem-sfb-universal-conormal-chart-transitivity). -/
abbrev UniversalConormalThickening.conormal {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    {f : Z ⟶ X} (D : UniversalConormalThickening f) : Z.Modules :=
  spaceConormal D.inclusion

/-- A square induces a unique map between its specified universal thickenings.
Source: Stacks, Tag 060A (blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node step 1): regard the source inclusion as a first-order test over the target
base. Its reduction is the source-to-target map followed by the target inclusion.
The target universal property gives exactly the two equations and uniqueness. -/
theorem universalConormalThickening_map_existsUnique {S : Scheme.{u}}
    {Z X Y B : AlgebraicSpace S} {f : Z ⟶ X} {g : Y ⟶ B}
    (D : UniversalConormalThickening f) (E : UniversalConormalThickening g)
    (a : Z ⟶ Y) (b : X ⟶ B) (w : a ≫ g = f ≫ b) :
    ∃! t : D.ambient ⟶ E.ambient,
      D.inclusion ≫ t = a ≫ E.inclusion ∧ t ≫ E.projection = D.projection ≫ b := by
  sorry

/-- The unique map extending a square, not an arbitrary ambient map.
Source: Stacks, Tag 060A (blueprint: lem-sfb-universal-conormal-chart-transitivity). -/
def UniversalConormalThickening.map {S : Scheme.{u}}
    {Z X Y B : AlgebraicSpace S} {f : Z ⟶ X} {g : Y ⟶ B}
    (D : UniversalConormalThickening f) (E : UniversalConormalThickening g)
    (a : Z ⟶ Y) (b : X ⟶ B) (w : a ≫ g = f ≫ b) : D.ambient ⟶ E.ambient :=
  Classical.choose (universalConormalThickening_map_existsUnique D E a b w)

/-- The induced ideal map with the existing local-ideal-tensor normalization.
Source: Stacks, Tags 060A and 0607
(blueprint: lem-sfb-universal-conormal-chart-transitivity). -/
def UniversalConormalThickening.conormalMap {S : Scheme.{u}}
    {Z X Y B : AlgebraicSpace S} {f : Z ⟶ X} {g : Y ⟶ B}
    (D : UniversalConormalThickening f) (E : UniversalConormalThickening g)
    (a : Z ⟶ Y) (b : X ⟶ B) (w : a ≫ g = f ≫ b) :
    (moduleTensorPullback a).obj E.conormal ⟶ D.conormal :=
  Classical.choose (space_conormal_map a (D.map E a b w) D.inclusion E.inclusion
    D.universal.1 E.universal.1
    (Classical.choose_spec (universalConormalThickening_map_existsUnique D E a b w)).1.1)

/-- Canonical maps extend their squares and the ideal maps have the specified normalization.
Source: Stacks, Tags 060A and 0607
(blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node steps 1 and 7): take the defining unique extension and the unique ideal map
of lem-sfb-space-universal-conormal. Their defining properties give all three clauses. -/
theorem universalConormalThickening_map_spec {S : Scheme.{u}}
    {Z X Y B : AlgebraicSpace S} {f : Z ⟶ X} {g : Y ⟶ B}
    (D : UniversalConormalThickening f) (E : UniversalConormalThickening g)
    (a : Z ⟶ Y) (b : X ⟶ B) (w : a ≫ g = f ≫ b) :
    D.inclusion ≫ D.map E a b w = a ≫ E.inclusion ∧
      D.map E a b w ≫ E.projection = D.projection ≫ b ∧
      IsSpaceConormalMap a (D.map E a b w) D.inclusion E.inclusion
        (D.conormalMap E a b w) := by
  sorry

/-- Composition preserves formal unramifiedness, hence has a universal thickening.
Source: Stacks, Tag 06BF, with the defining square-zero uniqueness test
(blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node step 1): two lifts into Z first agree in Y by formal unramifiedness of v,
then agree in Z by that of u. Apply lem-sfb-space-universal-conormal for existence. -/
theorem space_formallyUnramified_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (a : Z ⟶ Y) (b : Y ⟶ X) (ha : SpaceFormallyUnramified a)
    (hb : SpaceFormallyUnramified b) :
    SpaceFormallyUnramified (a ≫ b) ∧ Nonempty (UniversalConormalThickening (a ≫ b)) := by
  sorry

/-- The identity-source ideal map is uniquely the quotient on actual ideal sections.
The ambient map is the canonical map from the thickening over Y to that over X.
Source: Stacks, Tags 06BF and 060A
(blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node steps 2 and 3): the commuting quotient-ring square maps the source kernel
to the target kernel. Pull back to Z and use square-zero scalar actions. On a chart
this sends an ideal section to its ring-map image. These formulas glue; local ideal
tensors generate the conormal, giving uniqueness. This is the identity-source case
of lem-sfb-space-universal-conormal's canonical ideal map, with the identity tensor
comparison removed by multiplication. -/
theorem universalConormalQuotient_existsUnique {S : Scheme.{u}}
    {Z Y X : AlgebraicSpace S} (a : Z ⟶ Y) (b : Y ⟶ X)
    (D : UniversalConormalThickening (a ≫ b)) (E : UniversalConormalThickening a) :
    ∃! ρ : D.conormal ⟶ E.conormal,
      ∀ (U : Z.EtaleSite) (B : E.ambient.EtaleSite) (A : D.ambient.EtaleSite)
        (r : B.obj.left ⟶ A.obj.left)
        (_hr : yoneda.map r ≫ A.obj.hom =
          B.obj.hom ≫ (E.map D (𝟙 Z) b (Category.id_comp (a ≫ b))).hom.hom)
        (s : U.obj.left ⟶ B.obj.left)
        (hs : yoneda.map s ≫ B.obj.hom = U.obj.hom ≫ E.inclusion.hom.hom)
        (t : U.obj.left ⟶ A.obj.left)
        (ht : yoneda.map t ≫ A.obj.hom = U.obj.hom ≫ D.inclusion.hom.hom),
        s ≫ r = t → ∀ (m : (spaceKernel D.inclusion).val.obj (op A))
          (n : (spaceKernel E.inclusion).val.obj (op B)),
          (kernel.ι (moduleStructureMap E.inclusion)).val.app (op B) n =
            (forget₂ CommRingCat RingCat).map (Scheme.Γ.map r.left.op)
              ((kernel.ι (moduleStructureMap D.inclusion)).val.app (op A) m) →
          ρ.val.app (op U) (spaceConormalSection D.inclusion U A t ht m) =
            spaceConormalSection E.inclusion U B s hs n := by
  sorry

/-- The uniquely normalized quotient map, with its source literally C(Z/X).
Source: Stacks, Tag 06BF (blueprint: lem-sfb-universal-conormal-chart-transitivity). -/
def universalConormalQuotient {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (a : Z ⟶ Y) (b : Y ⟶ X)
    (D : UniversalConormalThickening (a ≫ b)) (E : UniversalConormalThickening a) :
    D.conormal ⟶ E.conormal :=
  Classical.choose (universalConormalQuotient_existsUnique a b D E)

/-- The intermediate universal thickening and the canonical right exact sequence.
The pullback square identifies W(Z/Y) with Y times over W(Y/X) W(Z/X).
Source: Stacks, Tag 06BF (blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node steps 1--3): the map h between the universal thickenings comes from 060A.
For P = Y times over W(Y/X) W(Z/X), uniqueness for W(Y/X) forces every extension
into W(Z/X) of a Y-test to factor uniquely through P. Thus P is universal over Y
and is uniquely isomorphic to the specified E. The closed-subspace/ideal correspondence
identifies its ideal as K/L where L is the image of h-star I. At a geometric point,
lem-sfb-space-stalk-ideal-pullback identifies the first map as I tensor B to K,
i tensor b maps to h-sharp(i) times any lift of b. Its image is IB-prime = L;
square-zero makes the lift immaterial. The second map is k maps to k modulo L.
It is onto with kernel L. Exact conservative stalks give exactness and epimorphy,
with no injectivity claim for the first arrow. -/
theorem universal_conormal_transitivity {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (a : Z ⟶ Y) (b : Y ⟶ X) (ha : SpaceFormallyUnramified a)
    (hb : SpaceFormallyUnramified b)
    (D : UniversalConormalThickening (a ≫ b))
    (E : UniversalConormalThickening a) (F : UniversalConormalThickening b) :
    IsPullback E.projection (E.map D (𝟙 Z) b (Category.id_comp (a ≫ b)))
      F.inclusion (D.map F a (𝟙 X) (Category.comp_id (a ≫ b)).symm) ∧
      ∃ w : D.conormalMap F a (𝟙 X) (Category.comp_id (a ≫ b)).symm ≫
          universalConormalQuotient a b D E = 0,
        (ShortComplex.mk _ _ w).Exact ∧ Epi (universalConormalQuotient a b D E) := by
  sorry

/-- Universal thickenings and their induced conormal maps localize on any etale square.
There is no cartesian-square or surjectivity hypothesis. The final comparison is the
specified tensor-to-restriction comparison, so the ideal map itself is the restriction iso.
Source: Stacks, Tags 060D and 0605(1)
(blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node steps 4--6): etale scheme maps lift uniquely on affine square-zero tests
by lem-weil-pbc-flat-unramified-formally-etale. Glue over affine covers and descend
along space atlases. These lifts show V/U is formally unramified. Etale transfer
lifts V/B to an etale map of universal thickenings over A. The unique lift to U
makes that same thickening universal over U; uniqueness identifies it with D.
The reduction square is cartesian. The ideal/closed-subspace correspondence identifies
its ideal with the etale restriction of the original ideal. The actual ideal map is
that identification, by its section normalization. The tensor-restriction theorem
identifies this with restriction on the small etale sites. -/
theorem universal_conormal_etale_localization {S : Scheme.{u}}
    {V U B A : AlgebraicSpace S} (f : V ⟶ U) (g : B ⟶ A)
    (p : V ⟶ B) (q : U ⟶ A) (w : p ≫ g = f ≫ q)
    (hp : IsEtale p.hom.hom) (hq : IsEtale q.hom.hom)
    (hg : SpaceFormallyUnramified g) :
    SpaceFormallyUnramified f ∧
      ∀ (D : UniversalConormalThickening f) (E : UniversalConormalThickening g),
        IsEtale (D.map E p q w).hom.hom ∧
        IsPullback p D.inclusion E.inclusion (D.map E p q w) ∧
        IsIso (D.conormalMap E p q w) ∧
        ∃ e : (pullback p hp).obj E.conormal ≅ D.conormal,
          D.conormalMap E p q w =
            ((Classical.choose (moduleTensorPullback_etale_restriction p hp)).hom.app
              E.conormal) ≫ e.hom := by
  sorry

/-- Every etale ambient pullback of a universal thickening is universal over the same base.
Source: Stacks, Tag 0605(1) (blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node step 6): etale base change makes the map on reductions etale. Apply the
etale lifting theorem to it. Uniqueness of the etale lift of a space across a
square-zero thickening identifies the given ambient D with that lifted universal
thickening, fixing both the inclusion and the structure map. -/
theorem universal_conormal_etale_ambient {S : Scheme.{u}}
    {B A W D V : AlgebraicSpace S} (g : B ⟶ A) (i : B ⟶ W) (r : W ⟶ A)
    (H : IsUniversalSpaceFirstOrderThickening g i r) (d : D ⟶ W)
    (hd : IsEtale d.hom.hom) (p : V ⟶ B) (j : V ⟶ D)
    (hcart : IsPullback p j i d) :
    IsUniversalSpaceFirstOrderThickening (p ≫ g) j (d ≫ r) := by
  sorry

/-- The induced maps of thickenings preserve identities and composition.
Source: Stacks, Tag 060A (blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node steps 1 and 7): the identity and the composite both extend the indicated
reduced map and have the indicated base map. Uniqueness gives the equalities. -/
theorem universalConormalThickening_map_functorial {S : Scheme.{u}}
    {Z₀ X₀ Z₁ X₁ Z₂ X₂ : AlgebraicSpace S}
    {f₀ : Z₀ ⟶ X₀} {f₁ : Z₁ ⟶ X₁} {f₂ : Z₂ ⟶ X₂}
    (D₀ : UniversalConormalThickening f₀) (D₁ : UniversalConormalThickening f₁)
    (D₂ : UniversalConormalThickening f₂)
    (a : Z₀ ⟶ Z₁) (b : X₀ ⟶ X₁) (c : Z₁ ⟶ Z₂) (d : X₁ ⟶ X₂)
    (w₀ : a ≫ f₁ = f₀ ≫ b) (w₁ : c ≫ f₂ = f₁ ≫ d)
    (w₂ : (a ≫ c) ≫ f₂ = f₀ ≫ (b ≫ d)) :
    D₀.map D₀ (𝟙 Z₀) (𝟙 X₀) ((Category.id_comp f₀).trans
      (Category.comp_id f₀).symm) = 𝟙 D₀.ambient ∧
      D₀.map D₁ a b w₀ ≫ D₁.map D₂ c d w₁ = D₀.map D₂ (a ≫ c) (b ≫ d) w₂ ∧
      (moduleTensorComposition a c).inv.app D₂.conormal ≫
        (moduleTensorPullback a).map (D₁.conormalMap D₂ c d w₁) ≫
          D₀.conormalMap D₁ a b w₀ = D₀.conormalMap D₂ (a ≫ c) (b ≫ d) w₂ := by
  sorry

/-- The composite of two tower squares commutes.
Source: Stacks, Tag 060A (blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node step 7): associativity followed by the two given square equations gives
z(a b) = (a0 b0)x. This applies also when x is the identity. -/
theorem universalConormalTower_square {S : Scheme.{u}}
    {Z Y X Z₀ Y₀ X₀ : AlgebraicSpace S}
    (a : Z ⟶ Y) (b : Y ⟶ X) (a₀ : Z₀ ⟶ Y₀) (b₀ : Y₀ ⟶ X₀)
    (z : Z₀ ⟶ Z) (y : Y₀ ⟶ Y) (x : X₀ ⟶ X)
    (w₁ : z ≫ a = a₀ ≫ y) (w₂ : y ≫ b = b₀ ≫ x) :
    z ≫ (a ≫ b) = (a₀ ≫ b₀) ≫ x := by
  sorry

/-- Compatible etale charts identify BOTH arrows of the right exact sequence.
The comparison of their tensor sources is the existing normalized moduleTensorSquare.
Source: Stacks, Tags 060A, 060D and 06BF
(blueprint: lem-sfb-universal-conormal-chart-transitivity).
Proof (node step 7): uniqueness makes the ambient extension maps commute. On ideal
tensors the two composites defining lambda send i tensor b to h-sharp(i) times a
lift of b. Both composites defining rho send k to its class modulo the pulled-back
ideal. Equality follows on conservative geometric stalks, or on local ideal generators.
The tensor source comparison multiplies scalar coefficients; the commuting ring-map
square gives the same product on both paths. Etale localization identifies the three
vertical ideal maps with isomorphisms. Nothing requires a nonidentity change on X. -/
theorem universal_conormal_transitivity_etale_charts {S : Scheme.{u}}
    {Z Y X Z₀ Y₀ X₀ : AlgebraicSpace S}
    (a : Z ⟶ Y) (b : Y ⟶ X) (a₀ : Z₀ ⟶ Y₀) (b₀ : Y₀ ⟶ X₀)
    (z : Z₀ ⟶ Z) (y : Y₀ ⟶ Y) (x : X₀ ⟶ X)
    (w₁ : z ≫ a = a₀ ≫ y) (w₂ : y ≫ b = b₀ ≫ x)
    (hz : IsEtale z.hom.hom) (hy : IsEtale y.hom.hom) (hx : IsEtale x.hom.hom)
    (ha : SpaceFormallyUnramified a) (hb : SpaceFormallyUnramified b)
    (D : UniversalConormalThickening (a ≫ b))
    (E : UniversalConormalThickening a) (F : UniversalConormalThickening b)
    (D₀ : UniversalConormalThickening (a₀ ≫ b₀))
    (E₀ : UniversalConormalThickening a₀) (F₀ : UniversalConormalThickening b₀) :
    SpaceFormallyUnramified a₀ ∧ SpaceFormallyUnramified b₀ ∧
      IsIso (F₀.conormalMap F y x w₂) ∧ IsIso (E₀.conormalMap E z y w₁) ∧
      IsIso (D₀.conormalMap D z x (universalConormalTower_square a b a₀ b₀ z y x w₁ w₂)) ∧
      (moduleTensorPullback z).map
          (D.conormalMap F a (𝟙 X) (Category.comp_id (a ≫ b)).symm) ≫
        D₀.conormalMap D z x (universalConormalTower_square a b a₀ b₀ z y x w₁ w₂) =
        (moduleTensorSquare a y z a₀ w₁).inv.app F.conormal ≫
          (moduleTensorPullback a₀).map (F₀.conormalMap F y x w₂) ≫
            D₀.conormalMap F₀ a₀ (𝟙 X₀) (Category.comp_id (a₀ ≫ b₀)).symm ∧
      (moduleTensorPullback z).map (universalConormalQuotient a b D E) ≫
        E₀.conormalMap E z y w₁ =
        D₀.conormalMap D z x (universalConormalTower_square a b a₀ b₀ z y x w₁ w₂) ≫
          universalConormalQuotient a₀ b₀ D₀ E₀ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
