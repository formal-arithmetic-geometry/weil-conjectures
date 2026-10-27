/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExists

/-! # Universal first-order thickenings and conormal modules of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tags 04GA and 0601--0608;
Morphisms of Spaces, Tag 03MB; More on Morphisms of Spaces, definition-conormal-sheaf
(blueprint: lem-sfb-space-universal-conormal).

## Main definitions and statements

* `SpaceFormallyUnramified`: injectivity on scheme first-order tests.
* `SpaceChartwiseUnramified`: unramifiedness on compatible etale scheme charts.
* `spaceConormal`: tensor pullback of the actual kernel ideal.
* `space_universal_firstOrderThickening_exists`: existence with all space tests.
* `space_universal_conormal`: the common topos and its square-zero kernel module.
* `space_universal_conormal_closed`: the ideal-square neighbourhood and quotient.
* `space_conormal_map`: canonical ideal maps, normalized on local tensor sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Formal unramifiedness on all scheme first-order thickenings, with fixed map to X.
Source: Stacks, Tag 04G8 and definition-formally-smooth-etale-unramified
(blueprint: lem-sfb-space-universal-conormal). -/
def SpaceFormallyUnramified {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (h : Z ⟶ X) : Prop :=
  ∀ (T T' : Over S) (j : T ⟶ T'), IsFirstOrderThickening j.left →
    ∀ (b : yoneda.obj T' ⟶ X.obj.obj) (a₁ a₂ : yoneda.obj T' ⟶ Z.obj.obj),
      a₁ ≫ h.hom.hom = b → a₂ ≫ h.hom.hom = b →
      yoneda.map j ≫ a₁ = yoneda.map j ≫ a₂ → a₁ = a₂

/-- Unramifiedness on compatible etale scheme charts, without assuming representability
of h. Source: Stacks, Tag 04GA, using the chart definition of unramifiedness
(blueprint: lem-sfb-space-universal-conormal). -/
def SpaceChartwiseUnramified {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (h : Z ⟶ X) : Prop :=
  ∀ (V U : Over S) (a : yoneda.obj V ⟶ Z.obj.obj)
    (b : yoneda.obj U ⟶ X.obj.obj) (g : V ⟶ U),
    IsEtale a → IsEtale b → a ≫ h.hom.hom = yoneda.map g ≫ b →
      AlgebraicGeometry.IsUnramified g.left

/-- The defining ideal, taken as the categorical kernel of the actual structural map.
Source: Stacks, Tag 03MB (blueprint: lem-sfb-space-universal-conormal). -/
abbrev spaceKernel {S : Scheme.{u}} {Z W : AlgebraicSpace S} (i : Z ⟶ W) : W.Modules :=
  kernel (moduleStructureMap i)

/-- The conormal module of a closed immersion, and in particular of a universal
first-order thickening. Tensor pullback is I/I²; for a first-order thickening I²=0.
Source: Stacks, definition-conormal-sheaf and Tag 0607
(blueprint: lem-sfb-space-universal-conormal). -/
def spaceConormal {S : Scheme.{u}} {Z W : AlgebraicSpace S} (i : Z ⟶ W) : Z.Modules :=
  (moduleTensorPullback i).obj (spaceKernel i)

/-- The section 1 tensor m on a compatible reduced chart. This uses the existing
normalized tensor adjunction, rather than a chosen map into the conormal module.
Source: Stacks, definition-conormal-sheaf and Tag 0607
(blueprint: lem-sfb-space-universal-conormal). -/
def spaceConormalSection {S : Scheme.{u}} {Z W : AlgebraicSpace S} (i : Z ⟶ W)
    (U : Z.EtaleSite) (V : W.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ i.hom.hom)
    (m : (spaceKernel i).val.obj (op V)) : (spaceConormal i).val.obj (op U) :=
  moduleTensorSection i (spaceKernel i) V
    (CostructuredArrow.mk (CostructuredArrow.homMk a ha)) 1 m

/-- Normalization of a conormal identification by the pullback of actual ideal sections.
Source: Stacks, Tag 0608 and the functoriality following definition-conormal-sheaf
(blueprint: lem-sfb-space-universal-conormal). -/
def IsSpaceConormalIdentification {S : Scheme.{u}} {Z W X : AlgebraicSpace S}
    (h : Z ⟶ X) (k : Z ⟶ W) (q : W ⟶ X)
    (e : spaceConormal h ≅ spaceConormal k) : Prop :=
  ∀ (U : Z.EtaleSite) (B : W.EtaleSite) (A : X.EtaleSite)
    (b : B.obj.left ⟶ A.obj.left)
    (_hb : yoneda.map b ≫ A.obj.hom = B.obj.hom ≫ q.hom.hom)
    (c : U.obj.left ⟶ B.obj.left)
    (hc : yoneda.map c ≫ B.obj.hom = U.obj.hom ≫ k.hom.hom)
    (d : U.obj.left ⟶ A.obj.left)
    (hd : yoneda.map d ≫ A.obj.hom = U.obj.hom ≫ h.hom.hom),
    c ≫ b = d → ∀ (s : (spaceKernel h).val.obj (op A))
      (t : (spaceKernel k).val.obj (op B)),
      (kernel.ι (moduleStructureMap k)).val.app (op B) t =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map b.left.op)
          ((kernel.ι (moduleStructureMap h)).val.app (op A) s) →
      e.hom.val.app (op U) (spaceConormalSection h U A d hd s) =
        spaceConormalSection k U B c hc t

/-- A map on conormals is the canonical map on ideals when it sends every local
ideal tensor to the tensor of its ring-map image. All charts and all lifts occur.
Source: Stacks, functoriality following definition-conormal-sheaf, and Tag 0607
(blueprint: lem-sfb-space-universal-conormal). -/
def IsSpaceConormalMap {S : Scheme.{u}} {Z Y W V : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : W ⟶ V) (i : Z ⟶ W) (j : Y ⟶ V)
    (θ : (moduleTensorPullback f).obj (spaceConormal j) ⟶ spaceConormal i) : Prop :=
  ∀ (U : Z.EtaleSite) (T : Y.EtaleSite) (B : W.EtaleSite) (A : V.EtaleSite)
    (a : U.obj.left ⟶ T.obj.left)
    (ha : yoneda.map a ≫ T.obj.hom = U.obj.hom ≫ f.hom.hom)
    (b : B.obj.left ⟶ A.obj.left)
    (_hb : yoneda.map b ≫ A.obj.hom = B.obj.hom ≫ g.hom.hom)
    (c : U.obj.left ⟶ B.obj.left)
    (hc : yoneda.map c ≫ B.obj.hom = U.obj.hom ≫ i.hom.hom)
    (d : T.obj.left ⟶ A.obj.left)
    (hd : yoneda.map d ≫ A.obj.hom = T.obj.hom ≫ j.hom.hom),
    c ≫ b = a ≫ d → ∀ (s : (spaceKernel j).val.obj (op A))
      (t : (spaceKernel i).val.obj (op B)),
      (kernel.ι (moduleStructureMap i)).val.app (op B) t =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map b.left.op)
          ((kernel.ι (moduleStructureMap j)).val.app (op A) s) →
      θ.val.app (op U)
          (moduleTensorSection f (spaceConormal j) T
            (CostructuredArrow.mk (CostructuredArrow.homMk a ha)) 1
              (spaceConormalSection j T A d hd s)) =
        spaceConormalSection i U B c hc t

/-- Unramified space maps are formally unramified.
Source: Stacks, Tag 04GA (blueprint: lem-sfb-space-universal-conormal).

Proof (node step 1): take compatible surjective etale scheme charts. The chart map
is unramified, hence formally unramified by the scheme theorem. The chart criterion
[lem-sfb-space-formally-unramified-etale-charts] descends uniqueness to affine tests.
Cover arbitrary scheme tests by affine opens and use the sheaf condition to descend
equality. No representability, separation or finiteness of h is assumed. -/
theorem space_unramified_formally_unramified {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (h : Z ⟶ X) (hh : SpaceChartwiseUnramified h) : SpaceFormallyUnramified h := by
  sorry

/-- Universal first-order thickenings exist, with the universal property on ALL spaces.
Source: Stacks, Tags 0603 and 0606 (blueprint: lem-sfb-space-universal-conormal).

Proof (node steps 2--5): scheme-test lifts glue over etale charts of any space test:
uniqueness gives agreement on scheme charts of overlaps. Choose compatible surjective
charts V -> Z and U -> X. The scheme existence theorem gives V -> V+ over U;
representable etale infinitesimal lifting makes it universal over X as well. Repeat
for R = V times_Z V. Universality lifts both projections R+ -> V+; etale transfer
makes them etale with cartesian reduction squares. Lift identity, inverse and
composition by universality. Their equations follow from uniqueness. Field-valued
points factor through the reductions, so the geometric-point criterion makes R+
an equivalence relation. Its algebraic-space quotient W carries W -> X. The
kernel-pair calculation shows Z times_W V+ = V and Z -> W monic. Closed-immersion
atlas locality makes it a representable closed immersion. Its ideal is square zero
on the atlas, hence globally. Etale descent of universality gives the assertion. -/
theorem space_universal_firstOrderThickening_exists {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (h : Z ⟶ X) (hh : SpaceFormallyUnramified h) :
    ∃ (W : AlgebraicSpace S) (k : Z ⟶ W) (q : W ⟶ X),
      IsUniversalSpaceFirstOrderThickening h k q := by
  sorry

/-- On the common etale topos, the conormal is precisely the square-zero kernel.
The unit is the canonical kernel-to-pullback map, including the quotient scalar action.
Source: Stacks, Tags 05ZS and 0607 (blueprint: lem-sfb-space-universal-conormal).

Proof (node step 6): a square-zero immersion is integral, radicial and surjective on
every scheme test. Topological invariance identifies the enlarged etale sites and
preserves covers. Small/enlarged comparison gives the stated small-topos equivalence.
The closed-immersion ideal theorem makes the kernel quasi-coherent. Its square is
zero, so its scalar action factors through O_Z. The closed-immersion module essential
image theorem identifies it with its tensor pullback; the identifying map is the
adjunction unit. Thus its conormal is quasi-coherent over O_Z. -/
theorem space_universal_conormal {S : Scheme.{u}} {Z X W : AlgebraicSpace S}
    (h : Z ⟶ X) (k : Z ⟶ W) (q : W ⟶ X)
    (H : IsUniversalSpaceFirstOrderThickening h k q) :
    (enlargedSmallDirectImage.{u, u} k).IsEquivalence ∧
      (spaceKernel k).IsQuasicoherent ∧ (spaceConormal k).IsQuasicoherent ∧
      IsIso ((moduleTensorAdjunction k).unit.app (spaceKernel k)) := by
  sorry

/-- For a closed immersion the universal neighbourhood is cut out by K²; the
conormal is K/K², with the isomorphism fixed on actual ideal sections.
Source: Stacks, Tags 05ZW and 0608 (blueprint: lem-sfb-space-universal-conormal).

Proof (node step 7): form the closed subspace defined by K², using the ideal/closed
subspace correspondence. Products localize, so K² is quasi-coherent. Its inclusion
of Z has ideal K/K² and is first order. A test map whose reduction factors through Z
sends K into the test ideal J and hence K² into J²=0. It factors uniquely through
this neighbourhood, proving universality. Uniqueness of the universal property
identifies every universal W with this neighbourhood over X and under Z. Pullback
on ring sheaves identifies the kernels by a -> a modulo K². The quotient action
identifies the tensor pullback of K with K/K². These equations prescribe the
isomorphism uniquely on local generators, including its compatibility with ideals.
The kernel of the adjunction unit is K² as a sheaf (local membership, not a claim
that all global quotient sections lift). -/
theorem space_universal_conormal_closed {S : Scheme.{u}} {Z X W : AlgebraicSpace S}
    (h : Z ⟶ X)
    (hh : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) h.hom.hom)
    (k : Z ⟶ W) (q : W ⟶ X) (H : IsUniversalSpaceFirstOrderThickening h k q) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) q.hom.hom ∧
      (∀ A : X.EtaleSite,
        Set.range ((kernel.ι (moduleStructureMap q)).val.app (op A)) =
          idealPowerSubsheafSections (kernel.ι (moduleStructureMap h))
            (SheafOfModules.unit X.structureSheaf) (fun _ ↦ Set.univ) 2 A) ∧
      Epi ((moduleTensorAdjunction h).unit.app (spaceKernel h)) ∧
      (∀ (A : X.EtaleSite) (s : (spaceKernel h).val.obj (op A)),
        ((moduleTensorAdjunction h).unit.app (spaceKernel h)).val.app (op A) s = 0 ↔
          (kernel.ι (moduleStructureMap h)).val.app (op A) s ∈
            idealPowerSubsheafSections (kernel.ι (moduleStructureMap h))
              (SheafOfModules.unit X.structureSheaf) (fun _ ↦ Set.univ) 2 A) ∧
      ∃! e : spaceConormal h ≅ spaceConormal k, IsSpaceConormalIdentification h k q e := by
  sorry

/-- Maps of first-order thickenings induce exactly the canonical maps of kernel ideals.
Together with the normalized identification above this expresses compatibility of the
conormal identifications with maps of thickenings.
Source: Stacks, Tag 0607 and functoriality following definition-conormal-sheaf
(blueprint: lem-sfb-space-universal-conormal).

Proof (node step 8): the commuting square of quotient ring maps sends each kernel
into the other kernel. Multiplication by a local lift of a reduced scalar defines
the tensor map. Different lifts differ by the target kernel, whose square is zero,
so the map is well-defined and linear. The ring-map identity commutes with chart
restrictions, hence glues. Local ideal tensors generate, giving uniqueness. In the
closed-immersion description the map sends a modulo K² to its ring-map image modulo
the other squared ideal. The normalization defining IsSpaceConormalIdentification
uses precisely this same ring-map formula, so these identifications commute with
every induced ideal map. -/
theorem space_conormal_map {S : Scheme.{u}} {Z Y W V : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : W ⟶ V) (i : Z ⟶ W) (j : Y ⟶ V)
    (hi : IsSpaceFirstOrderThickening i) (hj : IsSpaceFirstOrderThickening j)
    (hc : i ≫ g = f ≫ j) :
    ∃! θ : (moduleTensorPullback f).obj (spaceConormal j) ⟶ spaceConormal i,
      IsSpaceConormalMap f g i j θ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
