/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Sober
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.ProjectiveNodalTower
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Blowup.Complement

/-!
# Finite exceptional sets descend through trait conductor pushouts

Source: Stacks Project, varieties.tex, Tag 0BFP, clauses (1),(2), and
more-morphisms.tex, Tag 0E25, open-restriction construction; conductor descent
(blueprint: lem-sfb-conductor-modification-finite-complement).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical morphism of conductor pushouts induced by `h` and the identity of `N`.
It is the actual colimit descent map, not an independently supplied morphism.
Source: Stacks Project, more-morphisms.tex, Tag 0E25, universal property
(blueprint: lem-sfb-conductor-modification-finite-complement). -/
def conductorModificationMap {B C W N X Y : Scheme.{u}}
    (iC : B ⟶ C) (iW : B ⟶ W) (j : B ⟶ N)
    (a : C ⟶ X) (b : N ⟶ X) (aW : W ⟶ Y) (bY : N ⟶ Y)
    (h : W ⟶ C) (hB : iW ≫ h = iC)
    (hX : IsPushout iC j a b) (hY : IsPushout iW j aW bY) : Y ⟶ X :=
  hY.desc (h ≫ a) b (by rw [← Category.assoc, hB]; exact hX.w)

/-- Finite exceptional sets on regular surfaces over a trait descend through the two
compatible conductor pushout squares, including their horizontal node loci.

Source: Stacks Project, varieties.tex, Tag 0BFP, clauses (1),(2), and
more-morphisms.tex, Tag 0E25, open-restriction construction
(blueprint: lem-sfb-conductor-modification-finite-complement).

Proof plan:
1. A DVR is Noetherian [def-sc-discrete-valuation-ring, def-weil-pbc-noetherian-ring].
Its spectrum is locally Noetherian and quasi-compact [pqf-def-locnoeth,
lem-weil-pbc-affine-scheme-qcqs]. Projectivity implies properness, hence finite type;
C is Noetherian [lem-kun-projective-implies-proper, pqf-lem-proper-basic,
lem-weil-pbc-finite-type-over-noetherian].
2. Induct along A. The reduced point ideals are finitely generated on Noetherian affine
opens [pqf-lem-affine-open-locnoeth, def-weil-pbc-noetherian-ring]. Each blowup is proper
[lemma-nagata-blowup-proper], hence finite type, with Noetherian source. Every prefix and
r are proper [lem-weil-pbc-proper-composition]; T is Noetherian.
3. The stalks of T are regular [def-weil-regular-scheme], and the one-dimensional stalks
are DVRs [lem-sc-regular-dim1-dvr]. Apply clauses (1),(2) of
[lem-sfb-normal-modification-codimension-one] to q, with the supplied generic-point and
stalk isomorphisms. Its maximal isomorphism open contains all local-dimension 0 or 1 points.
4. Every point outside U has two strict generalizations
[lem-sc-scheme-stalk-dimension-generalization-chains]. A further strict specialization
would give a chain of length three in a dimension-two component, impossible
[def-kun-topological-krull-dimension]. Thus all these points are closed, and the closed
complement is finite [lem-sc-noetherian-closed-points-finite]. The generic fibre is open
and q is an isomorphism there, so maximality puts it inside U.
5. Properness makes the images under r and all prefixes closed [pqf-lem-proper-basic].
Their finite union D consists of closed special-fibre points. The finite map a is closed
[lem-weil-pbc-finite-closed-map-finite-fibres], so Z = a(D) has the same properties.
6. Above C minus D every blowup misses its centre. Iterate
[thm-nagata-global-blowup-complement] to make r an isomorphism there. That inverse image
also misses T minus U, so q, and consequently h = q r, is an isomorphism there.
7. Descend a h and b by [def-weil-pbc-category-colimit]. For V = X minus Z the two
inverse-image squares have curve terms identified by h, the same N term and the same B
term, since h restricts to iC on B. Both squares are pushouts by hOpenX and hOpenY.
8. Descend the inverse curve isomorphism and the identity on that N term. Uniqueness in
the two pushout universal properties makes both composites identities. This includes
every point of N over V and applies when B,N or the exceptional set is empty, and when
A has length zero.
-/
theorem conductor_modification_finite_complement
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (C W B N X Y T : Over (Spec (.of R)))
    [IsHProjective C.hom] [Flat C.hom] [LocallyOfFinitePresentation C.hom]
    [IsHProjective W.hom] [Flat W.hom] [LocallyOfFinitePresentation W.hom]
    [IsHProjective X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [IsHProjective Y.hom] [Flat Y.hom] [LocallyOfFinitePresentation Y.hom]
    [IsFinite B.hom] [Etale B.hom] [IsFinite N.hom] [Etale N.hom]
    (iC : B ⟶ C) (iW : B ⟶ W) (j : B ⟶ N)
    [IsClosedImmersion iC.left] [IsClosedImmersion iW.left]
    [Etale j.left] [j.left.IsFiniteLocallyFreeOfDegree 2]
    (hiC : ∀ z : B.left, iC.left z ∈ C.hom.smoothLocus)
    (hiW : ∀ z : B.left, iW.left z ∈ W.hom.smoothLocus)
    (hnodal : ∀ F : Over (Spec (.of R)), F ∈ [C, W, X, Y] →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
        Nonempty ↥(pullback (C := Scheme.{u}) F.hom g) ∧
        IsReduced (pullback (C := Scheme.{u}) F.hom g) ∧
        (pullback (C := Scheme.{u}) F.hom g).IsPureDimension 1 ∧
        ∀ x : ↥(pullback (C := Scheme.{u}) F.hom g),
          IsClosed ({x} : Set ↥(pullback (C := Scheme.{u}) F.hom g)) →
          (¬ ∃ V : (pullback (C := Scheme.{u}) F.hom g).Opens,
            x ∈ V ∧ Smooth (V.ι ≫ pullback.snd F.hom g)) →
          IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) F.hom g) x)
    (a : C ⟶ X) (b : N ⟶ X) (aW : W ⟶ Y) (bY : N ⟶ Y)
    [IsFinite a.left] [Surjective a.left] [IsClosedImmersion b.left]
    [IsFinite aW.left] [Surjective aW.left] [IsClosedImmersion bY.left]
    (hX : IsPushout iC.left j.left a.left b.left)
    (hY : IsPushout iW.left j.left aW.left bY.left)
    (hcartX : IsPullback iC.left j.left a.left b.left)
    (hcartY : IsPullback iW.left j.left aW.left bY.left)
    (hOpenX : ∀ V : X.left.Opens,
      IsPushout
        ((Over.pullback V.ι).map (Over.homMk iC.left rfl :
          Over.mk (iC.left ≫ a.left) ⟶ Over.mk a.left)).left
        ((Over.pullback V.ι).map (Over.homMk j.left hX.w.symm :
          Over.mk (iC.left ≫ a.left) ⟶ Over.mk b.left)).left
        (pullback.snd a.left V.ι) (pullback.snd b.left V.ι))
    (hOpenY : ∀ V : Y.left.Opens,
      IsPushout
        ((Over.pullback V.ι).map (Over.homMk iW.left rfl :
          Over.mk (iW.left ≫ aW.left) ⟶ Over.mk aW.left)).left
        ((Over.pullback V.ι).map (Over.homMk j.left hY.w.symm :
          Over.mk (iW.left ≫ aW.left) ⟶ Over.mk bY.left)).left
        (pullback.snd aW.left V.ι) (pullback.snd bY.left V.ι))
    (hcomplX : ∃ (V : C.left.Opens) (V' : X.left.Opens) (e : V.toScheme ≅ V'.toScheme),
      (V : Set C.left) = (Set.range iC.left)ᶜ ∧
      (V' : Set X.left) = (Set.range b.left)ᶜ ∧ e.hom ≫ V'.ι = V.ι ≫ a.left)
    (hcomplY : ∃ (V : W.left.Opens) (V' : Y.left.Opens) (e : V.toScheme ≅ V'.toScheme),
      (V : Set W.left) = (Set.range iW.left)ᶜ ∧
      (V' : Set Y.left) = (Set.range bY.left)ᶜ ∧ e.hom ≫ V'.ι = V.ι ≫ aW.left)
    (r : T ⟶ C) (A : OrdinaryBlowupTower C.left)
    (eT : T.left ≅ A.level (Fin.last A.length))
    (heT : eT.hom ≫ A.toBase (Fin.last A.length) = r.left)
    (hcentres : ∀ i : Fin A.length,
      ∃ (z : A.level i.castSucc) (hz : IsClosed ({z} : Set (A.level i.castSucc))),
        A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩ ∧
        (A.toBase i.castSucc ≫ C.hom) z = IsLocalRing.closedPoint R)
    (hregular : IsRegularScheme T.left)
    (hcomponents : ∃ (ι : Type u) (_ : Finite ι) (V : ι → T.left.Opens),
      (∀ i j : ι, i ≠ j → Disjoint (V i) (V j)) ∧ iSup V = ⊤ ∧
      ∀ i : ι, IsIntegral (V i).toScheme ∧ topologicalKrullDim (V i) = 2)
    (q : W ⟶ T) [IsProper q.left] [IsReduced W.left]
    (hgeneric : Set.BijOn q.left
      {η : W.left | ∃ F ∈ irreducibleComponents W.left, IsGenericPoint η F}
      {η : T.left | ∃ F ∈ irreducibleComponents T.left, IsGenericPoint η F})
    (hstalk : ∀ η : W.left, (∃ F ∈ irreducibleComponents W.left, IsGenericPoint η F) →
      IsIso (q.left.stalkMap η))
    (hqK : IsIso (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).map q).left))
    (hB : iW.left ≫ q.left ≫ r.left = iC.left)
    (U : T.left.Opens) (hU : IsGreatest {V : T.left.Opens | IsIso (q.left ∣_ V)} U) :
    ((U : Set T.left)ᶜ).Finite ∧
    (∀ z : T.left, z ∉ U → IsClosed ({z} : Set T.left) ∧
      T.hom z = IsLocalRing.closedPoint R) ∧
    ∃ (D : Set C.left) (Z : Set X.left),
      D = r.left '' (U : Set T.left)ᶜ ∪
        ⋃ i : Fin A.length, (A.toBase i.castSucc) '' (A.center i).support ∧
      Z = a.left '' D ∧ D.Finite ∧ Z.Finite ∧
      (∀ z ∈ D, IsClosed ({z} : Set C.left) ∧ C.hom z = IsLocalRing.closedPoint R) ∧
      (∀ z ∈ Z, IsClosed ({z} : Set X.left) ∧ X.hom z = IsLocalRing.closedPoint R) ∧
      ∃ V : X.left.Opens, (V : Set X.left) = Zᶜ ∧
        IsIso (conductorModificationMap iC.left iW.left j.left a.left b.left
          aW.left bY.left (q.left ≫ r.left) hB hX hY ∣_ V) := by
  sorry

end AlgebraicGeometry
