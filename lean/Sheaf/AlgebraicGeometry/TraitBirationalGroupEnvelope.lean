module

public import Sheaf.AlgebraicGeometry.RelativeBirationalGroupLaw
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # A group envelope for a birational group law over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 4.3 Theorem 6 and
5.1 Theorem 5, including its no-shrinking clause
(blueprint: lem-sfb-trait-birational-group-envelope).

The rational multiplication is given by a representative whose domain contains the
entire generic fibre. `Grp (Over T)` uses the standard group-object diagrams over `T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A smooth separated finite-type trait model with a birational group law and an entire
 generic group fibre embeds openly and fibrewise densely in a smooth separated finite-type
 group scheme, with exactly that generic group and multiplication.

Source: BLR 4.3 Theorem 6, printed p.108, and 5.1 Theorem 5, printed p.114
(blueprint: lem-sfb-trait-birational-group-envelope).

Proof plan:
1. Strictify on a fibrewise dense open containing the generic fibre, using
   lem-sfb-birational-law-strictification. Realize the strict law in a smooth separated
   finite-type group scheme by lem-sfb-strict-birational-law-realization.
2. Uniqueness of that realization over the fraction field identifies its generic fibre
   with the specified group, since the strictifying open contains the entire generic fibre.
3. The dense open contains all points of local dimension at most one by
   lem-sfb-smooth-trait-birational-immersion. A DVR is a normal Noetherian domain of
   dimension one: a fraction integral over it cannot have negative valuation, by its monic
   equation. Apply lem-sfb-relative-weil-codimension-extension to extend the open embedding.
4. The immersion criterion of lem-sfb-smooth-trait-birational-immersion makes this extension
   an open immersion. Its image contains the already fibrewise dense strict-law image.
5. On the multiplication domain the two maps into the separated group agree generically.
   The uniqueness clause of lem-sfb-smooth-trait-local-rational-spreading makes them equal
   everywhere. The source product is smooth by lem-pc-proper-base-change and
   lem-trf-smooth-composition. This proves restriction to the chosen representative.
No Néron mapping property is asserted. -/
theorem exists_trait_birationalGroupEnvelope
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Y : Over (Spec (.of R)))
    [Smooth Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    (hSpecial : Nonempty (Y.hom.fiber (IsLocalRing.closedPoint R)))
    (G : Grp (Over (Spec (.of (FractionRing R)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))))).obj Y ≅ G.X)
    (m : RelativeGroupLaw.Representative (Y ⊗ Y) Y)
    (hLaw : RelativeGroupLaw.IsBirationalGroupLaw m)
    (hGenericDomain : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R (FractionRing R))))).map m.inclusion))
    (hGenericMul :
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))))).map m.hom ≫ e.hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))))).map m.inclusion ≫
      (prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))))) Y Y).hom ≫
      (e.hom ⊗ₘ e.hom) ≫ μ[G.X]) :
    ∃ (M : Grp (Over (Spec (.of R)))),
      Smooth M.X.hom ∧ LocallyOfFiniteType M.X.hom ∧ QuasiCompact M.X.hom ∧
      IsSeparated M.X.hom ∧
      ∃ j : Y ⟶ M.X,
        IsOpenImmersion j.left ∧
        RelativeGroupLaw.IsFiberwiseDense M.X (Set.range j.left) ∧
        (∃ a : G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R))))).mapGrp.obj M,
          e.hom ≫ a.hom.hom.hom =
            (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap R (FractionRing R))))).map j) ∧
        m.hom ≫ j = m.inclusion ≫ (j ⊗ₘ j) ≫ μ[M.X] := by
  sorry

end AlgebraicGeometry
