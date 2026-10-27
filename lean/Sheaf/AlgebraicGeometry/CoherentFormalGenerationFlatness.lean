/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.AlgebraicGeometry.EtaleFibreProductPairRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.FlatCompletion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability

/-!
# Spreading coherent formal generators and flatness

Source: Stacks Project, Algebra, Tags 00MC, 00RC, 00MA, 00MB, 05CK;
Morphisms, Tags 02GO, 024T; the finite-denominator synthesis in the DAG
(blueprint: lem-per-coherent-formal-generation-flatness).

The structures specify the supplied straightening and the neighbourhoods in the
conclusion. Completion means the inverse limit `AdicCompletion`. All comparisons
are fixed on actual regular functions, coefficients and transverse variables.
Coefficient base change uses the actual tensor algebra, then its completion.
Nested series represent W and Z separately, with the coefficientwise map fixing Z.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

/-- A specified formal straightening along a closed section. The adic condition
fixes the completion topology; the constant term is actual restriction to N.
Source: the completion calculation of DAG proof step 2, Stacks 00MA, 00MB, 0H1D
(blueprint: lem-per-coherent-formal-generation-flatness). -/
structure FormalSectionExpansion {U N : Scheme.{u}} (j : N ⟶ U) (n : ℕ) where
  completion : AdicCompletion (RingHom.ker j.appTop.hom) Γ(U, ⊤) ≃+*
    MvPowerSeries (Fin n) Γ(N, ⊤)
  adic : Ideal.map
    (completion.toRingHom.comp
      (algebraMap Γ(U, ⊤) (AdicCompletion (RingHom.ker j.appTop.hom) Γ(U, ⊤))))
    (RingHom.ker j.appTop.hom) = Ideal.span (Set.range MvPowerSeries.X)
  constant : ∀ r : Γ(U, ⊤),
    MvPowerSeries.constantCoeff (completion (algebraMap Γ(U, ⊤) _ r)) = j.appTop r

/-- Expansion of actual regular functions under the specified completion.
Source: DAG proof step 2, Stacks 00MA
(blueprint: lem-per-coherent-formal-generation-flatness). -/
def FormalSectionExpansion.regular {U N : Scheme.{u}} {j : N ⟶ U} {n : ℕ}
    (F : FormalSectionExpansion j n) : Γ(U, ⊤) →+* MvPowerSeries (Fin n) Γ(N, ⊤) :=
  F.completion.toRingHom.comp
    (algebraMap Γ(U, ⊤) (AdicCompletion (RingHom.ker j.appTop.hom) Γ(U, ⊤)))

/-- The actual coefficient-base-change ring, with the displayed scalar maps.
Source: DAG proof step 8, Stacks 00HI
(blueprint: lem-per-coherent-formal-generation-flatness). -/
def formalCoefficientAlgebra {A B : Type u} {S : Type v}
    [CommRing A] [CommRing B] [CommRing S] (r : A →+* B) (q : A →+* S) :
    CommRingCat.{max u v} :=
  letI := r.toAlgebra
  letI := q.toAlgebra
  CommRingCat.of (B ⊗[A] S)

/-- The canonical pullback of regular functions to the coefficient-base-change ring.
Source: DAG proof step 8, Stacks 00HI
(blueprint: lem-per-coherent-formal-generation-flatness). -/
def formalCoefficientAlgebraLeft {A B : Type u} {S : Type v}
    [CommRing A] [CommRing B] [CommRing S] (r : A →+* B) (q : A →+* S) :
    B →+* formalCoefficientAlgebra r q :=
  letI := r.toAlgebra
  letI := q.toAlgebra
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] S).toRingHom

/-- The canonical coefficient map to the coefficient-base-change ring.
Source: DAG proof step 8, Stacks 00HI
(blueprint: lem-per-coherent-formal-generation-flatness). -/
def formalCoefficientAlgebraRight {A B : Type u} {S : Type v}
    [CommRing A] [CommRing B] [CommRing S] (r : A →+* B) (q : A →+* S) :
    S →+* formalCoefficientAlgebra r q :=
  letI := r.toAlgebra
  letI := q.toAlgebra
  (Algebra.TensorProduct.includeRight : S →ₐ[A] B ⊗[A] S).toRingHom

/-- All comparisons after coefficient base change, including the actual completed
ideal and flat quotient. The completion equivalence is pinned on both tensor factors.
Source: DAG proof step 8, Stacks 00HI, 00MA, 00MB
(blueprint: lem-per-coherent-formal-generation-flatness). -/
structure FormalGenerationBaseChange {A B : Type u} {S : Type v}
    [CommRing A] [CommRing B] [CommRing S] {n s : ℕ}
    (r : A →+* B) (q : A →+* S) (H J : Ideal B)
    (F : B →+* MvPowerSeries (Fin n) A) (f : Fin s → MvPowerSeries (Fin n) A) where
  completion : AdicCompletion (H.map (formalCoefficientAlgebraLeft r q))
      (formalCoefficientAlgebra r q) ≃+* MvPowerSeries (Fin n) S
  regular : ∀ b : B,
    completion (algebraMap (formalCoefficientAlgebra r q) _
      (formalCoefficientAlgebraLeft r q b)) = MvPowerSeries.map q (F b)
  scalar : ∀ t : S,
    completion (algebraMap (formalCoefficientAlgebra r q) _
      (formalCoefficientAlgebraRight r q t)) = MvPowerSeries.C t
  adic : Ideal.map (completion.toRingHom.comp
    (algebraMap (formalCoefficientAlgebra r q)
      (AdicCompletion (H.map (formalCoefficientAlgebraLeft r q))
        (formalCoefficientAlgebra r q)))) (H.map (formalCoefficientAlgebraLeft r q)) =
          Ideal.span (Set.range MvPowerSeries.X)
  generation : Ideal.map (completion.toRingHom.comp
    (algebraMap (formalCoefficientAlgebra r q)
      (AdicCompletion (H.map (formalCoefficientAlgebraLeft r q))
        (formalCoefficientAlgebra r q)))) (J.map (formalCoefficientAlgebraLeft r q)) =
      Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map q (f i))
  flat : ((Ideal.Quotient.mk
    (Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map q (f i)))).comp
      MvPowerSeries.C).Flat

/-- The simultaneous neighbourhood and all specified geometric and formal conclusions.
Source: the eight steps of the DAG synthesis, Stacks 00MC, 00RC, 00MA, 00MB
(blueprint: lem-per-coherent-formal-generation-flatness). -/
structure CoherentFormalGenerationNeighbourhood {k : Type u} [Field k]
    {U N : Scheme.{u}} {m n s : ℕ} (j : N ⟶ U) (a : N)
    (c : MvPolynomial (Fin m ⊕ Fin n) k →+* Γ(U, ⊤))
    (J : U.IdealSheafData) (F : FormalSectionExpansion j n)
    (f : Fin s → MvPowerSeries (Fin n) Γ(N, ⊤)) where
  baseOpen : N.Opens
  contains : a ∈ baseOpen
  affineBase : IsAffine baseOpen.toScheme
  ambient : Scheme.{u}
  affineAmbient : IsAffine ambient
  etaleMap : ambient ⟶ U
  etale : Etale etaleMap
  sectionMap : baseOpen.toScheme ⟶ ambient
  closed : IsClosedImmersion sectionMap
  cartesian : IsPullback sectionMap baseOpen.ι etaleMap j
  retraction : ambient ⟶ baseOpen.toScheme
  retracts : sectionMap ≫ retraction = 𝟙 baseOpen.toScheme
  smooth : Smooth retraction
  respects_w : ∀ i : Fin m,
    etaleMap.appTop (c (MvPolynomial.X (Sum.inl i))) =
      retraction.appTop (baseOpen.ι.appTop (j.appTop (c (MvPolynomial.X (Sum.inl i)))))
  transverse : Fin n → Γ(ambient, ⊤)
  transverse_eq : ∀ i : Fin n,
    transverse i = etaleMap.appTop (c (MvPolynomial.X (Sum.inr i))) -
      retraction.appTop (baseOpen.ι.appTop (j.appTop (c (MvPolynomial.X (Sum.inr i)))))
  sectionIdeal : RingHom.ker sectionMap.appTop.hom = Ideal.span (Set.range transverse)
  etaleCoordinates : Etale (ambient.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom retraction.appTop.hom transverse)))
  flatSubscheme : Flat ((J.comap etaleMap).subschemeι ≫ retraction)
  expansion : FormalSectionExpansion sectionMap n
  coefficient : ∀ t : Γ(baseOpen.toScheme, ⊤),
    expansion.regular (retraction.appTop t) = MvPowerSeries.C t
  variableExpansion : ∀ i : Fin n, expansion.regular (transverse i) = MvPowerSeries.X i
  transport : ∀ b : Γ(U, ⊤),
    expansion.regular (etaleMap.appTop b) = MvPowerSeries.map baseOpen.ι.appTop.hom (F.regular b)
  generation : Ideal.map expansion.regular ((J.comap etaleMap).idealOfOpens ⊤) =
    Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map baseOpen.ι.appTop.hom (f i))
  pointwise : ∀ (b : baseOpen.toScheme) (K : Type (max u v)) [Field K]
      (i : baseOpen.toScheme.residueField b →+* K),
    ∃ T : Γ(baseOpen.toScheme, ⊤) →+*
        MvPowerSeries (Fin m) (baseOpen.toScheme.residueField b),
      HilbertCoefficient.isTaylorMap
        (baseOpen.ι.appTop.hom.comp (j.appTop.hom.comp
          (c.comp (MvPolynomial.rename Sum.inl).toRingHom)))
        (baseOpen.toScheme.Γevaluation b).hom T ∧
      Ideal.map
        ((MvPowerSeries.map ((MvPowerSeries.map i).comp T)).comp expansion.regular)
        ((J.comap etaleMap).idealOfOpens ⊤) =
        Ideal.span (Set.range fun l : Fin s ↦
          MvPowerSeries.map (((MvPowerSeries.map i).comp T).comp baseOpen.ι.appTop.hom)
            (f l)) ∧
      ((Ideal.Quotient.mk (Ideal.map
        ((MvPowerSeries.map ((MvPowerSeries.map i).comp T)).comp expansion.regular)
        ((J.comap etaleMap).idealOfOpens ⊤))).comp MvPowerSeries.C).Flat
  baseChange : ∀ (S : Type (max u v)) [CommRing S] [IsNoetherianRing S]
      (q : Γ(baseOpen.toScheme, ⊤) →+* S),
    Nonempty (FormalGenerationBaseChange retraction.appTop.hom q
      (RingHom.ker sectionMap.appTop.hom) ((J.comap etaleMap).idealOfOpens ⊤)
      expansion.regular (fun i : Fin s ↦ MvPowerSeries.map baseOpen.ι.appTop.hom (f i)))
  emptyGenerators : s = 0 → J.comap etaleMap = ⊥
  zeroNearOriginalPoint : s = 0 → ∃ O : U.Opens, j a ∈ O ∧ J.comap O.ι = ⊥

/-- Formal generators and flatness at one centered diagonal point spread to one
common etale and Zariski neighbourhood, with the specified regular retraction.
The polynomial spectrum is the affine-coordinate presentation of affine space.

Source: Stacks Project, Algebra, Tags 00MC, 00RC, 00MA, 00MB, 05CK, 0306;
Morphisms, Tags 02GO, 024T; the node's finite-denominator synthesis
(blueprint: lem-per-coherent-formal-generation-flatness).

Proof:
1. Form U times over A^m with N, delete the other section components by
lem-trf-etale-fibre-product-pair-refinement, and restrict to a principal affine
neighbourhood. Translate z by its restriction along the resulting retraction.
Apply the same refinement to V(Z) to make its section the entire zero scheme.
Etale base change and composition (lem-weil-pbc-etale-scheme-base-change,
lem-weil-pbc-etale-composition-cancellation) and affine-space smoothness
(sbc-lem-affine-space-smooth, lem-sbc-smooth-relative-dimension-permanence)
give the etale coordinates and smooth retraction.
2. Coherence gives finitely many actual regular generators. Finite-type rings
are Noetherian (lem-weil-pbc-finite-type-algebra-noetherian), and their ideals
are finite (lem-trf-noetherian-submodule-finitely-presented). Apply
lem-sfb-augmented-etale-associated-graded and pass through the actual compatible
quotient maps. Exact completion and the tensor description for finite modules
(lem-weil-pbc-completion-exact-finite-modules,
lem-weil-pbc-completion-finite-module-tensor) identify the completed ideal with
the ideal generated by the regular generators inside A[[Z]].
3. Apply lem-trf-diagonal-taylor-faithful-flatness to the coefficient chart.
Localization and composition preserve flatness (lem-weil-pbc-localization-flat,
lem-weil-pbc-flat-ring-map-comp); the coefficient Taylor ring is Noetherian
(lem-weil-pbc-power-series-noetherian). The coefficient-extension result
lem-per-formal-coefficient-taylor-faithful-flatness gives faithful flatness
of the localization of A[[Z]] at the prime determined by a into L[[W]][[Z]].
4. Contract the assumed ideal equality by
lem-weil-pbc-faithfully-flat-ideal-contraction. Choose finite generators of both
ideals. Clear their finitely many localization denominators with one h whose
constant term c avoids the prime of a. After restricting the base to D(c), h
is a formal unit, so the two ideals agree. No infinitely many coefficient
opens are intersected.
5. Ambient diagonal Taylor faithful flatness descends flatness of the actual
quotient stalk (lem-weil-pbc-faithfully-flat-base-change,
lem-weil-pbc-flat-algebra-faithfully-flat-descent). Use the affine stalk
identifications (lem-weil-pbc-affine-open-stalk-localization), and spread by
lem-weil-pbc-noetherian-flat-locus-neighborhood. If the ideal is a unit at a,
remove its closed zero scheme instead.
6. Lift this open to an ambient principal open, intersect with the inverse
image of D(c), and restrict the base by the section. This preserves etaleness
(lem-a1-etale-open-restriction), the section and formal equality because every
new denominator has invertible constant term. Stalkwise flatness is precisely
def-weil-flat-morphism.
7. For each point b, including nonclosed points, base change to its residue
field and use the rational diagonal. Flatness survives base change and
localization (lem-weil-pbc-flat-module-base-change,
lem-weil-pbc-flat-local-ring-maps), then completion
(lem-weil-pbc-flat-completion). The actual Taylor ideal is the coefficientwise
image of the completed regular ideal and is generated by the transported f_i.
8. For any Noetherian coefficient ring S, first base change the actual quotient
algebra, then complete along the pulled-back section. Use
lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-noetherian-completion-flat, lem-weil-pbc-flat-ring-map-comp and
lem-weil-pbc-completion-finite-module-tensor. Finite ideal identities identify
its completed ideal with the coefficientwise images of f_i. This includes
further field extension and subsequent centered diagonal completion. For an
empty list, faithful flat contraction and the finitely many regular generators
make the actual ideal vanish near a. Empty variable lists use the same formulas.
-/
theorem coherent_formal_generation_flatness {k : Type u} [Field k] [CharZero k]
    (U N : Scheme.{u}) [IsAffine U] [IsAffine N] {m n s : ℕ}
    (j : N ⟶ U) [IsClosedImmersion j]
    (c : MvPolynomial (Fin m ⊕ Fin n) k →+* Γ(U, ⊤))
    [Smooth (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)))]
    [LocallyOfFiniteType
      (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)))]
    [QuasiCompact (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)))]
    [Smooth (j ≫ U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)))]
    (hchart : Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)))
    (hw : Etale (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (j.appTop.hom.comp
      (c.comp (MvPolynomial.rename Sum.inl).toRingHom)))))
    (F : FormalSectionExpansion j n)
    (hFw : ∀ i : Fin m, F.regular (c (MvPolynomial.X (Sum.inl i))) =
      MvPowerSeries.C (j.appTop (c (MvPolynomial.X (Sum.inl i)))))
    (hFz : ∀ i : Fin n, F.regular (c (MvPolynomial.X (Sum.inr i))) =
      MvPowerSeries.C (j.appTop (c (MvPolynomial.X (Sum.inr i)))) + MvPowerSeries.X i)
    (hFk : ∀ r : k, F.regular (c (MvPolynomial.C r)) =
      MvPowerSeries.C (j.appTop (c (MvPolynomial.C r))))
    (J : U.IdealSheafData) (hJ : RingedSpace.IsCoherent U.toRingedSpace J.toModules)
    (f : Fin s → MvPowerSeries (Fin n) Γ(N, ⊤)) (a : N)
    (T : Γ(N, ⊤) →+* MvPowerSeries (Fin m) (N.residueField a))
    (hT : HilbertCoefficient.isTaylorMap
      (j.appTop.hom.comp (c.comp (MvPolynomial.rename Sum.inl).toRingHom))
      (N.Γevaluation a).hom T)
    (hgen : Ideal.map ((MvPowerSeries.map T).comp F.regular) (J.idealOfOpens ⊤) =
      Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map T (f i)))
    (hflat : ((Ideal.Quotient.mk
      (Ideal.map ((MvPowerSeries.map T).comp F.regular) (J.idealOfOpens ⊤))).comp
        MvPowerSeries.C).Flat) :
    Nonempty (CoherentFormalGenerationNeighbourhood.{u, v} j a c J F f) := by
  sorry

end AlgebraicGeometry
