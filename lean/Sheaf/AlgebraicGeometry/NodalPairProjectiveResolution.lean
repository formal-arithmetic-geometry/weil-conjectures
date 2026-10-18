/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.NormalCrossingsStrictification
import Sheaf.SixFunctors.TraceFormula.NodalLogRegularity
import Sheaf.TraceFormula.DivisorialLogChart
import Sheaf.TraceFormula.LogRegularDesingularization

/-!
# Resolution of a nodal curve over a smooth normal crossings pair

Source: ILO, Travaux de Gabber, Expose X, proof of Lemma 2.2, pp. 149--150;
Expose VI, 1.4--1.9; Expose VIII, 3.4.8--3.4.9 and 4.1.1--4.1.8
(blueprint: lem-trf-nodal-pair-projective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A projective nodal curve over a smooth integral strict normal crossings pair has a proper
birational smooth resolution on which the reduced total marked boundary has strict normal
crossings. The marking is a finite etale effective Cartier divisor in the relative smooth
locus. Birationality is expressed by an isomorphism between dense open subschemes commuting
with the given modification. The reduced total inverse-image ideal is the radical of the
intersection of the marking ideal with the pulled-back base-boundary ideal.
Source: ILO, Expose X, proof of Lemma 2.2, pp. 149--150; Expose VI, 1.4--1.9;
Expose VIII, 3.4.8--3.4.9 and 4.1.1--4.1.8
(blueprint: lem-trf-nodal-pair-projective-resolution).

Proof:
1. Projectivity implies properness by `lem-kun-projective-implies-proper`, hence finite type.
Compose finite-type morphisms by `lem-sfb-finite-type-composition-base-change` to see that X
is finite type over F. Since Spec F is Noetherian, `lem-weil-pbc-finite-type-over-noetherian`
makes Y and X Noetherian.
2. Apply `lem-trf-snc-divisorial-log-chart` to the smooth normal crossings pair (Y,T).
The local monoids are N^r, so the pair is log regular, including for empty T.
3. Put B = |D| union f^{-1}|T|. The proper flat finitely presented nodal family, smooth off T,
and its etale smooth marking satisfy `lem-trf-nodal-log-regularity`. Thus B is nowhere dense
and (X,B) is log regular. Global separation of local branches is not required.
4. Apply `lem-trf-log-regular-desingularization`: obtain a proper modification p : X1 -> X
with X1 integral regular and finite type, isomorphic over U = X minus B with dense inverse
image, and reduced inverse-image boundary B1 a normal crossings Cartier divisor.
5. Apply `lem-trf-normal-crossings-strictification` to (X1,B1). It gives a proper q : X2 -> X1,
with X2 integral smooth over F and reduced inverse-image boundary B2 strict normal crossings,
while preserving the complement of the boundary.
6. Set r = q followed by p. It is proper by `lem-weil-pbc-proper-composition`. Both maps are
isomorphisms over the nonempty dense U. Its inverse image is a nonempty open in integral X2,
hence dense, giving the required dense-open isomorphism. Inverse images compose, and
`def-weil-pbc-scheme-reduction` preserves support, so the reduced total inverse image is B2. -/
theorem exists_nodal_pair_projective_resolution
    (F : Type u) [Field F] [IsAlgClosed F]
    (Y : Scheme.{u}) [Y.Over (Spec (.of F))] [IsIntegral Y]
    [Smooth (Y ↘ Spec (.of F))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F))] [QuasiCompact (Y ↘ Spec (.of F))]
    (T : Y.IdealSheafData)
    (hT : T.IsStrictNormalCrossingsDivisor (Y ↘ Spec (.of F)))
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Y)
    [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    [Smooth (f.fiberToSpecResidueField η)]
    [GeometricallyIntegral (f.fiberToSpecResidueField η)]
    (hfib : HasNodalGeometricFibres f)
    (hsmooth : ∀ x : X, f x ∉ T.support → x ∈ f.smoothLocus)
    (D : X.IdealSheafData) (hD : D.IsInvertible)
    [IsFinite (D.subschemeι ≫ f)] [Etale (D.subschemeι ≫ f)]
    (hmark : ∀ d : D.subscheme, D.subschemeι d ∈ f.smoothLocus) :
    ∃ (X' : Scheme.{u}) (r : X' ⟶ X),
      IsProper r ∧ IsIntegral X' ∧ Smooth (r ≫ f ≫ Y ↘ Spec (.of F)) ∧
      (∃ (U : X.Opens) (V : X'.Opens) (e : V.toScheme ≅ U.toScheme),
        Dense (U : Set X) ∧ Dense (V : Set X') ∧ e.hom ≫ U.ι = V.ι ≫ r) ∧
      ((D ⊓ T.comap f).comap r).radical.IsStrictNormalCrossingsDivisor
        (r ≫ f ≫ Y ↘ Spec (.of F)) := by
  sorry

end AlgebraicGeometry
