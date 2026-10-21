/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Sheaf.Algebra.Homology.BoundedAboveProjectiveModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.Paper.ConstructibleRHomCoproductContinuity
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Universal coefficients for constructible derived internal Hom

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Proposition 10.1.1, printed pp. 325--326, uniformly bounded alternative
(blueprint: lem-per-ctf-hom-universal-coefficients).

The comparison is the actual evaluation transpose, using the signed derived symmetry.
Coefficients are ordinary modules, and Tor amplitude is tested against all module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The evaluation-induced comparison `V tensor RHom(K,Y) → RHom(K,V tensor Y)`.
Its transpose first reassociates, swaps K and V by the canonical signed symmetry,
reassociates again, and applies V tensored with evaluation.
Source: ILO XVII, proof of Proposition 10.1.1, first paragraph, p. 325
(blueprint: lem-per-ctf-hom-universal-coefficients). -/
def universalCoefficientHomMap
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K Y V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj V).obj (((derivedHom A X).obj (op K)).obj Y) ⟶
      ((derivedHom A X).obj (op K)).obj (((derivedTensor A X).obj V).obj Y) :=
  (derivedTensorHomAdjunction A K).homEquiv _ _
    ((derivedTensorAssociator A X K V (((derivedHom A X).obj (op K)).obj Y)).inv ≫
      ((derivedTensor A X).map (((derivedTensorSymmetry A X).hom.app K).app V)).app
        (((derivedHom A X).obj (op K)).obj Y) ≫
      (derivedTensorAssociator A X V K (((derivedHom A X).obj (op K)).obj Y)).hom ≫
      ((derivedTensor A X).obj V).map ((derivedTensorHomAdjunction A K).counit.app Y))

/-- Uniform boundedness with all ordinary constant-module coefficients implies finite Tor
amplitude of RHom(K,Y), and the canonical coefficient comparison is invertible for every
bounded-below ordinary coefficient complex. The final equation is simultaneous naturality
in K (contravariantly), Y and C.

Source: ILO XVII, Proposition 10.1.1 and its proof, pp. 325--326
(blueprint: lem-per-ctf-hom-universal-coefficients).

Proof:
1. Set H=RHom(K,Y), F(C)=C_X tensor H, G(C)=RHom(K,C_X tensor Y).
   Taking M=A bounds H in [d,e]. Choose K≤r and a Tor interval [a,b] for Y.
   Exact constant sheafification, derived tensor and internal Hom make F,G exact.
   The displayed evaluation transpose gives the natural comparison and cone squares.
2. For any free module V, including rank zero and infinite rank, constant sheafification
   and tensor commute with its direct sum. Its degree-zero constant complex is K-flat
   (lem-pc-bounded-above-flat-kflat-site). Apply
   lem-per-constructible-rhom-coproduct-continuity to copies of Y, with common lower bound a.
   On each basis inclusion the comparison is evaluation's transpose, hence the identity.
3. A projective module is a retract of a free module. Naturality supplies an inverse
   on the retract. A finite stupid filtration, shifts and cone exactness give the result
   for bounded projective complexes (lem-sf-derived-homology-long-exact,
   lem-weil-pbc-five-lemma, lem-weil-pbc-unbounded-derived-iso-cohomology).
4. For E≤q, a bounded-above projective model L and a representative of H zero above e
   compute F(E). Total degrees give F(E)≤q+e, without assuming H has finite Tor amplitude.
5. For bounded C, cut its bounded-above projective model brutally above q. This is a
   bounded projective complex P with cone E bounded and ≤q. The preceding bound for F
   and lem-pur-bounded-heart-amplitude for G bound F(E) and G(E) above q+e.
   The long exact sequences give comparison isomorphisms in degrees i>q+e+1. Letting
   q decrease proves invertibility in every fixed degree.
6. For every ordinary module N, Step 5 gives N_X tensor H in [d,e]. At a geometric
   point this tests H_x against every N. For an arbitrary module sheaf B take N=B_x;
   exact conservative geometric stalks and lem-sfb-etale-derived-tensor-stalk give the
   same interval for B tensor H globally. Thus the Tor test includes all sheaves.
7. By lem-sp-ringed-site-tor-flat-model use bounded flat representatives of H in [d,e]
   and Y in [a,b]. For T≥t, total degrees give F(T)≥t+d and T_X tensor Y≥t+a.
   A K-injective representative of the latter zero below t+a and K zero above r compute
   G(T) by the Hom complex, giving G(T)≥t+a-r.
8. For C bounded below, use τ≤n C → C → τ≥n+1 C. The last bounds make both tails
   vanish in any fixed degree for sufficiently large n. Step 5 and the natural square
   give invertibility on that cohomology, hence invertibility of the actual comparison.
   Evaluation, signed symmetry and transposition give the naturality in all three variables.
   No perfectness or finite Tor amplitude of C enters the argument.
-/
theorem hom_universal_coefficients
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) [IsNoetherian X] (K Y : DerivedCategoryModule A X)
    (_hK : ∃ r : ℤ, K.IsLE r)
    (_hc : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X K)
    (_hY : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X Y)
    (_hbounded : ∃ d e : ℤ, d ≤ e ∧ ∀ M : ModuleCat.{u + 1} A,
      ∀ i : ℤ, i < d ∨ e < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))).obj Y)))) :
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj Y) ∧
    (∀ C : _root_.DerivedCategory (ModuleCat.{u + 1} A),
      (∃ n : ℤ, C.IsGE n) →
        IsIso (universalCoefficientHomMap (ModuleCat.{u + 1} A) X K Y
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C))) ∧
    ∀ (K' Y' : DerivedCategoryModule A X)
      (C C' : _root_.DerivedCategory (ModuleCat.{u + 1} A))
      (f : K' ⟶ K) (g : Y ⟶ Y') (h : C ⟶ C'),
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} A)).mapDerivedCategory.map h)).app
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj Y) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C')).map
          (((derivedHom (ModuleCat.{u + 1} A) X).map f.op).app Y ≫
            ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K')).map g) ≫
        universalCoefficientHomMap (ModuleCat.{u + 1} A) X K' Y'
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C') =
      universalCoefficientHomMap (ModuleCat.{u + 1} A) X K Y
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C) ≫
        ((derivedHom (ModuleCat.{u + 1} A) X).map f.op).app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C)).obj
              Y) ≫
        ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K')).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} A)).mapDerivedCategory.map h)).app Y ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} A)).mapDerivedCategory.obj C')).map g) := by
  sorry

end AlgebraicGeometry.Etale
