/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.SixFunctors.EtaleHomThickLocus
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel
import Sheaf.Paper.CtfHomConditionB
import Sheaf.Paper.HomUniversalCoefficients

/-!
# Finite-Tor constructible internal Hom and change of coefficients

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Theorem 7.6.1, pp. 310--311, proof p. 314; Definition 7.7.1, p. 314
(blueprint: lem-per-ctf-hom-coefficient-comparison).

## Main definitions

- `ctfHomBidualMap`: the canonical evaluation-transpose biduality arrow.
- `ctfHomCoefficientMap`: scalar-extended evaluation's tensor--Hom transpose.

## Main statements

- `ctf_hom_coefficient_comparison`: internal-Hom stability, scalar-extension stability,
  and natural invertibility of the specified comparison, without coefficient flatness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The evaluation-transpose map into the double dual with values in Q.
The symmetry is the canonical descent of the Koszul signed swap of complexes.
Source: ILO, Expose XVII, duality hypothesis of Theorem 7.6.1, p. 310
(blueprint: lem-per-ctf-hom-coefficient-comparison). -/
def ctfHomBidualMap (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (P Q : DerivedCategoryModule R X) :
    P ⟶ ((derivedHom (ModuleCat.{u + 1} R) X).obj
      (op (((derivedHom (ModuleCat.{u + 1} R) X).obj (op P)).obj Q))).obj Q :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} R)
    (((derivedHom (ModuleCat.{u + 1} R) X).obj (op P)).obj Q)).homEquiv _ _
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app
          (((derivedHom (ModuleCat.{u + 1} R) X).obj (op P)).obj Q)).app P ≫
        (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) P).counit.app Q)

/-- The coefficient comparison is the transpose of extended evaluation.
This is the component of the existing comparison from etaleHomComparison_thickLocus.
Its IsEtaleHomTranspose equation uses etaleHomTensorComparison, normalized by ordinary
scalar balancing, to take TP tensor T(Hom(P,L)) to T(P tensor Hom(P,L)).
Source: ILO, Expose XVII, Theorem 7.6.1, pp. 310--311, final proof paragraph p. 314
(blueprint: lem-per-ctf-hom-coefficient-comparison). -/
def ctfHomCoefficientMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (P L : DerivedCategoryModule A X) :
    (scalarExtension φ X).obj
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op P)).obj L) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((scalarExtension φ X).obj P))).obj ((scalarExtension φ X).obj L) :=
  ((etaleHomComparison_thickLocus X φ).choose L).app (op P)

/-- Finite-Tor constructible internal Hom is stable under arbitrary Noetherian
coefficient extension, and the evaluation-defined comparison is naturally invertible.
Source: ILO, Expose XVII, Theorem 7.6.1, pp. 310--311 and proof p. 314;
Definition 7.7.1 and the following paragraph, p. 314
(blueprint: lem-per-ctf-hom-coefficient-comparison).

Proof plan:
1. Apply lem-per-noetherian-ctf-flat-model to L, obtaining a bounded flat constructible
model with a single Galois partition trivializing every term. Tensoring with any ordinary
A-module M keeps the same partition and the same degree interval [a,b]. Kernels, images
and quotients of the constant complexes remain constant on its connected covers. Taking
M=A also places L in this partition class.
2. Apply lem-per-ctf-hom-condition-b to P and that partition. The Noetherian hypotheses
and the prime-field duality hypothesis give r,c independent of M, so Hom(P,M tensor L)
has cohomology in [a-r,b+c]. Its final constructibility clause applied to L makes
H=Hom(P,L) bounded constructible. Finite generation is used here only for M=A.
3. Apply lem-per-ctf-hom-universal-coefficients to P,L and that common interval.
It gives finite Tor amplitude against all module sheaves and invertibility of the
canonical u_C for every bounded-below ordinary coefficient complex C. Thus H is ctf.
4. Tensor a bounded flat constructible model of any ctf K with B. Flatness survives
extension since tensor over B cancels the B-extension. Finite projective constant terms
stay finite projective after extension, including rank zero. Noetherianity of B makes
their cohomology finitely generated. Thus extension preserves ctf for P,L,H without
assuming that B is flat or finitely generated over A.
5. Take C=B[0] in step 3. The evaluation-normalized scalar adjunction of
lem-sfb-dc-hom-scalar-adjunction identifies the restricted coefficient comparison with
u_B: insert the scalar unit and transpose both maps. Both become extended evaluation,
with coefficient 1*b=b and identical Koszul signs. Uniqueness of the transpose follows
from lem-weil-pbc-ringed-internal-hom-exact-restriction and lem-pur-rhom-global-sections.
Restriction reflects isomorphisms, proving invertibility of this actual map. Step 4
puts its source, and hence its target, in ctf. Naturality of evaluation, scalar tensor
comparison and transposition gives the displayed two-variable naturality equation. -/
theorem ctf_hom_coefficient_comparison
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod l) A]
    (hDual : ∃ Q : DerivedCategoryModule (ULift.{u + 1} (ZMod l)) X,
      DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod l)) X Q ∧
      ∀ P : DerivedCategoryModule (ULift.{u + 1} (ZMod l)) X,
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod l)) X P →
          DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod l)) X
            (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) X).obj
              (op P)).obj Q) ∧
          IsIso (ctfHomBidualMap (ULift.{u + 1} (ZMod l)) X P Q)) :
    (∀ P L : DerivedCategoryModule A X,
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X P →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op P)).obj L)) ∧
    (∀ (B : Type (u + 1)) [CommRing B] [IsNoetherianRing B] (φ : A →+* B),
      (∀ K : DerivedCategoryModule A X,
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K →
          DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X
            ((scalarExtension φ X).obj K)) ∧
      (∀ P L : DerivedCategoryModule A X,
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X P →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L →
          IsIso (ctfHomCoefficientMap X φ P L) ∧
          DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) X
            (((derivedHom (ModuleCat.{u + 1} B) X).obj
              (op ((scalarExtension φ X).obj P))).obj ((scalarExtension φ X).obj L))) ∧
      (∀ (P P' L L' : DerivedCategoryModule A X),
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X P →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X P' →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L' →
        ∀ (f : P' ⟶ P) (g : L ⟶ L'),
          (scalarExtension φ X).map
              (((derivedHom (ModuleCat.{u + 1} A) X).map f.op).app L ≫
                ((derivedHom (ModuleCat.{u + 1} A) X).obj (op P')).map g) ≫
              ctfHomCoefficientMap X φ P' L' =
            ctfHomCoefficientMap X φ P L ≫
              ((derivedHom (ModuleCat.{u + 1} B) X).map
                ((scalarExtension φ X).map f).op).app ((scalarExtension φ X).obj L) ≫
              ((derivedHom (ModuleCat.{u + 1} B) X).obj
                (op ((scalarExtension φ X).obj P'))).map ((scalarExtension φ X).map g))) := by
  sorry

end AlgebraicGeometry.Etale
