/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Paper.ModuleCupGodementModel
import Sheaf.Paper.ModuleCupGodementModelsExist
import Sheaf.Paper.ModuleCupGodementModelQuasiIso
import Sheaf.Paper.ModuleCupGodementObjectFlasque
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.Paper.ModuleCupFlasqueAcyclicity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.Localization
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Paper.FiniteOrderedFlasqueCechComparison
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Functorial augmented ring complexes

Source: Stacks Project, algebraization.tex, Tag 099D, lemma-all-rings, clauses (a)-(d)
(blueprint: lem-weil-pbc-ring-complex-functorial).

All complexes use modules on the existing one-object bottom-topology site. Semilinear
chain maps are given on the unique object's sections. Scalar extension of a K-flat
replacement is specified term by term, including its differential and the pure-tensor
normalization of the induced map. This is the total tensor with the target ring in
degree zero. The localization complex is specified by coordinates, including its
differential, rather than by choosing an unspecified complex with the same terms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- Stacks Project, Tag 099D(a)-(d)
(blueprint: lem-weil-pbc-ring-complex-functorial).

Proof plan:
1. Use the concrete Godement monad of def-sc-module-cup-godement-model and its alternating
   coface resolution (lem-sc-module-cup-godement-model-pairing-models-exist). Its augmentation
   is a quasi-isomorphism by lem-sc-module-cup-godement-model-quasi-iso and each term is
   flasque by lem-sc-module-cup-godement-object-flasque, including on empty schemes.
2. A ring map induces a map on the open complements of the ideals. On Godement products
   select the component at the image point and apply the induced stalk map. Iteration
   commutes with cofaces, units, compositions and augmentations componentwise.
3. Put A in degree zero, followed by sections of the Godement resolution of the structure
   module on Spec A minus V(I), shifted one degree to the right. Restriction followed by
   germ augmentation is the first differential. Step 2 supplies the semilinear chain maps.
4. For a finite generating list, compare the Godement section complex with the ordered
   principal-open Cech complex through the finite Cech double total. The intersections
   are affine by lem-weil-pbc-principal-localization-open-immersion; their sections are
   the localizations by lem-weil-pbc-spec-module-tilde-sections. Quasi-coherence follows
   from lem-weil-pbc-spec-tilde-free-module. Use pqf-lem-affine-vanishing and
   lem-sc-module-cup-flasque-acyclicity, with enough injectives from
   lem-sc-ringed-space-module-sheaves-enough-injectives and the bounded-below acyclic-unit
   comparison src-right-derived-functor-plus-acyclic-unit. Then apply
   lem-weil-pbc-finite-ordered-flasque-cech-comparison. The sums in each total degree are
   finite. The comparison is natural in the ring map.
5. Adjoin A in degree zero to the augmented comparison roof, shifting all former terms
   by one without changing signs. In degrees zero and one its cohomology is respectively
   the kernel and cokernel of A to H^0 of the former complex; in higher degrees it is
   the shifted former cohomology. Both roof arrows remain quasi-isomorphisms and are
   identity on A. Inverting the roof gives the augmentation-compatible derived isomorphism.
6. All localization terms are flat by lem-weil-pbc-localization-flat. The finite Cech
   complex is bounded and hence K-flat by lem-pc-bounded-above-flat-kflat-site. The
   fraction formulas identify its tensor with B with the localization complex of the
   image list, commuting with the differentials. Naturality of the roof makes this
   the induced map, so every K-flat replacement computes the asserted isomorphism.
   The empty list gives A[0]; zero rings, zero and repeated generators are included. -/
theorem exists_functorial_ringComplex
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{w} (RingSiteModules A)] :
    ∃ (K : ∀ A : CommRingCat.{u}, {I : Ideal A // I.FG} →
          CochainComplex (RingSiteModules A) ℤ)
      (ε : ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}),
        K A I ⟶ (HomologicalComplex.single (RingSiteModules A) (ComplexShape.up ℤ) 0).obj
          (@id (RingSiteModules A)
            (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf.{u} A)))))
      (m : ∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG}),
        I.val.map φ = J.val → ∀ n : ℤ,
          ((K A I).X n).val.obj (op ⟨PUnit.unit⟩) →ₛₗ[φ]
            ((K B J).X n).val.obj (op ⟨PUnit.unit⟩)),
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val) (n k : ℤ)
        (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m A B φ I J h k (((K A I).d n k).val.app (op ⟨PUnit.unit⟩) x) =
          ((K B J).d n k).val.app (op ⟨PUnit.unit⟩) (m A B φ I J h n x)) ∧
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val)
        (x : ((K A I).X 0).val.obj (op ⟨PUnit.unit⟩)),
        ((ε B J).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf.{u} B)))).hom).val.app (op ⟨PUnit.unit⟩)
          (m A B φ I J h 0 x) =
          φ (((ε A I).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
              (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app (op ⟨PUnit.unit⟩) x)) ∧
      (∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG})
        (h : I.val.map (RingHom.id A) = I.val) (n : ℤ)
        (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m A A (RingHom.id A) I I h n x = x) ∧
      (∀ (A B D : CommRingCat.{u}) (φ : A →+* B) (ψ : B →+* D)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (L : {L : Ideal D // L.FG}) (h : I.val.map φ = J.val)
        (h' : J.val.map ψ = L.val) (h'' : I.val.map (ψ.comp φ) = L.val)
        (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)),
        m B D ψ J L h' n (m A B φ I J h n x) = m A D (ψ.comp φ) I L h'' n x) ∧
      (∀ (A B : CommRingCat.{u}) (φ : A →+* B)
        (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
        (h : I.val.map φ = J.val) (P : CochainComplex (RingSiteModules A) ℤ)
        (p : P ⟶ K A I), P.IsKFlat → QuasiIso p →
        ∃ (E : CochainComplex (RingSiteModules B) ℤ)
          (t : ∀ n : ℤ, E.X n ≅
            SheafOfModules.changeOfRings.{u, u, u} (ringSiteMap.{u} φ) (P.X n)),
          (∀ n k : ℤ, E.d n k ≫ (t k).hom = (t n).hom ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} (ringSiteMap.{u} φ) (P.X n) (P.d n k)) ∧
          ∃ χ : E ⟶ K B J, IsIso (DerivedCategory.Q.map χ) ∧
            ∀ (n : ℤ) (x : (P.X n).val.obj (op ⟨PUnit.unit⟩)),
              (χ.f n).val.app (op ⟨PUnit.unit⟩)
                ((t n).inv.val.app (op ⟨PUnit.unit⟩)
                  ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
                    (ringSiteMap.{u} φ) (P.X n)).presheaf).app (op ⟨PUnit.unit⟩)
                    ((1 : B) ⊗ₜ[A, φ] x))) =
                m A B φ I J h n ((p.f n).val.app (op ⟨PUnit.unit⟩) x)) ∧
      (∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}) (r : ℕ)
        (f : Fin r → A), Ideal.span (Set.range f) = I.val →
        ∃ (C : CochainComplex (RingSiteModules A) ℤ)
          (a : C ⟶ (HomologicalComplex.single (RingSiteModules A) (ComplexShape.up ℤ) 0).obj
            (@id (RingSiteModules A)
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))))
          (e₀ : (C.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
          (e : ∀ q : ℕ, (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
            ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
          (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
            Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
              Localization.Away (∏ i, f (t i))),
          (∀ n : ℤ, n < 0 → IsZero (C.X n)) ∧
          (∀ (x : (C.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
            e 0 ((C.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
              algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x)) ∧
          (∀ (q : ℕ) (x : (C.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
            (t : Fin (q + 2) ↪o Fin r),
            e (q + 1) ((C.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app
              (op ⟨PUnit.unit⟩) x) t =
              ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
                l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) ∧
          (∀ x : (C.X 0).val.obj (op ⟨PUnit.unit⟩),
            (a.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (SheafOfModules.unit.{u, u, u} ((sheafCompose ⊥
                (forget₂ CommRingCat.{u} RingCat.{u})).obj
                  (CochainComplex.onePointRingSheaf.{u} A)))).hom).val.app
                    (op ⟨PUnit.unit⟩) x = e₀ x) ∧
          ∃ α : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj (K A I),
            α.hom ≫ DerivedCategory.Q.map (ε A I) = DerivedCategory.Q.map a) := by
  sorry

end AlgebraicGeometry
