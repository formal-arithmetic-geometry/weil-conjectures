/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Algebra.Homology.CoinductionTotalHomModel
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Simultaneous shifts and scalar normalization for coinduction

Source: Stacks Project, dualizing.tex, Tag 0BZW, proof of (1)(c), and Tags 0A70,
0A71; derived.tex, Tag 070H (blueprint: lem-trf-coinduction-shift-scalar-model).

The comparison structure only packages the isomorphisms and their coordinate
characterization. All complexes, cochains, shifts and coinduction functors are the
existing constructions. Shifted transposition below is evaluation at one after the
identity component identifications for termwise restriction and coinduction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u wP wA

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace CochainComplex

/-- The signed simultaneous-shift comparison for product total Hom complexes.
`component` is the formula sigma(f)^p = (-1)^(nr) f^(p-n), with the two index
identifications displayed explicitly. `naturality` concerns both variables;
`ofHom` says its degree-zero action is inverse shift on chain maps.
Source: Stacks 0BZW, proof of (1)(c)
(blueprint: lem-trf-coinduction-shift-scalar-model). -/
structure ModuleHomShiftComparison (R : Type u) [CommRing R] where
  iso : ∀ (L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ),
    moduleHomComplex (L⟦n⟧) (M⟦n⟧) ≅ moduleHomComplex L M
  component : ∀ (L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (n r p q p' q' : ℤ) (hpq : p + r = q) (hpq' : p' + r = q')
    (hp : p = p' + n) (hq : q = q' + n) (z : Cochain (L⟦n⟧) (M⟦n⟧) r),
    ((iso L M n).hom.f r z).v p q hpq = (n * r).negOnePow •
      ((L.shiftFunctorObjXIso n p' p hp).inv ≫ z.v p' q' hpq' ≫
        (M.shiftFunctorObjXIso n q' q hq).hom)
  naturality : ∀ (L L' M M' : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : L' ⟶ L) (b : M ⟶ M') (n r : ℤ) (z : Cochain (L⟦n⟧) (M⟦n⟧) r),
    (iso L' M' n).hom.f r
        (((Cochain.ofHom (a⟦n⟧')).comp
          (z.comp (Cochain.ofHom (b⟦n⟧')) (add_zero r)) (zero_add r))) =
      (Cochain.ofHom a).comp
        (((iso L M n).hom.f r z).comp (Cochain.ofHom b) (add_zero r)) (zero_add r)
  ofHom : ∀ (L M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (f : L ⟶ M),
    (iso L M n).hom.f 0 (Cochain.ofHom (f⟦n⟧')) = Cochain.ofHom f

end CochainComplex

namespace ModuleCat

/-- Signed shift cancellation is compatible with coinduction transposition and
identifies shifted multiplication with coefficient evaluation as actual chain maps.
The existential comparisons are fixed by their component formulas, not arbitrary
isomorphisms. The derived comparison is the mate of the canonical restriction shift.
The `t` family is T on shifted complexes transported through the identity component
identifications J(K[n]) = J(K)[n] and U(E[n]) = (UE)[n].

Source: Stacks 0BZW, proof of (1)(c), 0A70, 0A71, and 070H
(blueprint: lem-trf-coinduction-shift-scalar-model).

Proof:
1. Reindex each product factor by p-n and multiply a degree-r cochain by
   epsilon^r, epsilon = (-1)^n (def-sc-module-total-hom-complex). The inverse
   reindexes by p+n with the same sign. The shifted differential is epsilon
   times the original differential, and epsilon^(r+2) = epsilon^r, giving a
   chain isomorphism without a support or boundedness condition.
2. Precomposition and postcomposition commute with this reindexing and sign.
   In degree zero the sign is one, giving the usual inverse shift of chain maps.
3. For an acyclic N, N[-n] is acyclic. A map N to K[n] is a map N[-n] to K.
   Choose its null-homotopy k using def-pur-kinjective-complex and put
   h^i = epsilon k^(i+n); then d h + h d is the original map. This proves
   shift preservation of K-injectivity (def-weil-abstract-derived-category).
4. The coinduced term is Hom_P(A,K^i), with differential d_K postcomposition
   and action (ah)(b)=h(ba), by lem-trf-coinduction-total-hom-model. Thus
   J(K[n]) and J(K)[n] have identical terms, differentials and A-actions;
   postcomposition makes this natural. A shifted K-injective representative
   therefore computes the canonical shift comparison of def-trf-derived-coinduction.
   Both counits evaluate at one, which fixes the adjunction-mate normalization.
5. For a degree-r cochain the two transposition/shift composites both evaluate
   to epsilon^r f^(i-n)(x)(1), by lem-trf-coinduction-total-hom-model.
6. Multiplication by a is A-linear since A is commutative. It commutes with
   the A-linear differential, so it is a degree-zero cocycle and defines m_n
   on A[0] (def-sc-module-total-hom-complex).
7. The final composite sends (a,h) to (ah)(1)=h(a); its degree-zero sign is
   one. The component maps therefore agree as chain maps, and delta is a chain
   map. No bounds, perfectness, flatness or Noetherianity were used. -/
theorem coinduction_shift_scalar_model {P A : Type u} [CommRing P] [CommRing A]
    (φ : P →+* A) [HasDerivedCategory.{wP} (ModuleCat.{u} P)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)] :
    ∃ (σP : ModuleHomShiftComparison P) (σA : ModuleHomShiftComparison A)
      (j : ∀ (K : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ),
        (coinductionComplexFunctor φ).obj (K⟦n⟧) ≅
          ((coinductionComplexFunctor φ).obj K)⟦n⟧)
      (T : ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (K : CochainComplex (ModuleCat.{u} P) ℤ),
        ((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
            (moduleHomComplex E ((coinductionComplexFunctor φ).obj K)) ≅
          moduleHomComplex (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) K)
      (t : ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (K : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ),
        ((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
            (moduleHomComplex (E⟦n⟧) (((coinductionComplexFunctor φ).obj K)⟦n⟧)) ≅
          moduleHomComplex
            ((((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E)⟦n⟧) (K⟦n⟧)),
      (∀ (K : CochainComplex (ModuleCat.{u} P) ℤ) (n i : ℤ),
        (j K n).hom.f i = 𝟙 _) ∧
      (∀ (K K' : CochainComplex (ModuleCat.{u} P) ℤ) (a : K ⟶ K') (n : ℤ),
        (coinductionComplexFunctor φ).map (a⟦n⟧') ≫ (j K' n).hom =
          (j K n).hom ≫ ((coinductionComplexFunctor φ).map a)⟦n⟧') ∧
      (∀ (K : CochainComplex (ModuleCat.{u} P) ℤ) (n : ℤ),
        K.IsKInjective → (K⟦n⟧).IsKInjective) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ),
        K.IsKInjective → (K⟦n⟧).IsKInjective) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (K : CochainComplex (ModuleCat.{u} P) ℤ) (r p q : ℤ) (hpq : p + r = q)
        (z : Cochain E ((coinductionComplexFunctor φ).obj K) r) (x : E.X p),
        (((T E K).hom.f r z).v p q hpq) x =
          CoextendScalars.equiv φ (K.X q) (z.v p q hpq x) (1 : A)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (K : CochainComplex (ModuleCat.{u} P) ℤ) (n r p q : ℤ) (hpq : p + r = q)
        (z : Cochain (E⟦n⟧) (((coinductionComplexFunctor φ).obj K)⟦n⟧) r)
        (x : (E⟦n⟧).X p),
        (((t E K n).hom.f r z).v p q hpq) x =
          CoextendScalars.equiv φ (K.X (q + n)) (z.v p q hpq x) (1 : A)) ∧
      (∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
        (K : CochainComplex (ModuleCat.{u} P) ℤ) (n r : ℤ)
        (z : Cochain (E⟦n⟧) (((coinductionComplexFunctor φ).obj K)⟦n⟧) r),
        (σP.iso (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj E) K n).hom.f r
            ((t E K n).hom.f r z) =
          (T E K).hom.f r ((σA.iso E ((coinductionComplexFunctor φ).obj K) n).hom.f r z)) ∧
      (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) [I.IsKInjective]
        (_e : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)))
        (n : ℤ),
        (derivedCoinduction φ).map ((DerivedCategory.Q.commShiftIso n).hom.app I) ≫
            (Functor.commShiftIso (derivedCoinduction φ)
              (self := (derivedCoinductionAdjunction φ).rightAdjointCommShift ℤ) n).hom.app
                (DerivedCategory.Q.obj I) ≫
            (derivedCoinductionModel φ I).hom⟦n⟧' =
          (derivedCoinductionModel φ (I⟦n⟧)).hom ≫ DerivedCategory.Q.map (j I n).hom ≫
            (DerivedCategory.Q.commShiftIso n).hom.app ((coinductionComplexFunctor φ).obj I)) ∧
      (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) [I.IsKInjective]
        (_e : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P))),
        ∃ (m : ∀ n : ℤ,
          (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
              ((restrictScalars φ).obj (ModuleCat.of A A)) ⟶
            ((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
              (moduleHomComplex (((coinductionComplexFunctor φ).obj I)⟦n⟧)
                (((coinductionComplexFunctor φ).obj I)⟦n⟧)))
          (δI : (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
              ((restrictScalars φ).obj (ModuleCat.of A A)) ⟶
            moduleHomComplex
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
                ((coinductionComplexFunctor φ).obj I)) I),
          (∀ (n p : ℤ) (a : A)
            (h : (((coinductionComplexFunctor φ).obj I)⟦n⟧).X p),
            (((m n).f 0 ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
              ((restrictScalars φ).obj (ModuleCat.of A A))).inv a)).v p p (add_zero p)) h =
                a • h) ∧
          (∀ (p : ℤ) (a : A) (h : ((coinductionComplexFunctor φ).obj I).X p),
            ((δI.f 0 ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
              ((restrictScalars φ).obj (ModuleCat.of A A))).inv a)).v p p (add_zero p)) h =
                CoextendScalars.equiv φ (I.X p) h a) ∧
          (∀ n : ℤ, m n ≫ (t ((coinductionComplexFunctor φ).obj I) I n).hom ≫
            (σP.iso
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
                ((coinductionComplexFunctor φ).obj I)) I n).hom = δI)) := by
  sorry

end ModuleCat
