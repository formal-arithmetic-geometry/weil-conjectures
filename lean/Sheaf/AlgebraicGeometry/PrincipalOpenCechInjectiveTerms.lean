/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # principal-open Čech augmentation for injective terms

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-injective-terms).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The finite subset Čech augmentation for a complex with injective terms
induces monomorphisms on homology, without any boundedness or K-injectivity assumption.

Source: Stacks Project, Cohomology, Tag 08C1, finite exact augmented row argument.
(blueprint: lem-sc-principal-open-cech-injective-terms).

Proof: Each I.X n is injective as a sheaf of modules and hence flasque. The augmented
Čech row for the finite cover of V is exact: sheaf separation gives injectivity at
sections, gluing identifies the degree-zero kernel, and injective-module Čech
acyclicity gives exactness in positive degrees. Restrict the tuple model to increasing
tuples, using the alternating Čech comparison, and identify increasing tuples with
finite subsets. Their deletion positions are exactly the displayed filter-cardinality
signs. These identifications give row exactness for the formulas in the statement.
Given a section cocycle whose augmentation is the boundary of t, start at the largest
Čech column of t. Its horizontal differential is zero because the boundary has no
components above column zero. Row exactness produces a horizontal primitive in the
preceding column. Subtract its total differential from t. This preserves the total
boundary and removes that column, changing only the preceding column. Iterate down
through the r finite columns. At column zero, exactness identifies the remaining
primitive as the augmentation of a section. The chain-map identity and injectivity
of the augmented row show that the given section is its vertical boundary. Thus the
kernel of each homology map is zero. The zero-module interpretation of sections on
the empty open proves the r=0 case; repeated and empty opens do not change exactness.
The proof uses injectivity of the terms, never K-injectivity of the complex. -/
theorem principalOpenCech_homology_mono_of_injective_terms
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hJ : ∀ n : ℤ, Injective (J.X n)) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∀ n : ℤ, Mono (HomologicalComplex.homologyMap α n) := by sorry

end AlgebraicGeometry
