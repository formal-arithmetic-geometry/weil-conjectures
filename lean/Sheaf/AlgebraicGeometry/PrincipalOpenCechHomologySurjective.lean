/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # surjective on cohomology for the principal-open Čech augmentation

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-homology-surjective).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The principal-open section-to-total augmentation is surjective on cohomology.
The source and target are specified by degree isomorphisms and the actual differential
and augmentation formulas; no choice of unspecified Čech data occurs.

Source: Stacks Project, Cohomology, Tag 08C1 (lemma-alternating-cech-complex-complex).
(blueprint: lem-sc-principal-open-cech-homology-surjective).

Proof: Take a functorial K-injective resolution I of J with injective terms.
The comparison J → I is a homotopy equivalence, since both complexes are K-injective.
Sections carry its homotopies to homotopies. For the displayed total differential,
apply the coefficient homotopy in the component of Čech degree p with sign (-1)^p.
Restriction naturality cancels the horizontal terms, and the two vertical signs
multiply to one. Thus totalization also carries this comparison to a homotopy
equivalence. The augmentation commutes with the comparison by its singleton
restriction formula and its zero formula on larger subsets.
For I, each augmented section row is exact: the sheaf axiom gives exactness and
injectivity at the section term, and injective Čech acyclicity gives positive-degree
exactness. Restriction to increasing tuples identifies these rows with the subset
rows, since each subset has a unique increasing enumeration and the deletion signs
are the corresponding positions. Only columns -1 through r-1 can occur.
Given a total cocycle, solve the horizontal equation for its highest nonzero
Čech-degree component using row exactness, and subtract the total differential of
that preimage. This removes the highest component and changes only the previous
column. Repeat finitely many times down to Čech degree zero. Exactness at that
column identifies the remaining component with a section over V; injectivity of
the row augmentation and the vertical cocycle equation show that this section is
closed. Thus every total cohomology class comes from a section cohomology class.
Transfer this surjective assertion back along the two homotopy equivalences.
For r=0 the union is empty; sections and the total are zero, so the assertion holds.
Repeated or empty principal opens do not affect row exactness or the argument. -/
theorem principalOpenCech_homology_surjective
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
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
      ∀ n : ℤ, Epi (HomologicalComplex.homologyMap α n) := by
  sorry

end AlgebraicGeometry
