/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Flat finitely presented module sheaves are locally finite free retracts

Source: Stacks Project, Modules on Sites, Tag 08FD
(blueprint: lem-sf-site-flat-fp-finite-retract).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A flat module sheaf with local finite presentations is locally a retract of a
finite free module sheaf. Finite products of the structure module represent finite
free modules, since finite products and finite coproducts agree in this abelian category.
Source: Stacks Project, Modules on Sites, Tag 08FD
(blueprint: lem-sf-site-flat-fp-finite-retract).

Proof:
1. Fix U and choose its covering by finite presentations A : O^r → O^s and q : O^s → N.
   On the localized site, maps from finite free modules are specified by sections;
   thus A is a finite matrix and qA = 0 is its finite family of relations.
2. Induct on the number m of columns of any finite matrix A killed by g : O^n → N.
   The claim is that locally g = pB with B landing in a finite free module and BA = 0.
   For m = 0 take B = id and p = g, on the identity covering.
3. For m > 0 use lem-weil-pbc-site-flat-equational-criterion on the last column.
   Its coefficients b_pq and sections t_q give B and p with pB = g, killing that column.
4. Apply the induction hypothesis to the other m - 1 columns of BA and p. Compose
   the matrices and the coverings; the resulting matrix kills every column of A.
   Relocalization identifies iterated restriction with direct restriction.
5. Apply the claim to the finite presentation. By
   lem-pur-site-restriction-module-adjunction-exact, restriction preserves its cokernel.
   The restricted q is still a cokernel of the restricted A.
6. Since BA = 0, descend B uniquely along q to i : N → O^l. Then (pi)q = pB = q.
   Cancel the cokernel epimorphism q to get pi = id.
7. Compose the coverings to obtain the conclusion over the original U. Zero ranks
   and empty covering families are included throughout. -/
theorem exists_local_finiteFree_retract_of_flat_of_finitePresentation
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J CommRingCat.{max uC vC r})
    (N : ringedSiteModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))
    (hflat : IsFlatOnSite (J := J) (R := R) N)
    (hfp : N.IsFinitePresentation) :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ (n : ℕ)
          (i : N.over V ⟶ (∏ᶜ fun _ : Fin n ↦ unit
            (((sheafCompose J
              (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over V)))
          (p : (∏ᶜ fun _ : Fin n ↦ unit
            (((sheafCompose J
              (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over V)) ⟶
            N.over V), i ≫ p = 𝟙 (N.over V) := by
  sorry

end SheafOfModules
