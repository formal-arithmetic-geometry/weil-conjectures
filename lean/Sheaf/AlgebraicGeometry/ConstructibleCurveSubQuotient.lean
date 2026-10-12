/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Subobjects and quotients of constructible torsion sheaves on curves

Source: Stacks Project, Etale Cohomology, Proposition 09BH (2), with Definition 03RW
and Lemma 095E (blueprint: lem-weil-pbc-curve-constructible-sub-quotient).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.CurveCoefficientPair

/-- In a short exact sequence of torsion abelian sheaves on a curve, constructibility of
its middle term implies constructibility of both outer terms. Source: Stacks Project,
Etale Cohomology, Proposition 09BH (2), Definition 03RW and Lemma 095E
(blueprint: lem-weil-pbc-curve-constructible-sub-quotient).

Proof following the node's six steps:
1. The curve `P.C` is Noetherian, since it is of finite type over a field. A finite
   constructible stratification of `P.F`, quasi-compactness of the strata and openness of
   etale maps give finitely many finite constant groups on trivializing etale covers.
   Choose a positive integer `N` killing all these groups. Pullback-stalk comparisons
   (`lem-weil-pbc-inverse-image-stalk-germ`) and exactness of geometric stalks
   (`prop-weil-pbc-geometric-stalks-exact`) show that the image of `N` on `P.F` has zero
   stalks. Detection of monomorphisms by stalks
   (`lem-weil-pbc-geometric-stalks-detect-mono`) implies `N` kills `P.F`.
2. Monicity of `α` and epicity of `β` imply `N` also kills `F₁` and `F₂`.
   Sheaves killed by `N` form the full subcategory of abelian sheaves of `Z/N`-module
   sheaves (`def-weil-pbc-etale-sheaves`, `def-weil-pbc-abelian-etale-sheaves`), closed
   under subobjects and quotients. The same sequence is short exact there.
3. By `lem-weil-pbc-constructible-torsion-modules-agree`, `P.F` is constructible as a
   `Z/N`-module sheaf. On the Noetherian curve every locally closed stratum is
   constructible (`def-weil-constructible-subset`), so the module notions agree.
4. Apply `lem-weil-pbc-constructible-subobjects-noetherian` to the image of `α`.
   Monicity identifies it with `F₁`. Constructibility is invariant under isomorphism:
   inverse image transports the isomorphism, and the same local trivializations serve
   (`def-weil-pbc-inverse-image`, `def-weil-pbc-etale-constructible-sheaf`).
5. Exactness identifies `F₂` with the cokernel of `α`. Since `F₁` and `P.F` are
   constructible module sheaves, `thm-constructible-serre` implies their cokernel is
   constructible. Transport this property along the isomorphism to `F₂`.
6. Apply `lem-weil-pbc-constructible-torsion-modules-agree` to both outer terms to
   return to `def-weil-pbc-constructible-torsion`, using their torsion curve pairs. -/
theorem constructible_sub_quotient {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : P.IsConstructible) :
    (AlgebraicGeometry.CurveCoefficientPair.IsConstructible { P with F := F₁, isTorsion := h₁ }) ∧
      (AlgebraicGeometry.CurveCoefficientPair.IsConstructible
        { P with F := F₂, isTorsion := h₂ }) := by
  sorry

end AlgebraicGeometry.CurveCoefficientPair
