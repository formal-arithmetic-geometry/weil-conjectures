/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects

/-! # Reconstructing formal-system maps from maps of limit sheaves

Source: Stacks Project, Lemma 087W, and the uniqueness/gluing step of Lemma 088B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every module-sheaf map between the limits of coherent adic systems descends
uniquely at each level to a compatible map of systems; here only existence is asserted.
Source: Stacks Project, Lemma 087W, its formula M/I^n M = M_n, and Lemma 088B,
the construction of alpha through that equivalence and local uniqueness.
(blueprint: lem-weil-pbc-coherent-formal-module-limit-full)

Proof: On an affine open U = Spec A put I = J(U). Evaluation preserves limits,
so β gives an A-linear map b:N -> P between the module limits of G and H on U.
Lemma 087W identifies the nth projections with surjections whose kernels are
I^(n+1)N and I^(n+1)P. A-linearity carries the first kernel into the second:
apply b to finite sums of ideal multiples. Thus b induces a unique map
N/I^(n+1)N -> P/I^(n+1)P for every n. The affine tilde/sections equivalence
translates these maps into sheaf maps G_n|U -> H_n|U. Their transition equations
follow by precomposing with the surjective projections of N, using the defining
projection equations of b. Restriction to a smaller affine open preserves these
equations because β is a sheaf map. Surjectivity of its source projections gives
uniqueness on that smaller affine. Hence the local component maps agree after
restriction; cover overlaps by affine opens, without assuming intersections affine.
Glue each component using the sheaf axiom. Naturality is local and so holds globally.
The equations with the limit projections hold on the affine basis; the universal
property of the limit then gives lim.map α.hom = β. For J=0 this is the constant
system reconstruction; for J=1 the limits and all terms are zero. Zero sheaves
and empty affine opens also satisfy the argument. No proper morphism, comparison
κ, or map into a pushforward system is involved in this reconstruction theorem.
-/
theorem coherentFormalModule_limit_full {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G H : CoherentFormalModule Y J)
    (β : limit G.obj ⟶ limit H.obj) :
    ∃ α : G ⟶ H, lim.map α.hom = β := by sorry

end AlgebraicGeometry
