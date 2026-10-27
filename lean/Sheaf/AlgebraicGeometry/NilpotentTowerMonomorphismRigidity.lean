/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.GroupTheory.MonoidLocalization.Away
import Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-! # Monomorphism rigidity for a nilpotent ring tower

Source: Stacks Project, More on Flatness, Tag 0CTJ (lemma-monomorphism-isomorphism)
(blueprint: lem-sfb-nilpotent-tower-monomorphism-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finite type monomorphism to the spectrum of the inverse limit of a
surjective ring tower with elementwise nilpotent transition kernels is an isomorphism
if every stage spectrum factors through it. The object `D.obj (op n)` represents
`A_{n+1}` in the source's indexing, and `limit.π` supplies the canonical projections.

Source: Stacks Project, More on Flatness, Tag 0CTJ (lemma-monomorphism-isomorphism)
(blueprint: lem-sfb-nilpotent-tower-monomorphism-rigidity).

Proof, following the nine steps of the DAG node:
1. Put S = Spec A, S_n = Spec A_n. Factorizations a_n through h are unique by monicity,
   hence compatible with the transition maps S_n to S_{n+1}
   (def-weil-affine-spectrum).
2. Every projection A to A_n is surjective by successive lifting. If u maps to 1 in
   A_1, inductively lift an inverse across each transition: an error e in its kernel
   is nilpotent, so the finite geometric series in -e corrects the inverse. The
   inverses are compatible by uniqueness, giving an inverse of u in A. No uniform
   exponent is needed, either across elements or across stages.
3. An open U in S containing S_1 is S: cover U by basic opens D(f). Their images cover
   S_1, so a finite unit-ideal equation in A_1 lifts to c in A with first coordinate
   1. Step 2 makes c a unit; thus S = D(c) lies in U
   (lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact and
   lem-weil-pbc-spec-localization-away-basic-open).
4. Surjective nil-kernel transitions give homeomorphisms of spectra
   (lem-pur-all-element-powers-spectrum-homeomorphism, exponent 1). The compatible
   a_n have a common quasi-compact image. Choose a finite affine neighbourhood T'
   of this image and restrict all a_n to T'
   (lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-affine-opens-basis,
   def-weil-open-immersion).
5. The restriction q : T' to S is monic and locally finite type. For the latter,
   use basic opens in each finite type affine chart: localizing at b adds b inverse
   to its finite generating set (lem-weil-pbc-spec-localization-away-basic-open,
   lem-weil-pbc-principal-localization-open-immersion, def-weil-ring-localization-away,
   def-weil-finite-type-morphism). Apply
   lem-trf-monomorphism-finite-type-composite-lqf with g the identity to obtain
   separatedness and local quasi-finiteness. The affine S is qcqs and T' is
   quasi-compact, so q is quasi-compact (lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-qcqs-morphism-permanence).
6. By thm-pqf-zmt-factorization, q factors through a quasi-compact open immersion
   j : T' to W followed by a finite map p : W to S. The finite map is affine, hence
   W = Spec B (def-weil-finite-integral-morphism, pqf-def-affine-morphism).
   The composites j a_n give compatible ring maps beta_n : B to A_n whose composites
   with alpha : A to B are the projections (def-weil-affine-spectrum).
7. Define beta : B to A coordinatewise from beta_n. It is a ring map and beta alpha
   is the identity by its coordinates. Thus g : S to W satisfies g p = identity
   and i_n g = a_n j, with composition written here in diagrammatic order
   (def-weil-affine-spectrum).
8. Pull back j along g. The projection v : P to S is an open immersion
   (def-pc-fibre-product, lem-weil-pbc-open-immersion-base-change). It contains S_1
   by the pullback universal property, hence its image is S by step 3. It is an
   isomorphism (def-weil-open-immersion). Its inverse gives a section s' of q.
9. Compose s' with T' to T to obtain a section s of the original h. Cancel h in
   (h s) h = h to obtain h s = identity, in diagrammatic order. Thus h has a
   two-sided inverse, without any quasi-compactness assumption on T. -/
theorem isIso_of_nilpotentTower
    (D : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hsurj : ∀ n : ℕ,
      Function.Surjective (D.map (homOfLE (Nat.le_succ n)).op).hom)
    (hnil : ∀ (n : ℕ) (x : D.obj (op (n + 1))),
      (D.map (homOfLE (Nat.le_succ n)).op).hom x = 0 → IsNilpotent x)
    {T : Scheme.{u}} (h : T ⟶ Spec (limit D)) [Mono h] [LocallyOfFiniteType h]
    (hfactor : ∀ n : ℕ, ∃ a : Spec (D.obj (op n)) ⟶ T,
      a ≫ h = Spec.map (limit.π D (op n))) :
    IsIso h := by
  sorry

end AlgebraicGeometry
