/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.GroupTheory.Finiteness

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinement
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.AlgebraicGeometry.FlatClosedFamilyIdealBaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Lifting diagonalizable homomorphisms from the special fibre

Source: Conrad, Reductive group schemes, Theorem B.3.2(2), printed pp.288--290
(blueprint: lem-sfb-complete-local-diagonalizable-fibre-hom-lift).

Special fibres and restriction of homomorphisms use the group-object pullback along
A → A/m. The special fibre of D_A(M) is used in its chosen pullback presentation;
its affine coordinate algebra is k ⊗_A A[M] = k[M], with the same Hopf operations.
The multiplicative-type hypothesis is written as an affine fppf diagonalizing cover.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restriction to the special fibre is bijective on homomorphisms out of D_A(M).
Every homomorphism whose special fibre is an isomorphism is an open and closed immersion.
Affineness, finite type and flatness of G say exactly that G = Spec B for a finitely
generated flat A-algebra B. No smoothness or commutativity of G, or torsion-freeness
of M, is required.

Source: Conrad, Reductive group schemes, Theorem B.3.2(2), printed pp.288--290
(blueprint: lem-sfb-complete-local-diagonalizable-fibre-hom-lift).

Proof, following the accepted seven-step DAG split:
1. Put H = D_A(M), A_n = A/m^n and S_n = Spec A_n for n ≥ 1. The affine
   fibre-product formula identifies H over A_n with D_(A_n)(M), including all Hopf
   operations. Finite generation of M makes A[M] finite type. The finite-type
   Noetherian finite-presentation lemma gives finite presentation of H and G.
   Flat module base change preserves flatness of G_n. Apply
   lem-sfb-nilpotent-flat-multiplicative-deformation to m/m^n to make G_n
   multiplicative type.
2. On an affine refinement of an fppf diagonalizing cover of G_n, apply
   lem-sfb-relative-diagonalizable-character-duality. The nilpotent closed immersion
   S_1 → S_n preserves the underlying space, hence the locally constant character
   maps. Thus each special-fibre homomorphism lifts uniquely locally. On affine
   refinements of overlaps the lifts agree by the same duality. Scheme morphism
   gluing and representable fpqc descent glue them uniquely; the fppf base-change
   and fppf-is-fpqc lemmas supply the covering of H_n. The group equations and
   the prescribed reduction descend by uniqueness. This gives finite-level bijectivity.
3. These unique finite-level lifts are compatible. Apply
   lem-sfb-adic-diagonalizable-hom-effectivity to obtain a unique global lift.
   Two global lifts have equal reductions at every level and are equal by its
   injectivity. This proves the first conjunct.
4. If j_k is an isomorphism, its kernel K is a closed subgroup of H with trivial
   special fibre. Embed H into a split torus using generators of M, and apply
   lem-sfb-local-torus-subgroup-special-trivial to K. Thus K is trivial and j
   is a monomorphism on every test scheme. No flatness of K is assumed.
5. Apply lem-sfb-affine-multiplicative-type-monomorphism-closed to j. Write the
   closed immersion as Spec(B/L) → Spec B. The group algebra A[M] is free over A,
   so H and G are flat. Lem-sfb-flat-closed-family-ideal-base-change identifies
   L/mL with the kernel of the special-fibre coordinate map, which is zero.
   Hence L = mL. Finite-type Noetherianity makes L a finite B-module.
6. The annihilator form of Nakayama supplies f in 1+mB with fL = 0. The basic
   open D(f) factors through H since L_f = 0. Its augmentation lies in 1+m,
   hence is a unit, so D(f) contains the entire identity section.
7. Apply lem-sfb-flat-subgroup-identity-neighbourhood-open to j and D(f).
   H is flat and locally finitely presented over A by step 1, so j is an open
   immersion as well as the closed immersion from step 5. -/
theorem completeLocal_diagonalizable_fibre_hom_lift
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (G : Grp (Over (Spec (.of A))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [Flat G.X.hom]
    (hG : ∃ (I : Type u) (R : I → CommRingCat.{u})
        (f : ∀ i : I, Spec (R i) ⟶ Spec (.of (IsLocalRing.ResidueField A))),
      Presieve.ofArrows (fun i : I ↦ Spec (R i)) f ∈
          Scheme.fppfPrecoverage (Spec (.of (IsLocalRing.ResidueField A))) ∧
        ∀ i : I, ∃ (N : Type u) (_ : AddCommGroup N) (_ : AddGroup.FG N),
          Nonempty ((Over.pullback (f i)).mapGrp.obj
              ((Over.pullback (Spec.map
                (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.obj G) ≅
            ringDiagonalizableGroup (R i) N))
    (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    Function.Bijective
        ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.map
          (X := ringDiagonalizableGroup A M) (Y := G)) ∧
      ∀ j : ringDiagonalizableGroup A M ⟶ G,
        IsIso ((Over.pullback
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).mapGrp.map j) →
        IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left := by
  sorry

end AlgebraicGeometry
