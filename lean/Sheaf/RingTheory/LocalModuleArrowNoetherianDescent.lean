/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import Sheaf.Paper.LimitTowerEssentiallyFinitePresentation
import Sheaf.Algebra.FinitePresentationColimit
import Sheaf.RingTheory.TensorLocalizationTowerTransition
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-!
# Simultaneous Noetherian local approximation of a module arrow

Source: Stacks Project, Algebra, Tag 046Y (first proof paragraph), with Tags 00QX,
00QV, 00R7 and 01ZR (blueprint: lem-trf-local-module-arrow-noetherian-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option autoImplicit false

namespace RingHom

/--
Simultaneous Noetherian local approximation of a morphism of finitely presented modules.

Source: Stacks Project, Algebra, Tag 046Y (lemma-mod-injective-general), first proof
paragraph, using Tags 00QX, 00QV, 00R7, 00FN and Limits Tag 01ZR
(blueprint: lem-trf-local-module-arrow-noetherian-descent).

Proof:
1. Apply `lem-weil-pbc-limit-tower-essentially-finite-presentation` to `R → S → S`
   and `M`, using the identity as the second map. Write its stages `Rᵢ → Aᵢ → Sᵢ`.
   `lem-weil-pbc-essentially-finite-type-composition` makes `Sᵢ` essentially of finite
   type over `Rᵢ`. Starting with the Noetherian ring of integers, apply
   `lem-weil-pbc-finite-type-algebra-noetherian` and `lem-weil-pbc-localization-noetherian`
   to obtain Noetherianity of all stages. The chosen finite-type algebras are finitely
   presented by `lem-weil-pbc-finite-type-noetherian-finite-presentation`.
2. Apply `lem-weil-pbc-tensor-localization-tower-transition` to the two adjacent tower
   comparisons. This gives the displayed `Sᵢ ⊗ Rⱼ → Sⱼ` localization, and its application
   at the limit gives `Sᵢ ⊗ R → S`, with exactly the displayed pure-tensor formulas.
3. Apply the object clause of `lem-pc-fp-module-map-descent-affine` to descend `N` over
   the ring colimit. Move to a common stage with the model of `M`, tensor both finite
   cokernel presentations there, and apply the morphism clause to descend `u`. Thus
   at a stage `c` there are finitely presented modules `P,Q` and a map `v : P → Q`
   whose scalar extensions identify with `M,N,u`.
4. Restrict to the nonempty directed tail above `c`. Its inclusion is final, so
   `lem-weil-pbc-colimit-initial-full-subcategory` preserves both ring colimits. Set
   `Mⱼ = P ⊗ Sⱼ`, `Nⱼ = Q ⊗ Sⱼ`, and `uⱼ = v ⊗ 1`. The transitions send `x ⊗ a` to
   `x ⊗ sⱼₖ(a)` and the cocones send it to `a` times the fixed limit image of `x`.
   The tensor universal property (`def-weil-pbc-module-tensor-product`) gives these
   additive maps. Their formulas verify semilinearity, identity, composition,
   cocone compatibility, and both arrow squares.
5. Associativity identifies `(P ⊗ Sᵢ) ⊗ Sⱼ` with `P ⊗ Sⱼ` by the displayed canonical
   map, with inverse `x ⊗ b ↦ (x ⊗ 1) ⊗ b`; balancing proves both composites are
   identities. The same formulas apply to `Q` and at the limit. Applying them to
   `v(x)` proves compatibility with the arrow. Tensoring the finite cokernel
   presentations of `P,Q` gives finite presentation at every stage. We place the
   scalar ring first in the Lean tensor products, using `TensorProduct.comm`.
6. For compatible additive maps out of `P ⊗ Sⱼ`, define a map out of `P ⊗ S` by
   choosing a stage representative for each scalar. Eventual equality makes this
   well-defined; common upper bounds prove additivity and balancing. The tensor
   universal property gives existence and uniqueness, so these are the required
   additive-group colimits (`def-weil-pbc-category-colimit`). The usual quotient of
   stage elements by common-stage equality constructs directed ring and group
   colimits; hence all four colimits have the stated representation and equality
   criteria. Empty finite presentations and zero `v` include zero modules/maps.
   Universes may be enlarged in the construction. To retain an independently small
   module universe, replace each stage module by its small copy: each stage ring is
   countable (essential finite type over the integers), and each finite stage module
   is countable. Transport structures and maps along these equivalences.
-/
theorem exists_local_module_arrow_noetherian_descent
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [IsLocalRing R] [IsLocalRing S]
    (α : R →+* S) [IsLocalHom α]
    [Algebra R B] [Algebra.FinitePresentation R B]
    (W : Submonoid B) (f : B →+* S)
    (hf : f.comp (algebraMap R B) = α)
    (hS : letI := f.toAlgebra; IsLocalization W S)
    {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    (u : M →ₗ[S] N) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (Rdiag Sdiag : I ⥤ CommRingCat.{u})
      (ρ : Rdiag ⟶ Sdiag)
      (π : Rdiag ⟶ (Functor.const I).obj (CommRingCat.of R))
      (κ : Sdiag ⟶ (Functor.const I).obj (CommRingCat.of S))
      (Mdiag Ndiag : I ⥤ AddCommGrpCat.{v})
      (μ : Mdiag ⟶ (Functor.const I).obj (AddCommGrpCat.of M))
      (ν : Ndiag ⟶ (Functor.const I).obj (AddCommGrpCat.of N))
      (hModM : ∀ i : I, Module (Sdiag.obj i) (Mdiag.obj i))
      (hModN : ∀ i : I, Module (Sdiag.obj i) (Ndiag.obj i))
      (ui : ∀ i : I, Mdiag.obj i →ₗ[Sdiag.obj i] Ndiag.obj i),
      -- local rings, local homomorphisms, and commuting ring squares
      (∀ i, IsLocalRing (Rdiag.obj i)) ∧
      (∀ i, IsLocalRing (Sdiag.obj i)) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧
      (∀ (i j : I) (h : i ≤ j), IsLocalHom (Rdiag.map (homOfLE h)).hom) ∧
      (∀ (i j : I) (h : i ≤ j), IsLocalHom (Sdiag.map (homOfLE h)).hom) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i))) ∧
      (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
      -- semilinear transition and cocone maps, including their arrow squares
      (∀ (i j : I) (h : i ≤ j) (s : Sdiag.obj i) (x : Mdiag.obj i),
        (Mdiag.map (homOfLE h)).hom (s • x) =
          (Sdiag.map (homOfLE h)).hom s • (Mdiag.map (homOfLE h)).hom x) ∧
      (∀ (i j : I) (h : i ≤ j) (s : Sdiag.obj i) (x : Ndiag.obj i),
        (Ndiag.map (homOfLE h)).hom (s • x) =
          (Sdiag.map (homOfLE h)).hom s • (Ndiag.map (homOfLE h)).hom x) ∧
      (∀ i (s : Sdiag.obj i) (x : Mdiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) (s • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x) ∧
      (∀ i (s : Sdiag.obj i) (x : Ndiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) (s • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) x) ∧
      (∀ (i j : I) (h : i ≤ j) (x : Mdiag.obj i),
        (Ndiag.map (homOfLE h)).hom (ui i x) =
          ui j ((Mdiag.map (homOfLE h)).hom x)) ∧
      (∀ i (x : Mdiag.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) (ui i x) =
          u ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x)) ∧
      -- (1) Noetherianity and essential finite type
      (∀ i, IsNoetherianRing (Rdiag.obj i)) ∧
      (∀ i, IsNoetherianRing (Sdiag.obj i)) ∧
      (∀ i, (algebraMap ℤ (Rdiag.obj i)).EssFiniteType) ∧
      (∀ i, (ρ.app i).hom.EssFiniteType) ∧
      (∀ i, Module.FinitePresentation (Sdiag.obj i) (Mdiag.obj i)) ∧
      (∀ i, Module.FinitePresentation (Sdiag.obj i) (Ndiag.obj i)) ∧
      -- (2) ring and additive-group filtered colimits
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) μ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of N) ν)) ∧
      (∀ x : R, ∃ i r, (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)) r = x) ∧
      (∀ x : S, ∃ i s, (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s = x) ∧
      (∀ i j (x : Rdiag.obj i) (y : Rdiag.obj j),
        (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)) x =
            (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Rdiag.map (homOfLE hik)).hom x = (Rdiag.map (homOfLE hjk)).hom y) ∧
      (∀ i j (x : Sdiag.obj i) (y : Sdiag.obj j),
        (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x =
            (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Sdiag.map (homOfLE hik)).hom x = (Sdiag.map (homOfLE hjk)).hom y) ∧
      (∀ x : M, ∃ i m, (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) m = x) ∧
      (∀ x : N, ∃ i n, (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) n = x) ∧
      (∀ i j (x : Mdiag.obj i) (y : Mdiag.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x =
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Mdiag.map (homOfLE hik)).hom x = (Mdiag.map (homOfLE hjk)).hom y) ∧
      (∀ i j (x : Ndiag.obj i) (y : Ndiag.obj j),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) x =
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app j)) y ↔
          ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
            (Ndiag.map (homOfLE hik)).hom x = (Ndiag.map (homOfLE hjk)).hom y) ∧
      -- (3) transition localizations and module base changes
      (∀ (i j : I) (h : i ≤ j),
        letI := (ρ.app i).hom.toAlgebra
        letI := (Rdiag.map (homOfLE h)).hom.toAlgebra
        ∃ φ : Sdiag.obj i ⊗[Rdiag.obj i] Rdiag.obj j →+* Sdiag.obj j,
          (∀ (s : Sdiag.obj i) (r : Rdiag.obj j),
            φ (s ⊗ₜ[Rdiag.obj i] r) =
              (Sdiag.map (homOfLE h)).hom s * (ρ.app j).hom r) ∧
          (letI := φ.toAlgebra
           ∃ V : Submonoid (Sdiag.obj i ⊗[Rdiag.obj i] Rdiag.obj j),
             IsLocalization V (Sdiag.obj j))) ∧
      (∀ (i j : I) (h : i ≤ j),
        letI := (Sdiag.map (homOfLE h)).hom.toAlgebra
        ∃ (eM : Sdiag.obj j ⊗[Sdiag.obj i] Mdiag.obj i ≃ₗ[Sdiag.obj j] Mdiag.obj j)
          (eN : Sdiag.obj j ⊗[Sdiag.obj i] Ndiag.obj i ≃ₗ[Sdiag.obj j] Ndiag.obj j),
          (∀ (s : Sdiag.obj j) (x : Mdiag.obj i),
            eM (s ⊗ₜ[Sdiag.obj i] x) = s • (Mdiag.map (homOfLE h)).hom x) ∧
          (∀ (s : Sdiag.obj j) (y : Ndiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] y) = s • (Ndiag.map (homOfLE h)).hom y) ∧
          (∀ (s : Sdiag.obj j) (x : Mdiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] ui i x) = ui j (eM (s ⊗ₜ[Sdiag.obj i] x)))) ∧
      -- (4) localizations and module base changes at the limit
      (∀ i,
        letI := (ρ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ φ : Sdiag.obj i ⊗[Rdiag.obj i] R →+* S,
          (∀ (s : Sdiag.obj i) (r : R),
            φ (s ⊗ₜ[Rdiag.obj i] r) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) s * α r) ∧
          (letI := φ.toAlgebra
           ∃ V : Submonoid (Sdiag.obj i ⊗[Rdiag.obj i] R), IsLocalization V S)) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ (eM : S ⊗[Sdiag.obj i] Mdiag.obj i ≃ₗ[S] M)
          (eN : S ⊗[Sdiag.obj i] Ndiag.obj i ≃ₗ[S] N),
          (∀ (s : S) (x : Mdiag.obj i),
            eM (s ⊗ₜ[Sdiag.obj i] x) =
              s • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (μ.app i)) x) ∧
          (∀ (s : S) (y : Ndiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] y) =
              s • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of N) (ν.app i)) y) ∧
          (∀ (s : S) (x : Mdiag.obj i),
            eN (s ⊗ₜ[Sdiag.obj i] ui i x) = u (eM (s ⊗ₜ[Sdiag.obj i] x)))) := by
  sorry

end RingHom
