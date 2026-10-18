/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import Sheaf.TraceFormula.ValuationClosedFibreNoetherian

/-!
# Finite modules admit a finitely presented approximation with stable closed fibre

Source: Stacks Project, More on Morphisms, Tag 0GSG (lemma-mod-injective-valuation-ring),
proof, second paragraph (blueprint: lem-trf-valuation-finite-module-fp-reduction).

## Main statements

* `valuationFiniteModuleFpReduction` records the filtered finitely presented approximation
  and eventual closed-fibre isomorphism for a finite module over a local essentially finite
  type algebra over a valuation ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

/-- A finite module over a local essentially finite type algebra over a valuation ring is a
filtered colimit of finitely presented modules with surjective transition maps, and its
closed fibre is eventually unchanged.

The proof follows Tag 0GSG: choose finite subsets of a relation module to form the
finitely presented quotient system; verify its colimit by the universal property; use
Noetherianity of the closed fibre and finite generation of the reduced relation module to
obtain a stage after which the reduced relation submodules agree.
(blueprint: lem-trf-valuation-finite-module-fp-reduction) -/
theorem valuationFiniteModuleFpReduction
    (K : Type u) [Field K]
    (A : ValuationSubring K) [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : RingHom.EssFiniteType f)
    (N : Type u) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ (I : Type u) (c : Category.{u + 1} I)
      (d : @IsFilteredOrEmpty I c) (hI : Nonempty I)
      (F : @Functor I c (ModuleCat.{u} B) inferInstance)
      (t : @Cocone I c (ModuleCat.{u} B) inferInstance F)
      (ht : @IsColimit I c (ModuleCat.{u} B) inferInstance F t)
      (e : t.pt ≅ ModuleCat.of B N),
      (∀ (i : I), Module.FinitePresentation B (F.obj i)) ∧
      (∀ {i j : I} (g : i ⟶ j),
        Function.Surjective (F.map g).hom) ∧
      (∃ (i₀ : I), ∀ (i : I) (g : i₀ ⟶ i),
        ∃ (h :
            Submodule.span B
                (Set.range (fun p :
                  (Ideal.map f (IsLocalRing.maximalIdeal A)) × (F.obj i) =>
                  (p.1 : B) • p.2)) ≤
              (Submodule.span B
                (Set.range (fun p :
                  (Ideal.map f (IsLocalRing.maximalIdeal A)) × N =>
                  (p.1 : B) • p.2))).comap
                ((e.hom.hom).comp (t.ι.app i).hom))
          (q :
            (F.obj i ⧸ Submodule.span B
                (Set.range (fun p :
                  (Ideal.map f (IsLocalRing.maximalIdeal A)) × (F.obj i) =>
                  (p.1 : B) • p.2))) ≃ₗ[B]
              (N ⧸ Submodule.span B
                (Set.range (fun p :
                  (Ideal.map f (IsLocalRing.maximalIdeal A)) × N =>
                  (p.1 : B) • p.2)))) ,
            q.toLinearMap =
              (Submodule.span B
                (Set.range (fun p :
                  (Ideal.map f (IsLocalRing.maximalIdeal A)) × (F.obj i) =>
                  (p.1 : B) • p.2))).mapQ
                (Submodule.span B
                  (Set.range (fun p :
                    (Ideal.map f (IsLocalRing.maximalIdeal A)) × N =>
                    (p.1 : B) • p.2)))
                ((e.hom.hom).comp (t.ι.app i).hom) h) := by
  sorry

end WeilConjectures
