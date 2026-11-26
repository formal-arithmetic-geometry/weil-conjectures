/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps
import WeilConjectures.RingTheory.FormalGlueingComplexExact
import WeilConjectures.RingTheory.FormalGlueingCanonicalFunctor
import WeilConjectures.RingTheory.FormalGlueingMorphismLifting
import WeilConjectures.RingTheory.FormalGlueingEssentialSurjectivity

/-!
# The canonical functor for formal glueing

For a ring map `R → S` and `f₁, …, fₜ ∈ R`, the canonical functor from `R`-modules to formal
glueing data is constructed; if `R → S` is flat and induces an isomorphism modulo
`I = (f₁, …, fₜ)`, it is fully faithful and essentially surjective.

## Implementation details

Faithfulness follows from injectivity of the first map in the exact formal glueing complex, and
fullness is proved separately. For essential surjectivity, a glueing datum is compared with the
canonical datum of its module `H⁰` of compatible families; the kernel and cokernel of the
comparison on the prime module are `I`-power torsion, and flat base change and descent of
torsion modules and extensions produce a module whose canonical datum is isomorphic to the given
one.

## References

* [Stacks, Tag 05EL]
* [Stacks, Tag 05ER]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- The canonical comparison and interchange maps are isomorphisms, and the prescribed
objects and maps form a functor. Under flatness and the quotient isomorphism this functor
is fully faithful and essentially surjective. The heterogeneous equalities say that the
structural maps are the actual canonical maps, not merely isomorphic choices of them. -/
theorem exists_canonical_equivalence {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R) :
    (∀ (P : ModuleCat.{max u v w} R) (a b : R),
      Function.Bijective (compare φ a P) ∧ Function.Bijective (swap a b P)) ∧
    ∃ Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f,
      (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)) ∧
      (φ.Flat →
        Function.Bijective
          (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map) →
        (∀ M N : ModuleCat.{max u v w} R,
          Function.Bijective (Can.map : (M ⟶ N) → (Can.obj M ⟶ Can.obj N))) ∧
        (∀ X : Data.{u, v, max u v w} φ f,
          ∃ M : ModuleCat.{max u v w} R, Nonempty (Can.obj M ≅ X))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro P a b
    refine ⟨(compare_properties φ P a).2.2.2.2, ?_⟩
    have hs := (swap_properties P a b).2.2.2.2
    constructor
    · intro x y h
      have hx := congrArg (fun k => k x) hs.1
      have hy := congrArg (fun k => k y) hs.1
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        hx.symm.trans ((congrArg (swap b a P) h).trans hy)
    · intro y
      refine ⟨swap b a P y, ?_⟩
      exact congrArg (fun k => k y) hs.2
  · obtain ⟨Can, hobj, hmap⟩ := exists_canonical_functor φ t f
    refine ⟨Can, hobj, hmap, ?_⟩
    intro hflat hquot
    refine ⟨?_, canonical_essentially_surjective φ t f Can hobj hflat hquot⟩
    intro M N
    refine ⟨?_, canonical_map_surjective φ t f Can hobj hmap hflat hquot M N⟩
    intro a b hab
    have hprime : extendMap φ a.hom = extendMap φ b.hom :=
      eq_of_heq ((hmap M N a).1.symm.trans
        ((heq_of_eq (congrArg (fun z => z.prime) hab)).trans (hmap M N b).1))
    have hchart (i : Fin t) : localMap (f i) a.hom = localMap (f i) b.hom :=
      eq_of_heq (((hmap M N a).2 i).symm.trans
        ((heq_of_eq (congrArg (fun z => z.chart i) hab)).trans ((hmap M N b).2 i)))
    let : Algebra R S := φ.toAlgebra
    have hinj := (RingTheory.formalGlueingComplexExact φ hflat t f hquot N).1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply hinj
    apply Prod.ext
    · have hp := congrArg (fun k => k (TensorProduct.tmul R (1 : S) m)) hprime
      simpa [extendMap, LinearMap.baseChange_tmul] using hp
    · funext i
      have hc := congrArg (fun k => k (LocalizedModule.mk m 1)) (hchart i)
      simpa [localMap, IsLocalizedModule.map_LocalizedModules] using hc

end FormalGlueing
