/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.KrullTopology

/-!
# Sections over finite separable fields and geometric stalk invariants

Source: Stacks Project, Etale Cohomology, Tags 04JM and 03QW
(blueprint: lem-exc-field-sections-stalk-invariants).
-/

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- (blueprint: lem-exc-field-sections-stalk-invariants) Stacks Project, Tags 04JM and 03QW.
The action on the geometric stalk is characterized by changing lifts through automorphisms
of the algebraic closure. At every finite separable intermediate field, the canonical germ
map identifies sections with the elements fixed by its Galois subgroup. These maps commute
with sheaf morphisms and field embeddings, independently of the extending automorphism.

Proof (Stacks 04JM, direct proof; 03QW for the action and naturality):
1. Restrict the sheaf to the small etale site of each intermediate field by etale
composition (`lem-weil-pbc-etale-covering-composition`). For a finite Galois extension
`E/L`, apply `lem-exc-finite-galois-sections-descent` to identify sections over `L` with
invariant sections over `E`.
2. Use the stalk colimit (`def-weil-pbc-geometric-stalks`), shrink a pointed neighbourhood
to its connected component, and apply `lem-weil-pbc-etale-fibre-discrete-separable-points`
to represent a germ over a finite separable field. Enlarge it to a finite Galois extension
of `L` using `lem-weil-pbc-finite-galois-receiving-separable-extensions`. The germ map
there is injective: use `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered` and observe
that every pointed neighbourhood mapping to this one-point spectrum is nonempty and
etale, hence surjective. Its restriction map is injective by the sheaf equalizer condition
(`def-weil-pbc-etale-sheaf-of-sets`). Lift each automorphism of `E/L` to the subgroup
fixing `L`; invariance of the germ and this injectivity give invariance of its representative.
Finite Galois descent now gives a unique section over `L`. Conversely, germs of sections
over `L` are fixed by its fixing subgroup.
3. Naturality in representing objects (`lem-galois-yoneda-hom-bijection`) and the
lift-change action (`def-weil-pbc-geometric-stalks`, Stacks 03QW) identify pullback along
an embedding with the extending automorphism acting on the germ. Since `g(L)` lies in
`L'`, conjugating the subgroup fixing `L'` by `g` inverse gives a subgroup fixing `L`.
Thus `g` carries invariants into invariants; the action law gives composition compatibility.
4. Two extensions `g`, `g'` differ by an element of the subgroup fixing `L`, so agree on
its invariants. Naturality in sheaf morphisms follows from the Yoneda naturality
(`lem-galois-yoneda-hom-bijection`) and stalk functoriality
(`def-weil-pbc-geometric-stalks`). -/
theorem fieldSections_stalkInvariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ (lift : ∀ (L : IntermediateField K Ks)
        [FiniteDimensional K L] [Algebra.IsSeparable K L],
          (pointSmallEtale s).fiber.obj (etaleSpec K L))
      (action : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)),
        MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F)),
      (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
        [Algebra.IsSeparable K L],
        (lift L).left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype))) ∧
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : (Spec (.of K)).Etale)
          (x x' : (pointSmallEtale s).fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
          (action F).smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
            (pointSmallEtale s).toPresheafFiber X x' F.obj z) ∧
        (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
          [Algebra.IsSeparable K L],
          Set.BijOn
            ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj)
            Set.univ
            {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m}) ∧
        (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L]
          [FiniteDimensional K L'] [Algebra.IsSeparable K L]
          [Algebra.IsSeparable K L']
          (j : L →ₐ[K] L') (g : Gal(Ks/K))
          (hg : g.toAlgHom.comp L.val = L'.val.comp j)
          (z : F.obj.obj (op (etaleSpec K L))),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K L') (lift L') F.obj
              (F.obj.map (etaleSpecMap j).op z) =
            (action F).smul g
              ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧
        (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L]
          [FiniteDimensional K L'] [Algebra.IsSeparable K L]
          [Algebra.IsSeparable K L']
          (j : L →ₐ[K] L') (g g' : Gal(Ks/K))
          (hg : g.toAlgHom.comp L.val = L'.val.comp j)
          (hg' : g'.toAlgHom.comp L.val = L'.val.comp j)
          (m : (pointSmallEtale s).sheafFiber.obj F)
          (hm : ∀ h ∈ L.fixingSubgroup, (action F).smul h m = m),
          (∀ h ∈ L'.fixingSubgroup,
            (action F).smul h ((action F).smul g m) = (action F).smul g m) ∧
          (action F).smul g m = (action F).smul g' m)) ∧
      (∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
        (φ : F ⟶ F'),
        (∀ (L : IntermediateField K Ks) [FiniteDimensional K L]
          [Algebra.IsSeparable K L] (z : F.obj.obj (op (etaleSpec K L))),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F'.obj
              (φ.hom.app _ z) =
            (pointSmallEtale s).sheafFiber.map φ
              ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧
        (∀ (g : Gal(Ks/K)) (m : (pointSmallEtale s).sheafFiber.obj F),
          (pointSmallEtale s).sheafFiber.map φ ((action F).smul g m) =
            (action F').smul g ((pointSmallEtale s).sheafFiber.map φ m))) := by
  sorry

end AlgebraicGeometry.Scheme
