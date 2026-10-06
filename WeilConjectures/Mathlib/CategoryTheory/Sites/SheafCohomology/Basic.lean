/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# The map on sheaf cohomology induced by an exact functor

Sheaf cohomology `CategoryTheory.Sheaf.H F n` is the `Ext`-group in degree `n` from the
constant sheaf `ℤ` to `F`. An exact functor `G` between two categories of abelian sheaves
therefore induces a map on cohomology as soon as it is compatible with the constant sheaves:
push an `Ext`-class forward along `G` and precompose with the comparison of constant sheaves.

## Main definitions

- `CategoryTheory.Sheaf.IsTorsion`: a sheaf of abelian groups all of whose groups of sections
  are torsion groups.
- `CategoryTheory.Sheaf.H.mapFunctor`: the map `H F n →+ H (G.obj F) n` on sheaf cohomology
  induced by an exact functor `G` together with an isomorphism `e` between the constant
  sheaf `ℤ` on the target site and the image under `G` of the constant sheaf `ℤ` on the
  source site.

## Main statements

- `CategoryTheory.Sheaf.H.mapFunctor_map`: the induced map is natural in the sheaf.
- `CategoryTheory.Sheaf.H.mapFunctor_bijective`: it is bijective as soon as `G` is fully
  faithful and preserves injective objects, and the source category of sheaves has enough
  injective objects.
- `CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`: `H¹(F) = 0` as soon as, for every
  short exact sequence `0 → F → E → Q → 0`, every global section of `Q` lifts to `E`.
- `CategoryTheory.Sheaf.H.quotientRangeAddEquiv`: for a short exact sequence
  `0 → F → I → Q → 0` with `H¹(I) = 0`, the connecting homomorphism identifies `H¹(F)` with
  the cokernel of `Γ(I) → Γ(Q)`.
- `CategoryTheory.Sheaf.exists_shortExact_injective_addEquiv_H_one`: such a sequence exists
  with `I` injective.
-/

@[expose] public section

universe w' w v' v u' u

namespace CategoryTheory

open Abelian Limits AddCommGrpCat

/-- A sheaf of abelian groups is *torsion* if all its groups of sections are torsion groups. -/
def Sheaf.IsTorsion {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ U, IsAddTorsion (F.obj.obj U)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable [HasSheafify K AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
variable (G : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ≅
    G.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

namespace Sheaf

variable (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ)

/-- The map on sheaf cohomology induced by an exact functor `G` between two categories of
abelian sheaves, together with an isomorphism `e` between the constant sheaf `ℤ` on the
target site and the image under `G` of the constant sheaf `ℤ` on the source site: an
`Ext`-class is pushed forward along `G` and then precomposed with `e`. -/
noncomputable def H.mapFunctor : H F n →+ H (G.obj F) n :=
  (Ext.precompAddEquiv e _ n).toAddMonoidHom.comp (G.mapExtAddHom _ F n)

lemma H.mapFunctor_apply (x : H F n) :
    H.mapFunctor G e F n x = (Ext.mk₀ e.hom).comp (x.mapExactFunctor G) (zero_add n) :=
  rfl

section Naturality

variable {F}

/-- The map induced on sheaf cohomology by an exact functor is natural in the sheaf: the
square

```
   H F n ──────H.mapFunctor G e F n──────→ H (G.obj F) n
     │                                          │
     │ H.map φ n                                │ H.map (G.map φ) n
     ↓                                          ↓
   H F' n ─────H.mapFunctor G e F' n─────→ H (G.obj F') n
```

commutes. -/
lemma H.mapFunctor_map {F' : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ F') (x : H F n) :
    H.mapFunctor G e F' n (H.map φ n x) =
      H.map (G.map φ) n (H.mapFunctor G e F n x) := by
  simp only [H.mapFunctor_apply, H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

end Naturality

/-- If moreover `G` is fully faithful and preserves injective objects, and the source
category of sheaves has enough injective objects, then the induced map on sheaf cohomology
is bijective. -/
theorem H.mapFunctor_bijective [G.Full] [G.Faithful]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] [G.PreservesInjectiveObjects] :
    Function.Bijective (H.mapFunctor G e F n) :=
  (Ext.precompAddEquiv e _ n).bijective.comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects G _ F n)

end Sheaf

section VanishingH1

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- **`H¹` vanishes when global sections lift.** Let `T` be a terminal object, so that global
sections are sections over `T`. If for every short exact sequence `0 → F → E → Q → 0` of
abelian sheaves every global section of `Q` lifts to a global section of `E`, then
`H¹(F) = 0`.

In torsor language: the fibre of `E → Q` over a global section of `Q` is an `F`-torsor, which
is trivial exactly when the section lifts; every class in `H¹(F) = Ext¹(ℤ, F)` arises this way
from an embedding of `F` into an injective sheaf. This is the half of the classification of
`H¹` by torsors that is needed for vanishing results.
(blueprint: `lem-sc-torsor-h1`, vanishing direction) -/
theorem Sheaf.subsingleton_H_one_of_surjective (F : Sheaf J AddCommGrpCat.{w}) {T : C}
    (hT : IsTerminal T)
    (h : ∀ ⦃E Q : Sheaf J AddCommGrpCat.{w}⦄ (ι : F ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact → Function.Surjective (π.hom.app (op T))) :
    Subsingleton (H F 1) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨t, ht⟩ := h S.f S.g S.zero hS (H.equiv₀ S.X₃ hT y)
  have hy : ((H.equiv₀ S.X₂ hT).symm t).comp (Ext.mk₀ S.g) (add_zero 0) = y := by
    rw [← H.map_apply, H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [← hy, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (zero_add 1), hS.comp_extClass,
    Ext.comp_zero]

end VanishingH1

section HOneCokernel

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) {T : C} (hT : IsTerminal T)

/-- The connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` of a short exact sequence of abelian
sheaves, where global sections are sections over a terminal object `T`. -/
noncomputable def Sheaf.H.δ : S.X₃.obj.obj (op T) →+ H S.X₁ 1 :=
  (hS.extClass.postcomp _ (zero_add 1)).comp (H.equiv₀ S.X₃ hT).symm.toAddMonoidHom

lemma Sheaf.H.δ_apply (s : S.X₃.obj.obj (op T)) :
    H.δ hS hT s = ((H.equiv₀ S.X₃ hT).symm s).comp hS.extClass (zero_add 1) :=
  rfl

/-- The kernel of the connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` consists of the global
sections of `S.X₃` which lift to `S.X₂`. -/
lemma Sheaf.H.ker_δ : (H.δ hS hT).ker = (S.g.hom.app (op T)).hom.range := by
  ext s
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, H.δ_apply]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _ hS _ (zero_add 1) h
    refine ⟨H.equiv₀ S.X₂ hT x, (H.equiv₀ S.X₃ hT).symm.injective ?_⟩
    rw [← H.equiv₀_symm_naturality, AddEquiv.symm_apply_apply, H.map_apply, hx]
  · rintro ⟨x, rfl⟩
    rw [← H.equiv₀_symm_naturality, H.map_apply, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1)
      (zero_add 1), hS.comp_extClass, Ext.comp_zero]

/-- The connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` is surjective when `H¹(S.X₂) = 0`. -/
lemma Sheaf.H.surjective_δ [Subsingleton (H S.X₂ 1)] : Function.Surjective (H.δ hS hT) := by
  intro x
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) (zero_add 1)
  exact ⟨H.equiv₀ S.X₃ hT y, by rw [H.δ_apply, AddEquiv.symm_apply_apply]⟩

/-- For a short exact sequence `0 → F → I → Q → 0` of abelian sheaves with `H¹(I) = 0`, the
connecting homomorphism identifies `H¹(F)` with the cokernel of `Γ(I) → Γ(Q)`. -/
noncomputable def Sheaf.H.quotientRangeAddEquiv [Subsingleton (H S.X₂ 1)] :
    S.X₃.obj.obj (op T) ⧸ (S.g.hom.app (op T)).hom.range ≃+ H S.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (H.ker_δ hS hT)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (H.surjective_δ hS hT))

/-- **`H¹` as a cokernel of global sections.** Every abelian sheaf `F` on a site with a
terminal object `T` sits in a short exact sequence `0 → F → I → Q → 0` with `I` injective,
hence with `H^q(I) = 0` for `q ≥ 1`, and the connecting homomorphism then identifies `H¹(F)`
with the cokernel of `d_T : Γ(I) → Γ(Q)`.

The blueprint takes for `I` the Godement sheaf of `F`, which is flasque; here `I` is an
injective sheaf, which has the same two properties used later: it is acyclic, and every
equivariant map from a torsor into it exists (see
`CategoryTheory.Sheaf.Torsor.exists_quotientEquiv_H_one`).
(blueprint: `lem-galois-flasque`) -/
theorem Sheaf.exists_shortExact_injective_addEquiv_H_one (hT : IsTerminal T)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] (F : Sheaf J AddCommGrpCat.{w}) :
    ∃ (I Q : Sheaf J AddCommGrpCat.{w}) (ι : F ⟶ I) (d : I ⟶ Q) (w : ι ≫ d = 0),
      (ShortComplex.mk ι d w).ShortExact ∧ Injective I ∧ (∀ q, Subsingleton (H I (q + 1))) ∧
      Nonempty (H F 1 ≃+ Q.obj.obj (op T) ⧸ (d.hom.app (op T)).hom.range) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  exact ⟨S.X₂, S.X₃, S.f, S.g, S.zero, hS, inferInstance, fun _ ↦ inferInstance,
    ⟨(H.quotientRangeAddEquiv hS hT).symm⟩⟩

end HOneCokernel

end CategoryTheory
