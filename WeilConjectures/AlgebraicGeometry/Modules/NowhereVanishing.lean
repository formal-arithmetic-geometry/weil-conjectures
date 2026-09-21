/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle

/-!
# A line bundle with a nowhere vanishing section, and the Liouville dichotomy

Let `X` be a scheme and `L` an invertible sheaf of `𝒪ₓ`-modules carrying a global section `s`
which vanishes at no point of `X`, in the sense of
`AlgebraicGeometry.Scheme.Modules.VanishesAt`. Multiplication by `s` is then an isomorphism
`𝒪ₓ ≅ L`, so `L` is trivial and every global section of `L` is `g • s` for a unique global
function `g`, vanishing exactly where `g` does.

When moreover `Γ(X, 𝒪ₓ)` is a field — for instance when `X` is an integral scheme, universally
closed over a field, by `AlgebraicGeometry.isField_of_universallyClosed` — a non-zero `g` is a
unit, hence vanishes nowhere. This is the **Liouville dichotomy**: on such an `X`, once *one*
global section of `L` vanishes nowhere, every other global section either vanishes identically
or vanishes nowhere.

The proof of the trivialisation is local: an invertible sheaf has, around every point, a
trivialising section `m` over an open `W`
(`SheafOfModules.Invertible.exists_isIso_unitSmulRestrictHom`), and `s|_W = g • m` for a function
`g ∈ Γ(X, W)` whose basic open subset is, by
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`, the non-vanishing locus of
`s` inside `W`. The hypothesis says that this basic open subset is all of `W`, so `g` restricts
to a unit on every open `V ≤ W` and multiplication by `s` is bijective on the sections over `V`;
`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_isIso_app` glues these trivialisations.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop_of_forall_not_vanishesAt`: **a line
  bundle with a nowhere vanishing global section is trivial**, through the explicit
  trivialisation `AlgebraicGeometry.Scheme.Modules.isoUnitOfForallNotVanishesAt`, and
  `AlgebraicGeometry.Scheme.Modules.exists_smul_eq_of_forall_not_vanishesAt`: every global
  section of `L` is a multiple of a nowhere vanishing one.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_smul_iff_notMem_basicOpen_of_forall_not_vanishesAt`:
  the multiple `g • s` of a nowhere vanishing section vanishes exactly outside the basic open
  subset of `g`.
- `AlgebraicGeometry.Scheme.Modules.eq_zero_or_forall_not_vanishesAt`: **the Liouville
  dichotomy** over a scheme whose global functions form a field, with the pointwise form
  `AlgebraicGeometry.Scheme.Modules.forall_not_vanishesAt_of_isField` and the version
  `AlgebraicGeometry.Scheme.Modules.eq_zero_or_forall_not_vanishesAt_of_universallyClosed` for an
  integral scheme universally closed over a field.
- `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_forall_not_vanishesAt`: the same
  dichotomy read in the fibres, through
  `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_isField`.

## Blueprint

This is the Liouville step in the proof of `prop:deg-ample-positive` of
`blueprint/src/version/detailed/curve_estimates/28_degree_of_the_isogeny.tex`: on an irreducible
component `T` of a projective scheme, a section of `𝒪(1)|_T` which vanishes nowhere forces some
homogeneous coordinate to vanish nowhere on `T`, so that `T` lies in a standard affine chart.
-/

@[expose] public section

universe u

open CategoryTheory Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules}

/-- **A line bundle with a nowhere vanishing global section is trivial**: if the global section
`s` of the invertible sheaf `L` vanishes at no point of `X`, then multiplication by `s` is an
isomorphism `𝒪ₓ ≅ L`. -/
theorem isIso_homOfSectionTop_of_forall_not_vanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) : IsIso (homOfSectionTop L s) := by
  refine isIso_of_forall_exists_isIso_app _ fun x ↦ ?_
  obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
  have hmi : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨g, hg⟩ := (bijective_smulSection m (le_refl W)).2 (L.presheaf.map W.leTop.op s)
  have hgW : L.presheaf.map W.leTop.op s = g • m := by
    rw [← hg, smulSection]
    simp only [AddMonoidHom.mk'_apply]
    congr 1
    rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from Subsingleton.elim _ _]
    simp
  have hWg : W ≤ X.basicOpen g := fun y hy ↦
    not_not.1 fun h ↦ hs y ((vanishesAt_iff_notMem_basicOpen m s g hgW hy).2 h)
  refine ⟨W, hxW, fun V hV ↦ ?_⟩
  have hres : L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s =
      X.presheaf.map (homOfLE hV).op g • L.presheaf.map (homOfLE hV).op m := by
    rw [show L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s =
        L.presheaf.map (homOfLE hV).op (L.presheaf.map W.leTop.op s) from by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]; congr 2,
      hgW, Scheme.Modules.map_smul]
  obtain ⟨u, hu⟩ : IsUnit (X.presheaf.map (homOfLE hV).op g) := by
    have h₀ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    have h₂ : X.presheaf.map (homOfLE hV).op g =
        X.presheaf.map (homOfLE (hV.trans hWg)).op
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 2
    rw [h₂]
    exact h₀.map _
  have happ : ∀ r : Γ(X, V), Hom.app (homOfSectionTop L s) V r =
      smulSection m V hV (r * X.presheaf.map (homOfLE hV).op g) := by
    intro r
    rw [Hom.app_homOfSectionTop, hres, smulSection]
    simp only [AddMonoidHom.mk'_apply]
    rw [smul_smul]
  have hmul : Function.Bijective
      (fun r : Γ(X, V) ↦ r * X.presheaf.map (homOfLE hV).op g) := by
    rw [← hu]
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨b * ((u⁻¹ : Γ(X, V)ˣ) : Γ(X, V)), ?_⟩⟩
    · simpa [mul_assoc] using congrArg (fun z ↦ z * ((u⁻¹ : Γ(X, V)ˣ) : Γ(X, V))) hab
    · simp [mul_assoc]
  rw [ConcreteCategory.isIso_iff_bijective, funext happ]
  exact (bijective_smulSection m hV).comp hmul

/-- **The trivialisation of a line bundle by a nowhere vanishing global section.** -/
noncomputable def isoUnitOfForallNotVanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) : L ≅ SheafOfModules.unit X.ringCatSheaf :=
  haveI := isIso_homOfSectionTop_of_forall_not_vanishesAt hL s hs
  (asIso (homOfSectionTop L s)).symm

/-- **Every global section of a line bundle is a multiple of a nowhere vanishing one.** -/
theorem exists_smul_eq_of_forall_not_vanishesAt (hL : L.Invertible) {s : Γ(L, ⊤)}
    (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) : ∃ g : Γ(X, ⊤), g • s = t := by
  have := isIso_homOfSectionTop_of_forall_not_vanishesAt hL s hs
  obtain ⟨g, hg⟩ :=
    (ConcreteCategory.bijective_of_isIso (Hom.app (homOfSectionTop L s) ⊤)).2 t
  exact ⟨g, by rw [← hg, homOfSectionTop_app_top]⟩

/-- **A multiple of a nowhere vanishing section vanishes exactly off the basic open subset of the
multiplier.** -/
theorem vanishesAt_smul_iff_notMem_basicOpen_of_forall_not_vanishesAt {s : Γ(L, ⊤)}
    (hs : ∀ x : X, ¬ L.VanishesAt s x) (g : Γ(X, ⊤)) (x : X) :
    L.VanishesAt (g • s) x ↔ x ∉ X.basicOpen g := by
  rw [vanishesAt_iff, germ_smul, Scheme.mem_basicOpen_top]
  refine ⟨fun h hu ↦ hs x ?_, fun h ↦ Submodule.smul_mem_smul
    (IsLocalRing.mem_maximalIdeal _ |>.2 (mem_nonunits_iff.2 h)) Submodule.mem_top⟩
  obtain ⟨u, hu⟩ := hu
  have hmem := Submodule.smul_mem _ ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) h
  rw [smul_smul, ← hu, Units.inv_mul, one_smul] at hmem
  exact hmem

/-- **The Liouville dichotomy, pointwise.** On a scheme whose ring of global functions is a
field, if one global section of an invertible sheaf vanishes nowhere, then every non-zero global
section vanishes nowhere. -/
theorem forall_not_vanishesAt_of_isField (hX : IsField Γ(X, ⊤)) (hL : L.Invertible)
    {s : Γ(L, ⊤)} (hs : ∀ x : X, ¬ L.VanishesAt s x) {t : Γ(L, ⊤)} (ht : t ≠ 0) (x : X) :
    ¬ L.VanishesAt t x := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_forall_not_vanishesAt hL hs t
  have hg : g ≠ 0 := by
    rintro rfl
    exact ht (zero_smul _ _)
  have hgu : IsUnit g := isUnit_iff_exists_inv.2 (hX.mul_inv_cancel hg)
  rw [vanishesAt_smul_iff_notMem_basicOpen_of_forall_not_vanishesAt hs, not_not,
    (X.isUnit_iff_basicOpen_eq_top g).1 hgu]
  trivial

/-- **The Liouville dichotomy.** On a scheme whose ring of global functions is a field, once one
global section of an invertible sheaf vanishes nowhere, every global section is either zero or
vanishes nowhere. -/
theorem eq_zero_or_forall_not_vanishesAt (hX : IsField Γ(X, ⊤)) (hL : L.Invertible)
    {s : Γ(L, ⊤)} (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) :
    t = 0 ∨ ∀ x : X, ¬ L.VanishesAt t x :=
  or_iff_not_imp_left.2 fun ht x ↦ forall_not_vanishesAt_of_isField hX hL hs ht x

/-- **The Liouville dichotomy on an integral scheme proper over a field.** The field `K` need
not be algebraically closed, and universal closedness suffices for properness. -/
theorem eq_zero_or_forall_not_vanishesAt_of_universallyClosed {K : Type u} [Field K]
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed π] (hL : L.Invertible)
    {s : Γ(L, ⊤)} (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) :
    t = 0 ∨ ∀ x : X, ¬ L.VanishesAt t x :=
  eq_zero_or_forall_not_vanishesAt (isField_of_universallyClosed K π) hL hs t

/-- **The Liouville dichotomy read in the fibres.** A non-zero global section of a line bundle
carrying a nowhere vanishing section has non-zero image in every fibre, as soon as the ring of
global functions is a field. -/
theorem fiberMk_ne_zero_of_forall_not_vanishesAt (hX : IsField Γ(X, ⊤)) (hL : L.Invertible)
    {s : Γ(L, ⊤)} (hs : ∀ x : X, ¬ L.VanishesAt s x) {t : Γ(L, ⊤)} (ht : t ≠ 0) (x : X) :
    fiberMk L x t ≠ 0 :=
  fiberMk_ne_zero_of_isField hX (isoUnitOfForallNotVanishesAt hL s hs) ht x

end AlgebraicGeometry.Scheme.Modules
