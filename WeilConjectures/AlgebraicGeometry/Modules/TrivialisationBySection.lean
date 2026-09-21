/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle
public import WeilConjectures.AlgebraicGeometry.Modules.VanishingFibre

/-!
# Trivialising a line bundle by a nowhere vanishing section, and the Liouville dichotomy

Let `X` be a scheme and `L` an invertible sheaf of `𝒪ₓ`-modules carrying a global section `s`
which vanishes at no point of `X`, in the sense of
`AlgebraicGeometry.Scheme.Modules.VanishesAt`. Multiplication by `s` is then an isomorphism
`𝒪ₓ ≅ L`, so `L` is trivial and every global section of `L` is `g • s` for a unique global
function `g`, vanishing exactly where `g` does — the last point being
`AlgebraicGeometry.Scheme.Modules.vanishesAt_smul_iff_notMem_basicOpen`, which needs no
hypothesis on `L`.

When moreover `Γ(X, 𝒪ₓ)` is a field — for instance when `X` is an integral scheme, universally
closed over a field, by `AlgebraicGeometry.isField_of_universallyClosed` — a non-zero `g` is a
unit, hence vanishes nowhere. This is the **Liouville dichotomy**: on such an `X`, once *one*
global section of `L` vanishes nowhere, every other global section either vanishes identically
or vanishes nowhere.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.isoUnitOfForallNotVanishesAt`: the trivialisation `L ≅ 𝒪ₓ`
  attached to a nowhere vanishing global section, and
  `AlgebraicGeometry.Scheme.Modules.sectionsEquivOfForallNotVanishesAt`: the induced
  `Γ(X, 𝒪ₓ)`-linear equivalence `Γ(X, 𝒪ₓ) ≃ Γ(L, ⊤)`, `g ↦ g • s`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop_of_forall_not_vanishesAt`: **a line
  bundle with a nowhere vanishing global section is trivial**, with the converse in
  `AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop_iff_forall_not_vanishesAt` and
  `AlgebraicGeometry.Scheme.Modules.existsUnique_smul_eq_of_forall_not_vanishesAt`: every global
  section of `L` is a multiple of a nowhere vanishing one, by a unique global function.
- `AlgebraicGeometry.Scheme.Modules.eq_zero_or_forall_not_vanishesAt`: **the Liouville
  dichotomy** over a scheme whose global functions form a field, with the pointwise form
  `AlgebraicGeometry.Scheme.Modules.not_vanishesAt_of_isField` and the version
  `AlgebraicGeometry.Scheme.Modules.eq_zero_or_forall_not_vanishesAt_of_universallyClosed` for an
  integral scheme universally closed over a field.
- `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_forall_not_vanishesAt`: the same
  dichotomy read in the fibres, through
  `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_isField`.

## Implementation notes

The trivialisation is the fibrewise criterion
`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_fiberMap_ne_zero` read through
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_fiberMk_eq_zero`, which identifies the two
spellings of non-vanishing that the project uses. Everything else in the file is a consequence of
that trivialisation, so the two forms of the dichotomy — in the germs and in the fibres — are the
same statement read through the same bridge, not two independent arguments.

Throughout, the distinguished nowhere vanishing section `s` is an explicit argument, while the
section `t` being tested is implicit, inferred from the hypothesis made on it. The dichotomy in
the fibres is named `fiberMk_ne_zero_of_forall_not_vanishesAt` after the nowhere vanishing
hypothesis rather than after the field hypothesis, because
`AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_isField` is the name of the statement it is
deduced from.

## Blueprint

This is the Liouville step in the proof of `prop:deg-ample-positive` of
`blueprint/src/version/detailed/curve_estimates/28_degree_of_the_isogeny.tex`, recorded there as
`lem:deg-liouville-dichotomy`: on an irreducible component `T` of a projective scheme, taken with
its reduced induced structure so that it is integral, a section of `𝒪(1)|_T` which vanishes
nowhere forces some homogeneous coordinate to vanish nowhere on `T`, so that `T` lies in a
standard affine chart.
-/

@[expose] public section

universe u

open CategoryTheory Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules}

/-- **A line bundle with a nowhere vanishing global section is trivial**: if the global section
`s` of the invertible sheaf `L` vanishes at no point of `X`, then multiplication by `s` is an
isomorphism `𝒪ₓ ≅ L`.

This is the fibrewise criterion
`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_fiberMap_ne_zero` applied to multiplication by
`s`, whose fibre at `x` is non-zero exactly when the image of `s` in `L(x)` is
(`AlgebraicGeometry.Scheme.Modules.fiberMk_eq_zero_iff_fiberMap_homOfSectionTop`), that is
exactly when `s` does not vanish at `x`
(`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_fiberMk_eq_zero`). -/
theorem isIso_homOfSectionTop_of_forall_not_vanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) : IsIso (homOfSectionTop L s) :=
  isIso_of_forall_fiberMap_ne_zero (SheafOfModules.invertible_unit X.sheaf) hL _ fun x h ↦
    hs x ((vanishesAt_iff_fiberMk_eq_zero hL s x).2
      ((fiberMk_eq_zero_iff_fiberMap_homOfSectionTop L s x).2 h))

/-- **A line bundle is trivialised by a global section exactly when that section vanishes
nowhere.** -/
theorem isIso_homOfSectionTop_iff_forall_not_vanishesAt (hL : L.Invertible) (s : Γ(L, ⊤)) :
    IsIso (homOfSectionTop L s) ↔ ∀ x : X, ¬ L.VanishesAt s x :=
  ⟨fun h x ↦ not_vanishesAt_of_isIso_homOfSectionTop h x,
    isIso_homOfSectionTop_of_forall_not_vanishesAt hL s⟩

/-- The inverse of multiplication by a nowhere vanishing global section `s`, as an isomorphism
`L ≅ 𝒪ₓ`; see
`AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop_of_forall_not_vanishesAt`. -/
noncomputable def isoUnitOfForallNotVanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) : L ≅ unit X.ringCatSheaf :=
  haveI := isIso_homOfSectionTop_of_forall_not_vanishesAt hL s hs
  (asIso (homOfSectionTop L s)).symm

/-- **The global sections of a line bundle with a nowhere vanishing section `s` are the global
functions**, by `g ↦ g • s`. This is the trivialisation
`AlgebraicGeometry.Scheme.Modules.isoUnitOfForallNotVanishesAt` read on global sections. -/
noncomputable def sectionsEquivOfForallNotVanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) : Γ(X, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(L, ⊤) :=
  haveI := isIso_homOfSectionTop_of_forall_not_vanishesAt hL s hs
  sectionsEquivOfIso (asIso (homOfSectionTop L s)) ⊤

@[simp]
lemma sectionsEquivOfForallNotVanishesAt_apply (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) (g : Γ(X, ⊤)) :
    sectionsEquivOfForallNotVanishesAt hL s hs g = g • s :=
  homOfSectionTop_app_top L s g

/-- **Every global section of a line bundle is a multiple of a nowhere vanishing one, by a unique
global function.** -/
theorem existsUnique_smul_eq_of_forall_not_vanishesAt (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) : ∃! g : Γ(X, ⊤), g • s = t := by
  obtain ⟨hinj, hsurj⟩ := (sectionsEquivOfForallNotVanishesAt hL s hs).bijective
  obtain ⟨g, hg⟩ := hsurj t
  rw [sectionsEquivOfForallNotVanishesAt_apply] at hg
  refine ⟨g, hg, fun g' hg' ↦ hinj ?_⟩
  rw [sectionsEquivOfForallNotVanishesAt_apply, sectionsEquivOfForallNotVanishesAt_apply, hg', hg]

/-- **The Liouville dichotomy read in the fibres.** A non-zero global section of a line bundle
carrying a nowhere vanishing section has non-zero image in every fibre, as soon as the ring of
global functions is a field. -/
theorem fiberMk_ne_zero_of_forall_not_vanishesAt (hX : IsField Γ(X, ⊤)) (hL : L.Invertible)
    (s : Γ(L, ⊤)) (hs : ∀ x : X, ¬ L.VanishesAt s x) {t : Γ(L, ⊤)} (ht : t ≠ 0) (x : X) :
    fiberMk L x t ≠ 0 :=
  fiberMk_ne_zero_of_isField hX (isoUnitOfForallNotVanishesAt hL s hs) ht x

/-- **The Liouville dichotomy, pointwise.** On a scheme whose ring of global functions is a
field, if one global section of an invertible sheaf vanishes nowhere, then every non-zero global
section vanishes nowhere. This is
`AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_forall_not_vanishesAt` read in the germs. -/
theorem not_vanishesAt_of_isField (hX : IsField Γ(X, ⊤)) (hL : L.Invertible) (s : Γ(L, ⊤))
    (hs : ∀ x : X, ¬ L.VanishesAt s x) {t : Γ(L, ⊤)} (ht : t ≠ 0) (x : X) :
    ¬ L.VanishesAt t x := fun h ↦
  fiberMk_ne_zero_of_forall_not_vanishesAt hX hL s hs ht x
    ((vanishesAt_iff_fiberMk_eq_zero hL t x).1 h)

/-- **The Liouville dichotomy.** On a scheme whose ring of global functions is a field, once one
global section of an invertible sheaf vanishes nowhere, every global section is either zero or
vanishes nowhere. -/
theorem eq_zero_or_forall_not_vanishesAt (hX : IsField Γ(X, ⊤)) (hL : L.Invertible)
    (s : Γ(L, ⊤)) (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) :
    t = 0 ∨ ∀ x : X, ¬ L.VanishesAt t x :=
  or_iff_not_imp_left.2 fun ht x ↦ not_vanishesAt_of_isField hX hL s hs ht x

/-- **The Liouville dichotomy on an integral scheme proper over a field.** The field `K` need
not be algebraically closed, and universal closedness suffices for properness. -/
theorem eq_zero_or_forall_not_vanishesAt_of_universallyClosed {K : Type u} [Field K]
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed π] (hL : L.Invertible)
    (s : Γ(L, ⊤)) (hs : ∀ x : X, ¬ L.VanishesAt s x) (t : Γ(L, ⊤)) :
    t = 0 ∨ ∀ x : X, ¬ L.VanishesAt t x :=
  eq_zero_or_forall_not_vanishesAt (isField_of_universallyClosed K π) hL s hs t

end AlgebraicGeometry.Scheme.Modules
