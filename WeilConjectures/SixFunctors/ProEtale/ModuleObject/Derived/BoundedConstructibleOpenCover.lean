/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Bounded constructibility is local on finite open covers

Let `Λ` be a commutative condensed ring and `X` a scheme with noetherian underlying space, covered
by finitely many opens `Uᵢ`. A complex `K` of module objects over `Λ_X` is bounded constructible
as soon as its restrictions `K|_{Uᵢ}` are
(`ProEtale.CondensedRing.boundedConstructible_of_openCover`). This rests on the open–closed
dévissage: for an open `U` with closed complement `Z`, a module object is zero, respectively
constructible, as soon as its restrictions to `U` and `Z` are
(`ProEtale.CondensedRing.isZero_of_isZero_upperStar_of_isCompl`,
`ProEtale.CondensedRing.isConstructibleModuleObject_of_openClosed`, by concatenating
stratifications), and on an induction on the number of opens, as for étale sheaves
(`AlgebraicGeometry.Etale.boundedConstructible_of_openCover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- On an empty scheme every module object over `Λ` is zero: all sections over the (empty)
objects of the pro-étale site are zero. -/
lemma isZero_mod_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero M :=
  isZero_of_isZero_X _ (IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) _
    (Functor.isZero _ fun T ↦
      have : IsEmpty T.unop.left := ⟨fun t ↦ IsEmpty.false (α := X) (T.unop.hom.base t)⟩
      (ProEt.isTerminalSectionsOfIsEmpty M.X T.unop).isZero))

/-- If the restriction of `j^* M` along `g` is pro-étale locally finitely presented, so is the
restriction of `M` along `g ≫ j`. -/
lemma isLocallyFinitelyPresented_mapMod_comp {W U X : Scheme.{u}} (g : W ⟶ U) (j : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsLocallyFinitelyPresented ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ U))
      (((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ U)).obj ((j)^*⟦Λ⟧.obj M))) :
    IsLocallyFinitelyPresented ((g ≫ j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((g ≫ j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M) := by
  refine (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2 (IsLocallyFinitelyPresented.of_iso ?_
    ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 h))
  exact ((upperStarComp Λ g j).app _).symm

/-- **Open–closed dévissage of constructibility**: for an open immersion `j` with quasi-compact
range and a closed immersion `i` onto its complement, a module object whose restrictions along `j`
and `i` are constructible is constructible, along the concatenated stratification
(`Scheme.Stratification.openClosed`). -/
theorem isConstructibleModuleObject_of_openClosed {X U Z : Scheme.{u}} (j : U ⟶ X)
    (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hU : IsConstructibleModuleObject (condensedRingObj Λ U) ((j)^*⟦Λ⟧.obj M))
    (hZ : IsConstructibleModuleObject (condensedRingObj Λ Z) ((i)^*⟦Λ⟧.obj M)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  obtain ⟨SU, hSU⟩ := hU
  obtain ⟨SZ, hSZ⟩ := hZ
  refine ⟨Stratification.openClosed j i hij SU SZ, fun k ↦ ?_⟩
  change IsLocallyFinitelyPresented
      ((Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
        (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
        (finSumFinEquiv.symm k))^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M)
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · exact isLocallyFinitelyPresented_mapMod_comp Λ (SU.immersion l) j M (hSU l)
  · exact isLocallyFinitelyPresented_mapMod_comp Λ (SZ.immersion l) i M (hSZ l)

end AlgebraicGeometry.ProEtale.CondensedRing
