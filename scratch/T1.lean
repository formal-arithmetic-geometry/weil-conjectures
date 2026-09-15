module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

theorem isIso_of_forall_bijective_app (φ : M ⟶ N)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W → Function.Bijective (φ.app V)) :
    IsIso φ := by
  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let f : F ⟶ G := ⟨φ.mapPresheaf⟩
  have hinj : Sheaf.IsLocallyInjective f := by
    constructor
    intro U s t hst
    intro x hx
    obtain ⟨W, hxW, hW⟩ := h x
    refine ⟨U.unop ⊓ W, homOfLE inf_le_left, ?_, hx, hxW⟩
    show M.presheaf.map _ s = M.presheaf.map _ t
    refine (hW _ inf_le_right).injective ?_
    rw [Hom.naturality_apply, Hom.naturality_apply]
    exact congrArg _ hst
  have hsurj : Sheaf.IsLocallySurjective f := by
    rw [show Sheaf.IsLocallySurjective f ↔
        TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf from Iff.rfl,
      TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨W, hxW, hW⟩ := h x
    obtain ⟨s, hs⟩ := (hW (U ⊓ W) inf_le_right).surjective (N.presheaf.map (homOfLE inf_le_left).op t)
    exact ⟨U ⊓ W, inf_le_left, ⟨s, hs⟩, hx, hxW⟩
  have hiso : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨hinj, hsurj⟩
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X)]
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map f))

end AlgebraicGeometry.Scheme.Modules
