/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.LerayAcyclicAdditiveNaturality
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural

/-! # Linear Leray comparison for an acyclic direct image

## References

* Stacks Project, Tag 01F4 (1), Lemma 20.13.6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The degenerate Leray comparison respects scalars from any scheme below the target.
(Stacks, Tag 01F4 (1) and Tag 01EY) -/
theorem nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
    {Y X T : Scheme.{u}} (p : Y ⟶ X) (f : X ⟶ T)
    [HasInjectiveResolutions Y.Modules] (F : Y.Modules)
    (hF : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage p q).obj F)) (q : ℕ) :
    letI : Module Γ(T, ⊤) (((pushforward p).obj F).H q) :=
      Module.compHom _ f.appTop.hom
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (p ≫ f).appTop.hom
    Nonempty (((pushforward p).obj F).H q ≃ₗ[Γ(T, ⊤)] F.H q) := by
  let : Module Γ(T, ⊤) (((pushforward p).obj F).H q) :=
    Module.compHom _ f.appTop.hom
  let : Module Γ(T, ⊤) (F.H q) := Module.compHom _ (p ≫ f).appTop.hom
  obtain ⟨e, he⟩ :=
    exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing p F hF q
  refine ⟨{ toAddEquiv := e, map_smul' := ?_ }⟩
  intro r x
  change e (H.map (((pushforward p).obj F).smulHom (f.appTop r)) q x) =
    H.map (F.smulHom ((p ≫ f).appTop r)) q (e x)
  rw [← pushforward_map_smulHom]
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    he (F.smulHom (p.appTop (f.appTop r))) x

end AlgebraicGeometry.Scheme.Modules
