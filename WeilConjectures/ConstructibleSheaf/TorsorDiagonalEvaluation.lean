/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant

/-!
# Evaluation on the diagonal section of a torsor

For a finite Galois cover `c.P → V`, evaluating equivariant sections on the graph section
identifies the restriction to `c.P` of the equivariant module presheaf with the presheaf
underlying the constant module sheaf.

## Implementation details

For `W` étale over `c.P`, the torsor isomorphism identifies `W ×_V c.P` with a disjoint union
of copies of `W` indexed by `P`; the inverse of evaluation extends a locally constant function
`t` on `W` by `ρ(g)(t(w))` on the `g`-translate of the graph. Locally constant functions are
then identified with sections of the constant module sheaf. This avoids sheafifying the
equivariant presheaf or invoking inverse image.

## References

* [Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- The equivariant presheaf restricted to `c.P` is the presheaf underlying the
constant module sheaf, naturally in the representation. -/
theorem equivariantModulePresheaf_diagonal {V : Scheme.{u}} (ℓ : ℕ)
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    Nonempty (
      c.equivariantModulePresheafFunctor ℓ ⋙
        (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)) ⋙
        (Functor.whiskeringLeft c.P.Etaleᵒᵖ V.Etaleᵒᵖ _).obj
          (MorphismProperty.Over.map ⊤ c.etale).op ≅
      forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
        constantSheaf c.P.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
        sheafToPresheaf c.P.smallEtaleTopology _) := by
  let R := ULift.{u + 1} (ZMod ℓ)
  let S := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : R →+* ZMod ℓ)
  let F := c.equivariantModulePresheafFunctor ℓ ⋙
    (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj S ⋙
    (Functor.whiskeringLeft c.P.Etaleᵒᵖ V.Etaleᵒᵖ _).obj
      (MorphismProperty.Over.map ⊤ c.etale).op
  let G := forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙ S
  let e : F ≅ G ⋙ Scheme.Etale.locallyConstantModulePresheafFunctor c.P R :=
    NatIso.ofComponents (fun N ↦
      NatIso.ofComponents (fun W ↦
        (LinearEquiv.ofBijective (c.diagonalEvaluation ℓ N W.unop).hom
          (c.diagonalEvaluation_bijective ℓ N W.unop)).toModuleIso) (by
        intro W W' f
        ext s
        apply LocallyConstant.ext
        intro x
        change s.val (c.sectionRestriction
          ((MorphismProperty.Over.map ⊤ c.etale).map f.unop)
          (c.diagonalSection W'.unop x)) =
          s.val (c.diagonalSection W.unop (f.unop.left x))
        have h : c.diagonalSection W'.unop ≫ c.sectionRestriction
            ((MorphismProperty.Over.map ⊤ c.etale).map f.unop) =
            f.unop.left ≫ c.diagonalSection W.unop := by
          apply Limits.pullback.hom_ext <;>
            simp [diagonalSection, sectionRestriction, MorphismProperty.Over.w f.unop]
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun k ↦ s.val (k x)) h)) (by
      intro N N' f
      ext W s
      rfl)
  obtain ⟨h⟩ := Scheme.Etale.locallyConstantModulePresheafFunctor_iso_constantSheaf c.P R
  exact ⟨e ≪≫ Functor.isoWhiskerLeft G h⟩

end AlgebraicGeometry.Scheme.GaloisCover
