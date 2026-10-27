/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.EtalePresentedRecoveryData

/-! # Local cokernels of étale free presentations

Source: Stacks Project, Descent, Tag 03DX, first paragraph of the proof.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The local part of effective recovery, before any overlap or global descent.
Source: Stacks 03DX (blueprint: lem-trf-etale-presented-local-cokernels). -/
structure EtalePresentedLocalRecovery
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T) (I : Type w) (U : I → T.Etale)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G) where
  /-- Canonical free comparisons, normalized by their adjoints on free generators. -/
  freeIso : ∀ (i : I) (A : Type u),
    (c (U i).left).extension.obj
      (SheafOfModules.free (R := (U i).left.ringCatSheaf) A) ≅
        SheafOfModules.free (R := smallEtaleModuleRing (U i).left) A
  freeIso_hom : ∀ (i : I) (A : Type u),
    (freeIso i A).hom = presentedEtaleFreeMap (c (U i).left) A
  /-- The unique lifted presentation matrices. -/
  lift : ∀ i, SheafOfModules.free (R := (U i).left.ringCatSheaf) (K i) ⟶
    SheafOfModules.free (J i)
  lift_image : ∀ i, (c (U i).left).extension.map (lift i) ≫ (freeIso i (J i)).hom =
    (freeIso i (K i)).hom ≫ d i
  lift_unique : ∀ i (h : SheafOfModules.free (R := (U i).left.ringCatSheaf) (K i) ⟶
      SheafOfModules.free (J i)),
    (c (U i).left).extension.map h ≫ (freeIso i (J i)).hom =
      (freeIso i (K i)).hom ≫ d i → h = lift i
  /-- The cokernel object and projection, with their full universal property. -/
  localModule : ∀ i, (U i).left.Modules
  localQuotient : ∀ i, SheafOfModules.free (R := (U i).left.ringCatSheaf) (J i) ⟶
    localModule i
  localZero : ∀ i, lift i ≫ localQuotient i = 0
  localCokernel : ∀ i, Nonempty (IsColimit (CokernelCofork.ofπ
    (localQuotient i) (localZero i)))
  localQC : ∀ i, (localModule i).IsQuasicoherent
  localIso : ∀ i, (c (U i).left).extension.obj (localModule i) ≅
    (presentedEtaleRestriction (U i)).obj G
  local_projection : ∀ i,
    (c (U i).left).extension.map (localQuotient i) ≫ (localIso i).hom =
      (freeIso i (J i)).hom ≫ q i
  /-- Tensor coordinates for the local comparisons, fixed by the unit on opens. -/
  localTensor : ∀ i,
    (SheafOfModules.toSheaf (smallEtaleModuleRing (U i).left)).obj
      ((c (U i).left).extension.obj (localModule i)) ≅
        @etaleTensorSectionsSheaf (U i).left (localModule i) (localQC i)
  local_linear : ∀ (i : I) (A : (U i).left.Etale) (r : Γ(A.left, ⊤))
    (s : ((c (U i).left).extension.obj (localModule i)).val.obj (op A)),
    (localTensor i).hom.hom.app (op A) (r • s) =
      r • (@id (Γ((tensorPullback A.hom).obj (localModule i), ⊤))
        ((localTensor i).hom.hom.app (op A) s))
  local_unit : ∀ (i : I) (W : (U i).left.Opens),
    ((c (U i).left).adjunction.unit.app (localModule i)).app W ≫
      (localTensor i).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale (U i).left).obj W)) ≫
        (tensorOpenSectionIso (U i).left (localModule i) W).hom = 𝟙 _

/-- Lift each free presentation and form its quasi-coherent Zariski cokernel.
Source: Stacks Project, Descent, Tag 03DX, first paragraph of the proof
(blueprint: lem-trf-etale-presented-local-cokernels).

Proof: The structure module is quasi-coherent by the affine rank-one tilde
calculation. Coproduct closure makes every small free module quasi-coherent.
Tensor extension preserves coproducts and the structure module; its comparison
on free objects is the adjoint of the specified generator sections, hence is
exactly presentedEtaleFreeMap. Full faithfulness on quasi-coherent modules
lifts each d uniquely, after conjugating by these free comparisons. Form the
categorical cokernel of this lift and use cokernel closure for quasi-coherence.
Extension preserves its cokernel. Transport its cofork by the free comparisons;
the supplied cofork q is another colimit of the same diagram. Uniqueness of
colimits gives localIso and the projection equation. The normalized tensor
comparison from etaleExtension_free_presentations_hom gives localTensor,
its scalar equation and the open-unit equation. Contexts contain only proof
fields, so proof irrelevance identifies the context in that theorem with c.
No covering or global descent is used, even for empty index or basis types. -/
theorem etalePresented_localCokernels
    (c : ∀ X : Scheme.{u}, ZariskiEtaleModuleContext X)
    (T : Scheme.{u}) (G : SmallEtaleModules T)
    (I : Type w) (U : I → T.Etale)
    (K J : I → Type u)
    (d : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (K i) ⟶
      SheafOfModules.free (J i))
    (q : ∀ i, SheafOfModules.free (R := smallEtaleModuleRing (U i).left) (J i) ⟶
      (presentedEtaleRestriction (U i)).obj G)
    (zero : ∀ i, d i ≫ q i = 0)
    (presentation : ∀ i, Nonempty (IsColimit (CokernelCofork.ofπ (q i) (zero i)))) :
    Nonempty (EtalePresentedLocalRecovery c T G I U K J d q) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
