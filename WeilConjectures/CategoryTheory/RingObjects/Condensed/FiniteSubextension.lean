/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!

# The inclusions `E̲ ⟶ F̲ ⟶ ℚ̲̄_ℓ` of condensed coefficient rings

Let `ℓ` be a prime. The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` form the directed poset
`PadicAlgCl.FiniteIntermediateField ℓ`. For each of them the condensed ring `E̲ = C(-, E)` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` is a commutative ring object
`Profinite.padicSubfieldRingObj ℓ E` of condensed abelian groups, and this file records the
inclusions between them:

* for `E ≤ F`, the inclusion `E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`), postcomposition
  with the inclusion `E ⊆ F`, strictly functorial in `E ≤ F`;
* the inclusion `E̲ ⟶ ℚ̲̄_ℓ` (`Profinite.padicSubfieldRingObjToPadicAlgCl`): a continuous map
  `S → E` is a section of `ℚ̲̄_ℓ` over `S`, taking values in the finite subextension `E`;

compatibly with each other (`Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl`). All of them
are morphisms of ring objects. Their pullbacks along `p_X` are the coefficient changes
`E_X ⟶ F_X ⟶ ℚ̄_ℓ,X` on a scheme `X`.

## `ℚ̲̄_ℓ` as the colimit of the `E̲`

The inclusions `E̲ ⟶ ℚ̲̄_ℓ` form a cocone `Profinite.padicAlgClRingObjCocone` over the diagram
`E ↦ E̲` (`Profinite.padicSubfieldRingObjFunctor`) of condensed abelian groups, indexed by the
filtered poset of finite subextensions, and this cocone is a colimit
(`Profinite.isColimitPadicAlgClRingObjCocone`): `ℚ̲̄_ℓ = colim_E E̲`. This is the comparison
identity `eq:Qbar-comparison` of `WeilConjectures/RefactorInstruction.tex` (Proposition
`prop:comparison-only`); it is a theorem, not the definition of `ℚ̲̄_ℓ`, which is defined by its
sections. It holds because filtered colimits of condensed abelian groups are computed
sectionwise on profinite sets (the coverings of `*_proét` being refined by finite ones), and
sectionwise `ℚ̲̄_ℓ(S)` is the union of the subgroups `C(S, E)` of `C(S, ℚ̄_ℓ)` by definition.

## Sorried input

* `Profinite.isColimitPadicAlgClRingObjCocone`: `ℚ̲̄_ℓ = colim_E E̲`, see above.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

instance : CoeSort (FiniteIntermediateField ℓ) Type := ⟨fun E ↦ E.1⟩

/-- The poset of finite subextensions, as a category, is filtered: it is directed and
nonempty. -/
instance : IsFiltered (FiniteIntermediateField ℓ) := isFiltered_of_directed_le_nonempty _

end PadicAlgCl

namespace Profinite

open AlgebraicGeometry.ProEtale PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusions `E̲ ⟶ F̲` -/

/-- The inclusion `E̲ ⟶ F̲` of condensed rings, for finite subextensions `E ≤ F`: postcomposition
with the inclusion `E ⊆ F`, which is continuous for the topologies restricted from `ℚ̄_ℓ`. -/
noncomputable def padicSubfieldCondensedRingMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldCondensedRing.{u} ℓ E ⟶ padicSubfieldCondensedRing ℓ F :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
  continuousMapRingSheafMap (IntermediateField.inclusion h).toRingHom
    (continuous_induced_rng.mpr continuous_induced_dom)

/-- The inclusion `E̲ ⟶ F̲` of ring objects of condensed abelian groups, for finite subextensions
`E ≤ F`: the abelian sheaf morphism underlying `Profinite.padicSubfieldCondensedRingMap`. -/
noncomputable def padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObj.{u} ℓ E ⟶ padicSubfieldRingObj ℓ F :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingMap ℓ h)

instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (padicSubfieldRingObjMap.{u} ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingMap ℓ h)))

lemma padicSubfieldRingObjMap_id (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap.{u} ℓ (le_refl E) = 𝟙 _ := rfl

lemma padicSubfieldRingObjMap_comp {E F H : FiniteIntermediateField ℓ} (h₁ : E ≤ F)
    (h₂ : F ≤ H) :
    padicSubfieldRingObjMap.{u} ℓ (h₁.trans h₂) =
      padicSubfieldRingObjMap ℓ h₁ ≫ padicSubfieldRingObjMap ℓ h₂ := rfl

/-! ### The inclusions `E̲ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `C(-, E) ⟶ ℚ̲̄_ℓ` of presheaves of rings on profinite sets, for a finite
subextension `E`: a continuous map `S → E`, composed with the inclusion `E ⊆ ℚ̄_ℓ`, takes values
in the finite subextension `E`. -/
noncomputable def padicSubfieldToPadicAlgClRingPresheaf (E : FiniteIntermediateField ℓ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    continuousMapRingPresheaf.{u} E ⟶ padicAlgClRingPresheaf ℓ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  { app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((((algebraMap E (PadicAlgCl ℓ)).compLeftContinuous S.unop
          (continuous_algebraMap_padicAlgCl_of_algebra ℓ E)).codRestrict
        (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)
        (fun a ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff ℓ _ _).mpr
          ⟨E.1, E.2, fun x ↦ (a x).2⟩)).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := rfl }

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings, for a finite subextension `E`. -/
noncomputable def padicSubfieldCondensedRingToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldCondensedRing.{u} ℓ E ⟶ padicAlgClCondensedRing ℓ :=
  ⟨padicSubfieldToPadicAlgClRingPresheaf ℓ E⟩

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicSubfieldCondensedRingToPadicAlgCl`. -/
noncomputable def padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObj.{u} ℓ E ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingToPadicAlgCl ℓ E)

instance (E : FiniteIntermediateField ℓ) :
    IsMonHom (padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingToPadicAlgCl ℓ E)))

/-- The inclusion `E̲ ⟶ F̲` followed by the inclusion `F̲ ⟶ ℚ̲̄_ℓ` is the inclusion
`E̲ ⟶ ℚ̲̄_ℓ`: both send a continuous map `S → E` to the same map into `ℚ̄_ℓ`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap.{u} ℓ h ≫ padicSubfieldRingObjToPadicAlgCl ℓ F =
      padicSubfieldRingObjToPadicAlgCl ℓ E := by
  rw [padicSubfieldRingObjMap, padicSubfieldRingObjToPadicAlgCl,
    padicSubfieldRingObjToPadicAlgCl, ← Functor.map_comp]
  rfl

/-! ### `ℚ̲̄_ℓ` as the colimit of the `E̲` -/

/-- The diagram `E ↦ E̲` of ring objects of condensed abelian groups, indexed by the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` ordered by inclusion. -/
noncomputable def padicSubfieldRingObjFunctor :
    FiniteIntermediateField ℓ ⥤ Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} where
  obj E := padicSubfieldRingObj ℓ E
  map f := padicSubfieldRingObjMap ℓ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone over the diagram `E ↦ E̲` with vertex `ℚ̲̄_ℓ`, given by the inclusions
`E̲ ⟶ ℚ̲̄_ℓ`. -/
noncomputable def padicAlgClRingObjCocone : Cocone (padicSubfieldRingObjFunctor.{u} ℓ) where
  pt := padicAlgClRingObj ℓ
  ι :=
    { app E := padicSubfieldRingObjToPadicAlgCl ℓ E
      naturality _ _ f :=
        (padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- **`ℚ̲̄_ℓ = colim_E E̲`**: the inclusions `E̲ ⟶ ℚ̲̄_ℓ` exhibit the condensed ring `ℚ̲̄_ℓ` as the
filtered colimit of the condensed rings `E̲` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, in
condensed abelian groups. See the module docstring. -/
noncomputable def isColimitPadicAlgClRingObjCocone :
    IsColimit (padicAlgClRingObjCocone.{u} ℓ) :=
  sorry

end Profinite
