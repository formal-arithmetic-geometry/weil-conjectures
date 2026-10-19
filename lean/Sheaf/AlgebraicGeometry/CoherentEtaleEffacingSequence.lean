/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality

/-! # Simultaneous effacement for the coherent comparison

Source: Stacks Project, Tags 0BDY, 03P2 and 010T.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.CoherentEtale
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_section_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {F G : Y.Modules} (φ : F ⟶ G) [Mono φ] :
    Mono (((tensorPullback f).map φ).app ⊤) := by
  let : PreservesFiniteLimits (tensorPullback f) :=
    (AlgebraicGeometry.flat_module_pullback_exact_pushforward_injective f).1.1
  have : Mono ((tensorPullback f).map φ) := inferInstance
  have : Mono ((toPresheaf X).map ((tensorPullback f).map φ)) := inferInstance
  change Mono (((toPresheaf X).map ((tensorPullback f).map φ)).app (op ⊤))
  infer_instance

private theorem coefficient_mono (X : Scheme.{u})
    (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) [Mono φ] : Mono (m F G φ) := by
  have h (U : X.Etaleᵒᵖ) : Mono ((m F G φ).hom.app U) := by
    rw [hm F G φ U.unop]
    let := tensor_section_mono U.unop.hom φ
    infer_instance
  let : ∀ U, Mono ((m F G φ).hom.app U) := h
  let : Mono (m F G φ).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mono_of_mono_map
    (show Mono (m F G φ).hom from inferInstance)

private theorem coefficient_map_sheafify (X : Scheme.{u}) (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (etaleTensorSectionsFunctor X).map φ ≫ (etaleTensorSectionsFunctorObjIso G).hom =
      (etaleTensorSectionsFunctorObjIso F).hom ≫ m F G φ := by
  have h : Functor.whiskerRight (etaleTensorSectionsMap φ)
      AddCommGrpCat.uliftFunctor.{u + 1, u} = (m F G φ).hom := by
    apply NatTrans.ext
    funext U
    exact (hm F G φ U.unop).symm
  change (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (etaleTensorSectionsMap φ) AddCommGrpCat.uliftFunctor) ≫ _ = _
  rw [h]
  exact (sheafificationNatIso X.smallEtaleTopology AddCommGrpCat.{u + 1}).inv.naturality
    (m F G φ)

private theorem coefficient_shortExact (X : Scheme.{u}) (m : Maps X)
    (hm : ∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤))
    (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    ∃ hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0,
      (ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz).ShortExact := by
  let T := etaleTensorSectionsFunctor X
  let : T.Additive := by
    dsimp [T, etaleTensorSectionsFunctor]
    infer_instance
  let : T.PreservesZeroMorphisms :=
    etaleTensorSectionsFunctor_preservesZeroMorphisms X
  let := preservesCokernels_etaleTensorSectionsFunctor X
  let : PreservesFiniteColimits T :=
    Functor.preservesFiniteColimits_of_preservesCokernels T
  have h₁ := coefficient_map_sheafify X m hm S.X₁ S.X₂ S.f
  have h₂ := coefficient_map_sheafify X m hm S.X₂ S.X₃ S.g
  have hz : m S.X₁ S.X₂ S.f ≫ m S.X₂ S.X₃ S.g = 0 := by
    apply (cancel_epi (etaleTensorSectionsFunctorObjIso S.X₁).hom).mp
    rw [← Category.assoc, ← h₁, Category.assoc, ← h₂,
      ← Category.assoc, ← T.map_comp, S.zero, T.map_zero, zero_comp, comp_zero]
  let R := ShortComplex.mk (m S.X₁ S.X₂ S.f) (m S.X₂ S.X₃ S.g) hz
  let e : S.map T ≅ R := ShortComplex.isoMk
    (etaleTensorSectionsFunctorObjIso S.X₁)
    (etaleTensorSectionsFunctorObjIso S.X₂)
    (etaleTensorSectionsFunctorObjIso S.X₃) h₁.symm h₂.symm
  let := hS.mono_f
  let := hS.epi_g
  have hmono : Mono (m S.X₁ S.X₂ S.f) := coefficient_mono X m hm S.f
  have hmonocomp : Mono (T.map S.f ≫ (etaleTensorSectionsFunctorObjIso S.X₂).hom) := by
    rw [h₁]
    infer_instance
  let : Mono (T.map S.f) := mono_of_mono _ (etaleTensorSectionsFunctorObjIso S.X₂).hom
  have hST : (S.map T).ShortExact := ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel T inferInstance inferInstance)
    (show Mono (T.map S.f) from inferInstance)
    (show Epi (T.map S.g) from inferInstance)
  exact ⟨hz, ShortComplex.shortExact_of_iso e hST⟩

private theorem acyclic_groups (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ)
    (hz : IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G)) :
    Subsingleton (Source X G q) ∧ Subsingleton (Target X G q) := by
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let e := (moduleCohomologyExtResolutionEquiv X G q).trans
    (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
      Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm)
  let : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G) :=
    ModuleCat.subsingleton_of_isZero hz
  refine ⟨e.symm.injective.subsingleton, ?_⟩
  obtain ⟨_, _, c, _, _⟩ := etale_zariski_qcoh_comparison X
  let : Subsingleton (@Sheaf.H _ _ X.smallEtaleTopology
      (etaleTensorSectionsSheaf G) inferInstance (HasExt.standard _) q) :=
    (c G q).symm.injective.subsingleton
  obtain ⟨l, _⟩ := exists_etaleTensorSectionsSheaf_cohomology_ulift_natural X G q
  exact l.injective.subsingleton

/-- Acyclic embeddings can be completed to sequences exact on both sites.
Source: Stacks Project, Tag 0BDY, Lemma 30.4.3(1); Tag 03P2; Tag 03DW(2).
(blueprint: lem-pbc-coherent-etale-effacing-sequence).

Proof: Properness over the field implies quasi-compactness and affine diagonal.
Embed F in the pushforward of its pullback to the finite disjoint union of a
finite affine open cover, using exists_quasicoherent_acyclic_embedding. Call this
module G and take Q to be the cokernel of the embedding. Cokernels preserve
quasi-coherence. Forgetting module scalars is exact. Tensor pullback along an
etale morphism is exact since it is flat; the sheaf of its sections is exact
because local lifts on Zariski covers are also local lifts on the etale site.
Thus the component prescription for m gives a short exact sequence on the etale
site. Coefficient lift is exact as well. The module cohomology of G vanishes in
positive degrees by construction. The module/abelian resolution comparison and
canonical Ext universe transport give vanishing of Source X G (n+1). The stated
etale--Zariski comparison followed by the coefficient-lift comparison gives
vanishing of Target X G (n+1). This includes the empty scheme, using the empty
finite affine cover and its zero section complex. -/
theorem exists_effacing_sequence {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (m : Maps X)
    (hm : ∀ (F G : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (U : X.Etale),
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤))
 :
    Effaces X m := by
  classical
  intro F hF n
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated :=
    HasAffineProperty.iff_of_isAffine.mp (inferInstance : IsSeparated f)
  let : IsAffineHom (pullback.diagonal (X ↘ Spec (.of k))) := inferInstance
  obtain ⟨G, hG, i, hi, hacyc⟩ := exists_quasicoherent_acyclic_embedding k X F
  let := hG
  let : Mono i := hi
  let Q := cokernel i
  have hQ : Q.IsQuasicoherent := isQuasicoherent_cokernel i
  let := hQ
  let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.cokernelSequence i
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) hi inferInstance
  have ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact :=
    hS.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  let : S.X₁.IsQuasicoherent := hF
  let : S.X₂.IsQuasicoherent := hG
  let : S.X₃.IsQuasicoherent := hQ
  obtain ⟨hz, he⟩ := coefficient_shortExact X m hm S hS
  obtain ⟨hza, hze⟩ := acyclic_groups X G (n + 1) (hacyc (n + 1) (by omega))
  exact ⟨G, Q, hG, hQ, i, cokernel.π i, cokernel.condition i,
    hS, ha, hz, he, hza, hze⟩

end
end AlgebraicGeometry.Scheme.Modules.CoherentEtale
