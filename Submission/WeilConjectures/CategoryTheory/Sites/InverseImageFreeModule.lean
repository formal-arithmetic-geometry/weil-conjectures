/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction

import Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Submission.WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Geometric inverse image of free module sheaves

Source: Stacks Project, Modules on Sites, Tags 04BL, 03CY, 03D3 and 08TQ
(auxiliary; not a blueprint node).

The free module is module sheafification of the sectionwise free module, on an arbitrary
sheaf of generators. Algebraic inverse-image presentations record precisely the transported
operations. Underlying modules use the common value universe of that recorded interface.
-/

@[expose] public section

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : K.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : K.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

private def rawLift (B : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (ring B)) :
    (underlyingRaw B).obj M ≅ (moduleSets B).obj M where
  hom := ⟨{ app := fun _ ↦ ↾ULift.up, naturality := by intros; rfl }⟩
  inv := ⟨{ app := fun _ ↦ ↾ULift.down, naturality := by intros; rfl }⟩

private theorem rawLift_naturality (B : Sheaf J CommRingCat.{w})
    {M N : SheafOfModules.{w} (ring B)} (a : M ⟶ N) :
    (underlyingRaw B).map a ≫ (rawLift B N).hom =
      (rawLift B M).hom ≫ (moduleSets B).map a := rfl

private theorem generator_lift (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    generatorRaw B E ≫ (rawLift B ((free B).obj E)).hom = generator B E := rfl

private theorem generator_naturality (B : Sheaf J CommRingCat.{w})
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    generator B E ≫ (moduleSets B).map ((free B).map e) = e ≫ generator B E' := by
  have h := (freeModule_restrict_naturality B E E' e
    ((free B).obj E') ((free B).obj E')).1 (𝟙 _)
  have hh := congrArg (fun a ↦ a ≫ (rawLift B ((free B).obj E')).hom) h
  simp only [restrictGenerators, Functor.map_id, Category.comp_id, Category.assoc,
    rawLift_naturality, generator_lift] at hh
  rw [← Category.assoc, generator_lift] at hh
  exact hh

private def identityUnderlying
    (B : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uC, vC, w, w}
      (𝟭 (Sheaf J (Type w))) B B)
    (hB : F.ringUnderlying = Iso.refl ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B))
    (M : SheafOfModules.{w} (ring B)) : M ⟶ F.modules.obj M := by
  let α := F.moduleUnderlying.inv.app M
  refine { val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (α.hom.app U (ULift.up x)).down
          map_add' := ?_
          map_smul' := ?_ }
      naturality := ?_ } }
  · intro x y
    let T := (underlyingRaw B).obj M ⊗ (underlyingRaw B).obj M
    let a : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.1, naturality := by intros; rfl }⟩
    let b : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.2, naturality := by intros; rfl }⟩
    let t : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun V ↦ ↾fun z ↦ ULift.up
           (@id (M.val.obj V) z.1 + @id (M.val.obj V) z.2)
         naturality := by
           intro U V i
           ext z
           exact congrArg ULift.up ((M.val.map i).hom.map_add _ _).symm }⟩
    exact F.moduleAdd M T a b t (fun _ _ ↦ rfl) U (x, y)
  · intro a x
    let R := (sheafCompose J (forget CommRingCat.{w})).obj B
    let T := R ⊗ (underlyingRaw B).obj M
    let r : T ⟶ (sheafCompose J
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.1, naturality := by intros; rfl }⟩
    let b : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.2, naturality := by intros; rfl }⟩
    let t : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun V ↦ ↾fun z ↦ ULift.up
           (@id (B.obj.obj V) z.1 • @id (M.val.obj V) z.2)
         naturality := by
           intro U V i
           ext z
           exact congrArg ULift.up ((M.val.map i).hom.map_smulₛₗ _ _).symm }⟩
    simpa [α, t, r, b, hB] using F.moduleSMul M T r b t (fun _ _ ↦ rfl) U (a, x)
  · intro U V i
    ext x
    exact congrArg ULift.down (congrArg (fun a ↦ a (ULift.up x))
      (α.hom.naturality i))

private theorem transportedFreeProperty
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w)) :
    HasTransportedFreeUniversalProperty f.inverse F E := by
  obtain ⟨P, eP, hAdd, hSmul, A, G, hA, hG, hChain, hAL, hAR, hGL, hGR,
    hBij, hEL, hER⟩ := geometricFreeModule_hom_chain f F
  exact hBij E

/-- The underlying comparison with the canonical inverse-image identification retained.
Source: Stacks 08TQ (auxiliary; not a blueprint node). -/
noncomputable def comparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) :
    f.inverse.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (f.inverse.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom

/-- Generator normalization of the comparison, an equality of sheaf maps and hence
valid on all generalized sections. Source: Stacks 08TQ
(auxiliary; not a blueprint node). -/
def IsComparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) : Prop :=
  f.inverse.map (generator B E) ≫ comparison f F E p = generator BI (f.inverse.obj E)

/-- Inverse image preserves the free module sheaf on any sheaf of sets, with its uniquely
normalized isomorphism. Source: Stacks 04BL, 03CY, 03D3 and 08TQ
(auxiliary; not a blueprint node).

Proof: first extend a map E → |M| sectionwise by summing coefficients times the images
of generators. The free presheaf universal property and module sheafification give
Hom_B(B[E], M) ≃ Hom(E, |M|). The geometric module transport adjunction of 03D3,
with coefficient map the identity on the transported ring, then gives
Hom_BI(F(B[E]), H) ≃ Hom_B(B[E], f_* H) ≃ Hom(E, f_* |H|) ≃ Hom(f⁻¹ E, |H|).
The transport normalization identifies this bijection with restriction to f⁻¹ of the
generator map. Thus source and target are free on f⁻¹ E with those generator maps.
Extend each generator map into the other free module. Their composites fix generators,
so freeness makes them identities. This gives the isomorphism; the same uniqueness
makes it the only generator-normalized isomorphism. -/
theorem inverseFreeModule_existsUnique
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w)) :
    ∃! p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E),
      IsComparison f F E p := by
  let P := F.modules.obj ((free B).obj E)
  let k := f.inverse.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E)
  let kRaw := k ≫ (rawLift BI P).inv
  have hP : ∀ M : SheafOfModules.{w} (ring BI),
      Function.Bijective (fun h : P ⟶ M ↦ kRaw ≫ (underlyingRaw BI).map h) := by
    intro M
    have h := transportedFreeProperty f F E M
    have eqn (a : P ⟶ M) :
        kRaw ≫ (underlyingRaw BI).map a =
          inverseFreeRestriction f F E M a ≫ (rawLift BI M).inv := by
      ext V x
      rfl
    simp_rw [eqn]
    exact ((rawLift BI M).symm.homToEquiv).bijective.comp h
  obtain ⟨p, hp, hu⟩ := freeModule_unique_iso BI (f.inverse.obj E) P kRaw hP
  have normalize (q : P ≅ (free BI).obj (f.inverse.obj E)) :
      (kRaw ≫ (underlyingRaw BI).map q.hom = generatorRaw BI (f.inverse.obj E)) ↔
        IsComparison f F E q := by
    rw [← cancel_mono (rawLift BI ((free BI).obj (f.inverse.obj E))).hom]
    simp only [Category.assoc, rawLift_naturality, generator_lift]
    simp only [kRaw, k, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  refine ⟨p, (normalize p).mp hp.1, ?_⟩
  intro q hq
  apply Iso.ext
  have hqp := (hP ((free BI).obj (f.inverse.obj E))).1
  exact hqp (((normalize q).mpr hq).trans hp.1.symm)


variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

local instance : T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance


end CategoryTheory.SheafFreeModule
