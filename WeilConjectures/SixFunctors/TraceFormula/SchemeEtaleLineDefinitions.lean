/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.Sites.Ga
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Étale comparison for invertible modules

Source: Stacks Project, Descent, Tags 03DX (2), 05VG and 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison).

The auxiliary definitions give the structure ring, the two full subcategories, and
postcomposition on the small étale site. The theorem specifies the comparison by its
canonical additive section sheaf, scalar action, and map on every module morphism.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The underlying structure-ring presheaf is a sheaf, without a universe-small
sheafification assumption. Source: Stacks Project, Descent, Tag 03DR
(blueprint: lem-trf-scheme-etale-invertible-comparison).

Proof: the structure presheaf is already a sheaf of commutative rings by étale descent.
A matching family of ring maps glues on every element by the set-valued sheaf axiom;
separatedness checks that the glued function preserves addition, multiplication, zero
and one. The resulting ring map is the unique amalgamation. -/
theorem trfEtaleStructureRing_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})  := by
  let P := X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}
  have h := X.isSheaf_etaleStructurePresheaf_comp_forget
  intro E V S hS x hx
  have hQ := h S hS
  let y (e : E) : Presieve.FamilyOfElements (P ⋙ CategoryTheory.forget RingCat) S :=
    fun W f hf ↦ (x f hf).hom e
  have hy (e : E) : (y e).Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    exact congrArg (fun φ : E ⟶ P.obj (op Z) ↦ φ.hom e) (hx g₁ g₂ h₁ h₂ fac)
  let g (e : E) : P.obj (op V) := hQ.amalgamate (y e) (hy e)
  have hg (e : E) {W : X.Etale} (f : W ⟶ V) (hf : S f) :
      P.map f.op (g e) = (x f hf).hom e := hQ.valid_glue (hy e) f hf
  have hext {a b : P.obj (op V)}
      (hab : ∀ {W : X.Etale} (f : W ⟶ V), S f → P.map f.op a = P.map f.op b) :
      a = b := hQ.isSeparatedFor.ext fun _ f hf ↦ hab f hf
  let φ : E ⟶ P.obj (op V) := RingCat.ofHom
    { toFun := g
      map_one' := hext fun f hf ↦ by rw [hg _ f hf, map_one, map_one]
      map_mul' := fun a b ↦ hext fun f hf ↦ by
        rw [map_mul, hg _ f hf, hg _ f hf, hg _ f hf, map_mul]
      map_zero' := hext fun f hf ↦ by rw [hg _ f hf, map_zero, map_zero]
      map_add' := fun a b ↦ hext fun f hf ↦ by
        rw [map_add, hg _ f hf, hg _ f hf, hg _ f hf, map_add] }
  refine ⟨φ, fun W f hf ↦ ?_, fun ψ hψ ↦ ?_⟩
  · change φ ≫ P.map f.op = x f hf
    ext e
    exact hg e f hf
  · refine RingCat.hom_ext (RingHom.ext fun e ↦ ?_)
    refine hext fun f hf ↦ ?_
    exact (congrArg (fun χ : E ⟶ P.obj (op _) ↦ χ.hom e) (hψ f hf)).trans
      (hg e f hf).symm

/-- The structure ring on the small étale site, evaluated as `Γ(U, 𝒪_U)`.
Source: Stacks Project, Descent, Tag 03DR
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfEtaleStructureRing (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology RingCat.{u} :=
  ⟨X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    trfEtaleStructureRing_isSheaf X⟩

/-- Ordinary invertible modules with all module morphisms.
Source: Stacks Project, Descent, Tag 03DX (2), specialized using Tag 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
abbrev TrfInvertibleModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun L : X.Modules ↦ L.IsInvertible)

/-- A line module is trivial on the localized sites of a jointly surjective étale
family. `CoversTop` expresses precisely this covering condition, with no finiteness
or nonemptiness restriction. Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def TrfIsEtaleLine {X : Scheme.{u}}
    (M : ringedSiteModules.{u} (trfEtaleStructureRing X)) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
    ∀ i, Nonempty (M.over (U i) ≅ SheafOfModules.unit ((trfEtaleStructureRing X).over (U i)))

/-- Étale line modules with all module morphisms, as a full subcategory.
Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
abbrev TrfEtaleLineModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (@TrfIsEtaleLine X)

/-- The canonical additive section sheaf of an ordinary invertible module.
This uses exactly the recorded associated-sheaf declaration, with its existing
quasi-coherence instance. Source: Stacks Project, Descent, Tag 03DU
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfInvertibleSections {X : Scheme.{u}} (L : TrfInvertibleModules X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  @Modules.etaleTensorSectionsSheaf _ L.obj
    (@Modules.IsInvertible.isQuasicoherent _ L.obj L.property)

/-- Restriction of an étale site along `v` evaluates at `w` by `w ≫ v`.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleCompose {Y X : Scheme.{u}} (v : Y ⟶ X) [Etale v] : Y.Etale ⥤ X.Etale where
  obj W := Scheme.Etale.mk (W.hom ≫ v)
  map {U V} g := MorphismProperty.Over.homMk g.left
    (by simp [← Category.assoc, MorphismProperty.Over.w g])

/-- Identity comparison on tensor pullback, normalized by the recorded adjunction unit.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfTensorId (X : Scheme.{u}) : Modules.tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  Adjunction.leftAdjointIdIso (Classical.choose (Modules.exists_tensorPullbackAdjunction (𝟙 X)))
    (Modules.pushforwardId X)

/-- Identity postcomposition changes only the structure arrow of a site object.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleIdArrow {X : Scheme.{u}} (W : X.Etale) :
    W ⟶ (trfEtaleCompose (𝟙 X)).obj W :=
  MorphismProperty.Over.homMk (𝟙 W.left) (by simp [trfEtaleCompose])

/-- Associativity identifies successive and composite postcomposition of site objects.
Source: Stacks Project, Descent, Tag 03LC (1)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfEtaleCompArrow {X Y Z : Scheme.{u}} (v : Y ⟶ X) (w : Z ⟶ Y) [Etale v] [Etale w]
    (W : Z.Etale) : (trfEtaleCompose (w ≫ v)).obj W ⟶
      (trfEtaleCompose v).obj ((trfEtaleCompose w).obj W) :=
  MorphismProperty.Over.homMk (𝟙 W.left)
    (by change (𝟙 W.left) ≫ ((W.hom ≫ w) ≫ v) = W.hom ≫ (w ≫ v)
        simp only [Category.id_comp, Category.assoc])

/-- The ordinary structure module, as an object of the invertible full subcategory.
Source: Stacks Project, Descent, Tags 03DX (2), 05VG
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfStructureInvertible (X : Scheme.{u}) : TrfInvertibleModules X :=
  ⟨SheafOfModules.unit X.ringCatSheaf, Modules.isInvertible_tensorUnit⟩

/-- Tensor pullback of the structure module, normalized by the canonical adjunction.
This is the unique comparison to Mathlib's pullback followed by its structure-unit map.
Source: Stacks Project, Descent, Tag 03LC (1); Sheaves, Tag 0096
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfTensorUnit {Y X : Scheme.{u}} (v : Y ⟶ X) :
    (Modules.tensorPullback v).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  ((Classical.choose (Modules.exists_tensorPullbackAdjunction v)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction v)).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      Modules.pullbackObjUnitIso v

/-- The underlying additive sheaf of a line module.
Source: Stacks Project, Modules on Sites, sheaves of modules; Descent, Tag 03DX
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
noncomputable def trfLineSections {X : Scheme.{u}} (M : TrfEtaleLineModules X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf _).obj M.obj

/-- The underlying module map of the comparison on any ordinary module morphism.
The full subcategory retains all morphisms, including zero and noninvertible maps.
Source: Stacks Project, Descent, Tag 03DX (2)
(blueprint: lem-trf-scheme-etale-invertible-comparison). -/
def trfComparisonMap {X : Scheme.{u}}
    (A : TrfInvertibleModules X ⥤ TrfEtaleLineModules X)
    {L K : TrfInvertibleModules X} (h : L.obj ⟶ K.obj) :
    (A.obj L).obj ⟶ (A.obj K).obj :=
  (A.map (ObjectProperty.homMk h)).hom

end AlgebraicGeometry.Scheme
