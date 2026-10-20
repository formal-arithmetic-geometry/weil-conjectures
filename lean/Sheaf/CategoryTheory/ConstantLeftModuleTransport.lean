/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Exact inverse image for constant left-module sheaves

Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), its fixed-ring
scalar-endomorphism proof, and Section 00XZ; Derived Categories, Tag 015F
(blueprint: lem-pe-constant-left-module-inverse-image).

The lift is characterized by its underlying-set comparison, addition and scalar
endomorphisms, and the original geometric adjunction unit. Comparisons have a
normalization equation and uniqueness; arbitrary unrelated functors are never compared.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace ConstantLeftModuleInverseImage

/-- Constant-coefficient module sheaves, using the recorded general-site category.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :=
  ringedSiteModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget constant scalars, retaining the abelian sheaf.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev V {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Forget the abelian group structure.
Source: Stacks, 00YV (2) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev U {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
  sheafCompose J (forget AddCommGrpCat.{u})

/-- The underlying-set functor on constant-coefficient modules.
Source: Stacks, 00YV (6) (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev W {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] :
    Modules J Λ ⥤ Sheaf J (Type u) := V J Λ ⋙ U J

/-- Characterization of a sheaf's addition map by its values on sections.
The projections allow arbitrary choices of categorical products.
Source: Stacks, discussion preceding 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsAddition {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A) : Prop :=
  ∀ (T : Cᵒᵖ) (x : ((U J).obj A ⨯ (U J).obj A).obj.obj T),
    a.hom.app T x =
      @id (A.obj.obj T)
        ((prod.fst : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x) +
      @id (A.obj.obj T)
        ((prod.snd : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A).hom.app T x)

/-- A constant scalar endomorphism of the underlying abelian sheaf. This is
not required to be a module morphism when the ring is noncommutative.
Source: Stacks, fixed-ring paragraph in the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsScalar {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) (a : (V J Λ).obj M ⟶ (V J Λ).obj M) : Prop :=
  ∀ (T : Cᵒᵖ) (x : M.val.obj T),
    a.hom.app T x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x

/-- The underlying set sheaf of the sheafified constant ring `Λ_C`.
Source: Stacks, 00YV (2) and 0H7J (blueprint: lem-pe-constant-left-module-inverse-image). -/
abbrev CoeffSet {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}] : Sheaf J (Type u) :=
  (sheafCompose J (forget RingCat.{u})).obj ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))

/-- Characterization of the addition map of the constant ring sheaf by its values
on sections. Source: Stacks, ring paragraph of the proof of 00YV
(blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingAdd {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) +
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

/-- Characterization of the multiplication map of the constant ring sheaf by its
values on sections, in the given order (no commutativity). Source: Stacks, ring
paragraph of the proof of 00YV (blueprint: lem-pe-constant-left-module-inverse-image). -/
def IsRingMul {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) *
      @id (((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-- A normalized lift of the given geometric morphism. The set comparisons and
unit equations connect both adjunctions to `L ⊣ R`; addition and scalar equations
specify the transported operations. Zero and negation are determined by addition.
The ring comparison is normalized on every scalar summand of the constant sheaf
(these summands determine it uniquely) and carries the addition and multiplication
transported by `L` to those of the target constant ring.
Source: Stacks, 00YV (2), (5), (6), 0H7J, and the node's proof steps 1--6
(blueprint: lem-pe-constant-left-module-inverse-image). -/
structure ConstantLeftModuleInverseImageLift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) where
  /-- The comparison `f⁻¹|Λ_C| ≅ |Λ_D|`, written on `L` of the constant set sheaf. -/
  ringUnderlying :
    L.obj ((constantSheaf J (Type u)).obj Λ) ≅
      (sheafCompose K (forget RingCat.{u})).obj
        ((constantSheaf K RingCat.{u}).obj (RingCat.of Λ))
  /-- The comparison carries the addition `L(+) ∘ p⁻¹` transported by `L` to the
  addition of `Λ_D`. -/
  ring_add : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingAdd J Λ m → IsRingAdd K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  /-- The comparison carries the multiplication `L(μ) ∘ p⁻¹` transported by `L`
  to the multiplication of `Λ_D`. With `ring_add`, the bijectivity of the
  comparison and `constant_scalar` at `0` and `1`, it is a ring-sheaf isomorphism
  from the transported ring structure on `f⁻¹Λ_C` to `Λ_D`. -/
  ring_mul : ∀ (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ),
    IsRingMul J Λ m → IsRingMul K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
          L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          ringUnderlying.hom =
        prod.map
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom)
          (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
            ringUnderlying.hom) ≫ m'
  pointIso : L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
    (constantSheaf K (Type u)).obj PUnit.{u+1}
  constant_scalar : ∀ r : Λ,
    L.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ ringUnderlying.hom ≫
      (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      pointIso.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))
  moduleFunctor : Modules J Λ ⥤ Modules K Λ
  moduleDirect : Modules K Λ ⥤ Modules J Λ
  moduleAdj : moduleFunctor ⊣ moduleDirect
  additive : moduleFunctor.Additive
  preservesFiniteLimits : PreservesFiniteLimits moduleFunctor
  preservesFiniteColimits : PreservesFiniteColimits moduleFunctor
  abelianInverse : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}
  abelianDirect : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}
  abelianAdj : abelianInverse ⊣ abelianDirect
  abelianSetIso : abelianInverse ⋙ U K ≅ U J ⋙ L
  abelianDirectSetIso : abelianDirect ⋙ U J ≅ U K ⋙ R
  abelian_addition : ∀ (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A)
    (b : (U K).obj (abelianInverse.obj A) ⨯ (U K).obj (abelianInverse.obj A) ⟶
      (U K).obj (abelianInverse.obj A)),
    IsAddition J A a → IsAddition K (abelianInverse.obj A) b →
      b ≫ abelianSetIso.hom.app A =
        prod.map (abelianSetIso.hom.app A) (abelianSetIso.hom.app A) ≫
          inv (prodComparison L ((U J).obj A) ((U J).obj A)) ≫ L.map a
  abelian_unit : ∀ A : Sheaf J AddCommGrpCat.{u},
    (U J).map (abelianAdj.unit.app A) ≫
      abelianDirectSetIso.hom.app (abelianInverse.obj A) ≫
      R.map (abelianSetIso.hom.app A) = adj.unit.app ((U J).obj A)
  underlyingIso : moduleFunctor ⋙ V K Λ ≅ V J Λ ⋙ abelianInverse
  directUnderlyingIso : moduleDirect ⋙ V J Λ ≅ V K Λ ⋙ abelianDirect
  moduleSetIso : moduleFunctor ⋙ W K Λ ≅ W J Λ ⋙ L
  moduleSetIso_compatibility : ∀ M : Modules J Λ,
    (U K).map (underlyingIso.hom.app M) ≫ abelianSetIso.hom.app ((V J Λ).obj M) =
      moduleSetIso.hom.app M
  scalar_compatibility : ∀ (M : Modules J Λ) (r : Λ)
    (a : (V J Λ).obj M ⟶ (V J Λ).obj M)
    (b : (V K Λ).obj (moduleFunctor.obj M) ⟶ (V K Λ).obj (moduleFunctor.obj M)),
    IsScalar J Λ M r a → IsScalar K Λ (moduleFunctor.obj M) r b →
      b ≫ underlyingIso.hom.app M = underlyingIso.hom.app M ≫ abelianInverse.map a
  unit_compatibility : ∀ M : Modules J Λ,
    (V J Λ).map (moduleAdj.unit.app M) ≫
      directUnderlyingIso.hom.app (moduleFunctor.obj M) ≫
      abelianDirect.map (underlyingIso.hom.app M) = abelianAdj.unit.app ((V J Λ).obj M)

/-! The coefficient comparison is natural in the constant type. Binary operations
are compared after the isomorphism from the constant sheaf on pairs. -/
section CoefficientConstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
variable (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]
private def pointTerminal : IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u+1}) := by
  exact (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _
private def pointComparison :
    L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u+1} :=
  ((pointTerminal J).isTerminalObj L _).uniqueUpToIso (pointTerminal K)
private def globalComparison : R ⋙ Sheaf.Γ J (Type u) ≅ Sheaf.Γ K (Type u) := by
  exact Functor.isoWhiskerLeft R (Sheaf.ΓNatIsoCoyoneda J PUnit.{u+1}) ≪≫
    (adj.compCoyonedaIso.app (op ((constantSheaf J (Type u)).obj PUnit.{u+1}))).symm ≪≫
    coyoneda.mapIso (pointComparison J K L).symm.op ≪≫
    (Sheaf.ΓNatIsoCoyoneda K PUnit.{u+1}).symm
private def constantComparison :
    constantSheaf J (Type u) ⋙ L ≅ constantSheaf K (Type u) :=
  (((constantSheafΓAdj J (Type u)).comp adj).ofNatIsoRight
    (globalComparison J K L R adj)).leftAdjointUniq (constantSheafΓAdj K (Type u))

@[reassoc] private theorem constantComparison_naturality (X Y : Type u) (f : X ⟶ Y) :
    L.map ((constantSheaf J (Type u)).map f) ≫
        (constantComparison J K L R adj).hom.app Y =
      (constantComparison J K L R adj).hom.app X ≫ (constantSheaf K (Type u)).map f :=
  (constantComparison J K L R adj).hom.naturality f

variable (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]

private def normalizedRingComparison :
    L.obj ((constantSheaf J (Type u)).obj Λ) ≅
      ConstantLeftModuleInverseImage.CoeffSet K Λ :=
  (constantComparison J K L R adj).app Λ ≪≫
    ((constantCommuteCompose K (forget RingCat.{u})).app (RingCat.of Λ)).symm

omit [HasWeakSheafify J RingCat.{u}] in
private theorem normalizedRingComparison_scalar (r : Λ) :
    L.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫
        (normalizedRingComparison J K L R adj Λ).hom ≫
          (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      ((constantComparison J K L R adj).app PUnit.{u+1}).hom ≫
        (constantSheaf K (Type u)).map
          (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)) := by
  dsimp only [normalizedRingComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact constantComparison_naturality J K L R adj PUnit.{u+1} Λ
    (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))

private theorem coeff_unit (T : Cᵒᵖ) (r : Λ) :
    ((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r) =
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) := by
  have h := sheafComposeIso_hom_fac J (forget RingCat.{u})
    ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (RingCat.of Λ) (forget RingCat.{u})).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ (RingCat.of Λ) (forget RingCat.{u})).inv) ≫
    (sheafifyComposeIso J (forget RingCat.{u})
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).hom).app T) r = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

omit [HasWeakSheafify J RingCat.{u}] in
private theorem constantMap_unit (X Y : Type u) (f : X → Y) (T : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app T x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app T (f x) := by
  exact (congrArg (fun g ↦ g.app T x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

open ConstantLeftModuleInverseImage
private theorem ringAddition_constants
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) (hm : IsRingAdd J Λ m) :
    prod.lift
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)) ≫ m =
      (constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 + p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ) := by
  let q : (constantSheaf J (Type u)).obj (Λ × Λ) ⟶
      CoeffSet J Λ ⨯ CoeffSet J Λ :=
    prod.lift
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
  change q ≫ m = _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (CoeffSet J Λ).property
  ext T r
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  change m.hom.app T _ = _
  rw [hm]
  have hfst : (prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.fst = _ from prod.lift_fst _ _)
  have hsnd : (prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.snd = _ from prod.lift_snd _ _)
  erw [hfst, hsnd]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, constantMap_unit, id_eq]
  change (show ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.1))) +
    (show ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.2))) =
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      (((constantSheaf J (Type u)).map
        (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 + p.2))).hom.app T
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)))
  rw [constantMap_unit, coeff_unit, coeff_unit, coeff_unit]
  exact (map_add (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T).hom) r.1 r.2).symm

private theorem ringMultiplication_constants
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) (hm : IsRingMul J Λ m) :
    prod.lift
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)) ≫ m =
      (constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 * p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ) := by
  let q : (constantSheaf J (Type u)).obj (Λ × Λ) ⟶
      CoeffSet J Λ ⨯ CoeffSet J Λ :=
    prod.lift
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
      ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
  change q ≫ m = _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (CoeffSet J Λ).property
  ext T r
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  change m.hom.app T _ = _
  rw [hm]
  have hfst : (prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.fst = _ from prod.lift_fst _ _)
  have hsnd : (prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.snd = _ from prod.lift_snd _ _)
  erw [hfst, hsnd]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, constantMap_unit, id_eq]
  change (show ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.1))) *
    (show ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.2))) =
    (((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)).hom.app T
      (((constantSheaf J (Type u)).map
        (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 * p.2))).hom.app T
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)))
  rw [constantMap_unit, coeff_unit, coeff_unit, coeff_unit]
  exact (map_mul (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T).hom) r.1 r.2).symm


private def coeffPair : (constantSheaf J (Type u)).obj (Λ × Λ) ⟶
    CoeffSet J Λ ⨯ CoeffSet J Λ :=
  prod.lift
    ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
      (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
    ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
      (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))

private instance coeffPair_isIso : IsIso (coeffPair J Λ) := by
  have h : coeffPair J Λ =
      (constantSheaf J (Type u)).map (Types.binaryProductIso Λ Λ).inv ≫
      prodComparison (constantSheaf J (Type u)) Λ Λ ≫
      prod.map ((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
        ((constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ)) := by
    apply prod.hom_ext
    · dsimp only [coeffPair]
      simp only [Category.assoc, prod.lift_fst]
      erw [prod.map_fst, prodComparison_fst_assoc, ← Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_fst]
    · dsimp only [coeffPair]
      simp only [Category.assoc, prod.lift_snd]
      erw [prod.map_snd, prodComparison_snd_assoc, ← Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_snd]
  rw [h]
  have : PreservesFiniteLimits (constantSheaf J (Type u)) :=
    comp_preservesFiniteLimits _ _
  infer_instance

private theorem coeffPair_naturality :
    L.map (coeffPair J Λ) ≫ prodComparison L (CoeffSet J Λ) (CoeffSet J Λ) ≫
      prod.map
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom)
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom) =
      (constantComparison J K L R adj).hom.app (Λ × Λ) ≫ coeffPair K Λ := by
  apply prod.hom_ext
  all_goals
    simp only [Category.assoc, prod.map_fst, prod.map_snd, prod.map_fst_assoc,
      prod.map_snd_assoc, prod.lift_fst,
      prod.lift_snd, prodComparison_fst_assoc, prodComparison_snd_assoc,
      ← Functor.map_comp_assoc]
    dsimp only [coeffPair, normalizedRingComparison, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom]
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd, prod.lift_fst_assoc,
      prod.lift_snd_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    erw [Category.comp_id]
    rw [constantComparison_naturality_assoc]
    rfl

private theorem ringOperation_transport
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ)
    (f : Λ × Λ → Λ)
    (hm : coeffPair J Λ ≫ m = (constantSheaf J (Type u)).map (TypeCat.ofHom f) ≫
      (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of Λ))
    (hm' : coeffPair K Λ ≫ m' = (constantSheaf K (Type u)).map (TypeCat.ofHom f) ≫
      (constantCommuteCompose K (forget RingCat.{u})).inv.app (RingCat.of Λ)) :
    inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
        L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
        (normalizedRingComparison J K L R adj Λ).hom =
      prod.map
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom)
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom) ≫ m' := by
  apply (cancel_epi
    (L.map (coeffPair J Λ) ≫ prodComparison L (CoeffSet J Λ) (CoeffSet J Λ))).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have h := congrArg (fun g ↦ g ≫ m') (coeffPair_naturality J K L R adj Λ)
  simp only [Category.assoc] at h
  rw [h]
  rw [hm']
  rw [← L.map_comp_assoc, hm]
  dsimp only [normalizedRingComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]
  rw [constantComparison_naturality_assoc]
  rfl

end CoefficientConstruction

/-! Lift left exact functors to abelian sheaves sectionwise, transport the constant
scalar endomorphisms, and extend them along ring sheafification. -/
section TransportConstruction
set_option linter.unusedSimpArgs false
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

private def abNatTrans
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact (H.preimage (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G)
    (ObjectProperty.homMk α)).hom

private theorem abNatTrans_forget
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (abNatTrans F G α) (forget AddCommGrpCat) = α := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact congrArg (fun f ↦ f.hom) (H.map_preimage
    (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G) (ObjectProperty.homMk α))

variable {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
  {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  (F : A ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]

private def sectionAb (T : Dᵒᵖ) : A ⥤ AddCommGrpCat.{u} :=
  ((AddCommGrpCat.leftExactFunctorForgetEquivalence A).inverse.obj
    (LeftExactFunctor.of (F ⋙ sheafToPresheaf K (Type u) ⋙
      (evaluation Dᵒᵖ (Type u)).obj T))).obj

private instance (T : Dᵒᵖ) : PreservesFiniteLimits (sectionAb K F T) :=
  ((AddCommGrpCat.leftExactFunctorForgetEquivalence A).inverse.obj
    (LeftExactFunctor.of (F ⋙ sheafToPresheaf K (Type u) ⋙
      (evaluation Dᵒᵖ (Type u)).obj T))).property

private def sectionRestriction {T S : Dᵒᵖ} (f : T ⟶ S) :
    sectionAb K F T ⟶ sectionAb K F S :=
  abNatTrans _ _
    { app := fun M ↦ (F.obj M).obj.map f
      naturality := by
        intro M N g
        exact ((F.map g).hom.naturality f).symm }

private theorem sectionRestriction_forget {T S : Dᵒᵖ} (f : T ⟶ S) (M : A) :
    (forget AddCommGrpCat).map ((sectionRestriction K F f).app M) =
      (F.obj M).obj.map f :=
  congr_app (abNatTrans_forget (sectionAb K F T) (sectionAb K F S)
    { app := fun M ↦ (F.obj M).obj.map f
      naturality := by
        intro N P g
        exact ((F.map g).hom.naturality f).symm }) M

private def abSheafLift : A ⥤ Sheaf K AddCommGrpCat.{u} where
  obj M :=
    ⟨{ obj := fun T ↦ (sectionAb K F T).obj M
       map := fun f ↦ (sectionRestriction K F f).app M
       map_id := by
         intro T
         apply (forget AddCommGrpCat).map_injective
         rw [sectionRestriction_forget]
         exact (F.obj M).obj.map_id T
       map_comp := by
         intro T S V f g
         apply (forget AddCommGrpCat).map_injective
         change (forget AddCommGrpCat).map
             ((sectionRestriction K F (f ≫ g)).app M) =
           (forget AddCommGrpCat).map ((sectionRestriction K F f).app M) ≫
             (forget AddCommGrpCat).map ((sectionRestriction K F g).app M)
         rw [sectionRestriction_forget, sectionRestriction_forget, sectionRestriction_forget]
         exact (F.obj M).obj.map_comp f g },
      by
        apply Presheaf.isSheaf_of_isSheaf_comp K _ (forget AddCommGrpCat)
        convert (F.obj M).property using 1
        apply Functor.ext
        · intro T S f
          simpa using sectionRestriction_forget K F f M
        · intro T
          rfl⟩
  map g :=
    { hom :=
      { app := fun T ↦ (sectionAb K F T).map g
        naturality := by
          intro T S f
          exact ((sectionRestriction K F f).naturality g).symm } }
  map_id := by
    intro M
    ext T x
    exact congrArg (fun k ↦ k.hom x) ((sectionAb K F T).map_id M)
  map_comp := by
    intro M N P f g
    ext T x
    exact congrArg (fun k ↦ k.hom x) ((sectionAb K F T).map_comp f g)


private theorem sectionAb_map_forget (M N : A) (g : M ⟶ N) (T : Dᵒᵖ) :
    (forget AddCommGrpCat).map ((sectionAb K F T).map g) = (F.map g).hom.app T := rfl

private def abSheafLiftSetIso : abSheafLift K F ⋙ U K ≅ F :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨{ app := fun T ↦ 𝟙 _
                naturality := by
                  intro T S f
                  change (forget AddCommGrpCat).map ((sectionRestriction K F f).app M) ≫
                    𝟙 _ = 𝟙 _ ≫ (F.obj M).obj.map f
                  simpa only [Category.comp_id, Category.id_comp] using
                    sectionRestriction_forget K F f M }⟩
      inv := ⟨{ app := fun T ↦ 𝟙 _
                naturality := by
                  intro T S f
                  change (F.obj M).obj.map f ≫ 𝟙 _ =
                    𝟙 _ ≫ (forget AddCommGrpCat).map ((sectionRestriction K F f).app M)
                  simpa only [Category.comp_id, Category.id_comp] using
                    (sectionRestriction_forget K F f M).symm }⟩
      hom_inv_id := by ext T x; rfl
      inv_hom_id := by ext T x; rfl })
    (fun g ↦ by ext T x; rfl)

private instance abSheafLiftLimits : PreservesFiniteLimits (abSheafLift K F) where
  preservesFiniteLimits I _ _ := by
    have : PreservesLimitsOfShape I (abSheafLift K F ⋙ U K) :=
      preservesLimitsOfShape_of_natIso (abSheafLiftSetIso K F).symm
    have : PreservesFiniteLimits (U K ⋙ sheafToPresheaf K (Type u)) := by
      change PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight Dᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u}))
      infer_instance
    have : PreservesFiniteLimits (U K) :=
      preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf K (Type u))
    have : ReflectsLimitsOfShape I (U K) := reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact preservesLimitsOfShape_of_reflects_of_preserves (abSheafLift K F) (U K)


private def liftSheafNatTrans
    (P Q : A ⥤ Sheaf K AddCommGrpCat.{u})
    [PreservesFiniteLimits P] [PreservesFiniteLimits Q]
    (α : P ⋙ U K ⟶ Q ⋙ U K) : P ⟶ Q := by
  let b (T : Dᵒᵖ) := abNatTrans
    (P ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    (Q ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    { app := fun N ↦ (α.app N).hom.app T
      naturality := by
        intro M N f
        exact congrArg (fun k ↦ k.hom.app T) (α.naturality f) }
  have hb (T : Dᵒᵖ) (M : A) :
      (forget AddCommGrpCat).map ((b T).app M) = (α.app M).hom.app T := by
    dsimp only [b]
    exact congr_app (abNatTrans_forget _ _ _) M
  exact
    { app := fun M ↦
        { hom :=
            { app := fun T ↦ (b T).app M
              naturality := by
                intro T S f
                apply (forget AddCommGrpCat).map_injective
                change (forget AddCommGrpCat).map ((P.obj M).obj.map f) ≫
                    (forget AddCommGrpCat).map ((b S).app M) =
                  (forget AddCommGrpCat).map ((b T).app M) ≫
                    (forget AddCommGrpCat).map ((Q.obj M).obj.map f)
                rw [hb, hb]
                exact (α.app M).hom.naturality f } }
      naturality := by
        intro M N f
        ext T x
        exact congrArg (fun k ↦ k.hom x) ((b T).naturality f) }

private theorem liftSheafNatTrans_forget
    (P Q : A ⥤ Sheaf K AddCommGrpCat.{u})
    [PreservesFiniteLimits P] [PreservesFiniteLimits Q]
    (α : P ⋙ U K ⟶ Q ⋙ U K) :
    Functor.whiskerRight (liftSheafNatTrans K P Q α) (U K) = α := by
  ext M T x
  exact congrArg (fun k ↦ k x) (congr_app (abNatTrans_forget
    (P ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    (Q ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    { app := fun N ↦ (α.app N).hom.app T
      naturality := by
        intro N P f
        exact congrArg (fun k ↦ k.hom.app T) (α.naturality f) }) M)


section AbelianAdjunction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
private instance forgetAbLimits : PreservesFiniteLimits (U J) := by
  have : PreservesFiniteLimits (U J ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))

private instance abBiproducts : HasFiniteBiproducts (Sheaf J AddCommGrpCat.{u}) :=
  .of_hasFiniteProducts

variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  [PreservesFiniteLimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

private abbrev abInverse : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  abSheafLift K (U J ⋙ L)
private abbrev abDirect : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  abSheafLift J (U K ⋙ R)

private def abUnitSets : U J ⟶ abInverse K J L ⋙ abDirect K J R ⋙ U J :=
  (Functor.rightUnitor (U J)).inv ≫ Functor.whiskerLeft (U J) adj.unit ≫
    Functor.whiskerRight (abSheafLiftSetIso K (U J ⋙ L)).inv R ≫
      Functor.whiskerLeft (abInverse K J L) (abSheafLiftSetIso J (U K ⋙ R)).inv

private def abCounitSets : abDirect K J R ⋙ abInverse K J L ⋙ U K ⟶ U K :=
  Functor.whiskerLeft (abDirect K J R) (abSheafLiftSetIso K (U J ⋙ L)).hom ≫
    Functor.whiskerRight (abSheafLiftSetIso J (U K ⋙ R)).hom L ≫
      Functor.whiskerLeft (U K) adj.counit ≫ (Functor.rightUnitor (U K)).hom

private def abUnit : 𝟭 (Sheaf J AddCommGrpCat.{u}) ⟶
    abInverse K J L ⋙ abDirect K J R :=
  liftSheafNatTrans J _ _ (abUnitSets K J L R adj)

private def abCounit : abDirect K J R ⋙ abInverse K J L ⟶
    𝟭 (Sheaf K AddCommGrpCat.{u}) :=
  liftSheafNatTrans K _ _ (abCounitSets K J L R adj)

private theorem abUnit_forget (A : Sheaf J AddCommGrpCat.{u}) :
    (U J).map ((abUnit K J L R adj).app A) = (abUnitSets K J L R adj).app A :=
  congr_app (liftSheafNatTrans_forget J (𝟭 (Sheaf J AddCommGrpCat.{u}))
    (abInverse K J L ⋙ abDirect K J R) (abUnitSets K J L R adj)) A

private theorem abCounit_forget (A : Sheaf K AddCommGrpCat.{u}) :
    (U K).map ((abCounit K J L R adj).app A) = (abCounitSets K J L R adj).app A :=
  congr_app (liftSheafNatTrans_forget K (abDirect K J R ⋙ abInverse K J L)
    (𝟭 (Sheaf K AddCommGrpCat.{u})) (abCounitSets K J L R adj)) A

@[irreducible] private def abAdjunction : abInverse K J L ⊣ abDirect K J R where
  unit := abUnit K J L R adj
  counit := abCounit K J L R adj
  left_triangle_components A := by
    apply (U K).map_injective
    rw [Functor.map_comp, abCounit_forget, Functor.map_id]
    let eL := abSheafLiftSetIso K (U J ⋙ L)
    let eR := abSheafLiftSetIso J (U K ⋙ R)
    apply (cancel_mono (eL.hom.app A)).mp
    dsimp only [abCounitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app]
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      show (U K).map ((abInverse K J L).map ((abUnit K J L R adj).app A)) ≫
        (abSheafLiftSetIso K (U J ⋙ L)).hom.app
          ((abDirect K J R).obj ((abInverse K J L).obj A)) = _ from
        eL.hom.naturality ((abUnit K J L R adj).app A)]
    simp only [Category.assoc]
    simp only [Functor.comp_map]
    rw [abUnit_forget]
    dsimp only [abUnitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app]
    simp only [Functor.map_comp, Category.assoc, Functor.map_id, Category.id_comp]
    rw [← L.map_comp_assoc ((abSheafLiftSetIso J (U K ⋙ R)).inv.app _)
      ((abSheafLiftSetIso J (U K ⋙ R)).hom.app _), Iso.inv_hom_id_app,
      L.map_id, Category.id_comp]
    try simp only [Category.id_comp]
    erw [← Category.assoc (L.map (R.map ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)))
      (adj.counit.app _)]
    erw [show L.map (R.map ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)) ≫
        adj.counit.app ((U K).obj ((abInverse K J L).obj A)) =
      adj.counit.app (L.obj ((U J).obj A)) ≫
        (abSheafLiftSetIso K (U J ⋙ L)).inv.app A from
          adj.counit.naturality ((abSheafLiftSetIso K (U J ⋙ L)).inv.app A)]
    dsimp only [eL, Functor.id_obj]
    simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
    simp only [Category.assoc, adj.left_triangle_components_assoc,
      Category.comp_id, Iso.inv_hom_id_app_assoc]
    erw [Category.id_comp]
    rw [Iso.inv_hom_id_app, Category.comp_id]
  right_triangle_components A := by
    apply (U J).map_injective
    rw [Functor.map_comp, abUnit_forget, Functor.map_id]
    let eL := abSheafLiftSetIso K (U J ⋙ L)
    let eR := abSheafLiftSetIso J (U K ⋙ R)
    apply (cancel_mono (eR.hom.app A)).mp
    rw [Category.assoc, show (U J).map
      ((abDirect K J R).map ((abCounit K J L R adj).app A)) ≫ eR.hom.app A = _ from
        eR.hom.naturality ((abCounit K J L R adj).app A)]
    dsimp only [abUnitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.comp_map]
    simp only [Category.id_comp, Category.assoc]
    dsimp only [eR, Functor.comp_obj]
    rw [Iso.inv_hom_id_app_assoc]
    rw [abCounit_forget]
    dsimp only [abCounitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app]
    simp only [Functor.map_comp, Functor.map_id, Category.assoc, Category.comp_id]
    rw [← R.map_comp_assoc ((abSheafLiftSetIso K (U J ⋙ L)).inv.app _)
      ((abSheafLiftSetIso K (U J ⋙ L)).hom.app _), Iso.inv_hom_id_app,
      R.map_id, Category.id_comp]
    try simp only [R.map_id, Category.comp_id]
    erw [← Category.assoc, show adj.unit.app ((U J).obj ((abDirect K J R).obj A)) ≫
        R.map (L.map ((abSheafLiftSetIso J (U K ⋙ R)).hom.app A)) =
      (abSheafLiftSetIso J (U K ⋙ R)).hom.app A ≫ adj.unit.app _ from
        (adj.unit.naturality ((abSheafLiftSetIso J (U K ⋙ R)).hom.app A)).symm]
    try simp only [R.map_id, Category.comp_id]
    simp only [Category.assoc, R.map_id, Category.comp_id,
      adj.right_triangle_components_assoc]
    erw [R.map_id, Category.comp_id]
private theorem abAdjunction_unit (A : Sheaf J AddCommGrpCat.{u}) :
    (abAdjunction K J L R adj).unit.app A = (abUnit K J L R adj).app A := by
  unfold abAdjunction
  rfl
end AbelianAdjunction

private theorem addition_formula
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A) (ha : IsAddition J A a) :
    prodComparison (U J) A A ≫ a = (U J).map (prod.fst + prod.snd) := by
  ext T x
  change a.hom.app T _ = _
  rw [ha]
  change _ + _ = (prod.fst : A ⨯ A ⟶ A).hom.app T x +
    (prod.snd : A ⨯ A ⟶ A).hom.app T x
  congr 1
  · exact congrArg (fun f ↦ f.hom.app T x) (prodComparison_fst (U J) A A)
  · exact congrArg (fun f ↦ f.hom.app T x) (prodComparison_snd (U J) A A)

private theorem addition_transport
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits L]
    (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [PreservesFiniteLimits B] [B.Additive]
    (e : B ⋙ U K ≅ U J ⋙ L)
    (A : Sheaf J AddCommGrpCat.{u})
    (a : (U J).obj A ⨯ (U J).obj A ⟶ (U J).obj A)
    (b : (U K).obj (B.obj A) ⨯ (U K).obj (B.obj A) ⟶ (U K).obj (B.obj A))
    (ha : IsAddition J A a) (hb : IsAddition K (B.obj A) b) :
    b ≫ e.hom.app A = prod.map (e.hom.app A) (e.hom.app A) ≫
      inv (prodComparison L ((U J).obj A) ((U J).obj A)) ≫ L.map a := by
  apply (cancel_epi (prodComparison (B ⋙ U K) A A)).mp
  have hleft : prodComparison (B ⋙ U K) A A ≫ b =
      (U K).map (B.map (prod.fst + prod.snd)) := by
    rw [prodComparison_comp, Category.assoc, addition_formula K _ b hb,
      ← Functor.map_comp]
    congr 1
    rw [Preadditive.comp_add, prodComparison_fst, prodComparison_snd, B.map_add]
  rw [← Category.assoc, hleft]
  rw [show (U K).map (B.map (prod.fst + prod.snd)) ≫ e.hom.app A = _ from
    e.hom.naturality (prod.fst + prod.snd)]
  rw [← prodComparison_natural_of_natTrans_assoc e.hom]
  rw [prodComparison_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← L.map_comp, addition_formula J A a ha]
  rfl

section ModuleAction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

private def scalarEndo (M : Modules J Λ) (r : Λ) : (V J Λ).obj M ⟶ (V J Λ).obj M where
  hom :=
    { app := fun T ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro T S f
        ext x
        change M.val.obj T at x
        change
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app S r) •
              M.val.map f x =
            M.val.map f
              (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g ↦ g r)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f) }

set_option backward.isDefEq.respectTransparency false in
private theorem scalarEndo_one (M : Modules J Λ) : scalarEndo J Λ M 1 = 𝟙 _ := by
  ext T x
  change M.val.obj T at x
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T 1) • x = x
  rw [map_one, one_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem scalarEndo_zero (M : Modules J Λ) : scalarEndo J Λ M 0 = 0 := by
  ext T x
  change M.val.obj T at x
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T 0) • x = 0
  rw [map_zero, zero_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem scalarEndo_add (M : Modules J Λ) (r s : Λ) :
    scalarEndo J Λ M (r + s) = scalarEndo J Λ M r + scalarEndo J Λ M s := by
  ext T x
  change M.val.obj T at x
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T (r + s)) • x = _
  rw [map_add, add_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarEndo_mul (M : Modules J Λ) (r s : Λ) :
    scalarEndo J Λ M (r * s) = scalarEndo J Λ M s ≫ scalarEndo J Λ M r := by
  ext T x
  change M.val.obj T at x
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T (r * s)) • x = _
  rw [map_mul, mul_smul]
  rfl

variable (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) [B.Additive]

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def transportedModule (M : Modules J Λ) (T : Dᵒᵖ) :
    Module Λ ((B.obj ((V J Λ).obj M)).obj.obj T) where
  smul r x := (B.map (scalarEndo J Λ M r)).hom.app T x
  one_smul x := by
    change (B.map (scalarEndo J Λ M 1)).hom.app T x = x
    simp only [scalarEndo_one, Functor.map_id]
    rfl
  zero_smul x := by
    change (B.map (scalarEndo J Λ M 0)).hom.app T x = 0
    simp only [scalarEndo_zero, Functor.map_zero]
    rfl
  smul_zero r := (B.map (scalarEndo J Λ M r)).hom.app T |>.hom.map_zero
  smul_add r x y := (B.map (scalarEndo J Λ M r)).hom.app T |>.hom.map_add x y
  add_smul r s x := by
    change (B.map (scalarEndo J Λ M (r + s))).hom.app T x =
      (B.map (scalarEndo J Λ M r)).hom.app T x +
        (B.map (scalarEndo J Λ M s)).hom.app T x
    simp only [scalarEndo_add, B.map_add]
    rfl
  mul_smul r s x := by
    change (B.map (scalarEndo J Λ M (r * s))).hom.app T x =
      (B.map (scalarEndo J Λ M r)).hom.app T
        ((B.map (scalarEndo J Λ M s)).hom.app T x)
    simp only [scalarEndo_mul, B.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
private def transportedPresheaf (M : Modules J Λ) :
    PresheafOfModules.{u} ((Functor.const Dᵒᵖ).obj (RingCat.of Λ)) := by
  letI (T : Dᵒᵖ) : Module
      (((Functor.const Dᵒᵖ).obj (RingCat.of Λ)).obj T)
      ((B.obj ((V J Λ).obj M)).obj.obj T) := transportedModule K J Λ B M T
  exact PresheafOfModules.ofPresheaf (B.obj ((V J Λ).obj M)).obj (by
    intro T S f r x
    change (B.obj ((V J Λ).obj M)).obj.map f
        ((B.map (scalarEndo J Λ M r)).hom.app T x) =
      (B.map (scalarEndo J Λ M r)).hom.app S
        ((B.obj ((V J Λ).obj M)).obj.map f x)
    exact (congrArg (fun k ↦ k.hom x) ((B.map (scalarEndo J Λ M r)).hom.naturality f)).symm)

set_option backward.isDefEq.respectTransparency false in
private def transportedSheaf [HasWeakSheafify K RingCat.{u}] (M : Modules J Λ) :
    Modules K Λ := by
  let φ : (transportedPresheaf K J Λ B M).presheaf ⟶
      (B.obj ((V J Λ).obj M)).obj := eqToHom (by rfl)
  have : IsIso φ := by dsimp only [φ]; infer_instance
  exact PresheafOfModules.sheafify
    (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of Λ))) φ

set_option backward.isDefEq.respectTransparency false in
private theorem transportedSheaf_constant_smul [HasWeakSheafify K RingCat.{u}]
    (M : Modules J Λ) (T : Dᵒᵖ) (r : Λ) (x : (transportedSheaf K J Λ B M).val.obj T) :
    ((toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of Λ))).app T r) • x =
      (B.map (scalarEndo J Λ M r)).hom.app T x := by
  let α := toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of Λ))
  have h := ((PresheafOfModules.toSheafify α
    (M₀ := transportedPresheaf K J Λ B M)
    (eqToHom (show (transportedPresheaf K J Λ B M).presheaf =
      (B.obj ((V J Λ).obj M)).obj by rfl))).app T).hom.map_smul r x
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalarEndo_naturality {M N : Modules J Λ} (f : M ⟶ N) (r : Λ) :
    scalarEndo J Λ M r ≫ (V J Λ).map f =
      (V J Λ).map f ≫ scalarEndo J Λ N r := by
  ext T x
  exact (f.val.app T).hom.map_smul _ x

set_option backward.isDefEq.respectTransparency false in
private def transportedPresheafMap {M N : Modules J Λ} (f : M ⟶ N) :
    transportedPresheaf K J Λ B M ⟶ transportedPresheaf K J Λ B N :=
  PresheafOfModules.homMk (B.map ((V J Λ).map f)).hom (by
    intro T r x
    change (B.map ((V J Λ).map f)).hom.app T
        ((B.map (scalarEndo J Λ M r)).hom.app T x) =
      (B.map (scalarEndo J Λ N r)).hom.app T
        ((B.map ((V J Λ).map f)).hom.app T x)
    have h := congrArg B.map (scalarEndo_naturality J Λ f r)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg (fun k ↦ k.hom.app T x) h)

set_option backward.isDefEq.respectTransparency false in
private def transportedSheafMap [HasWeakSheafify K RingCat.{u}]
    {M N : Modules J Λ} (f : M ⟶ N) :
    transportedSheaf K J Λ B M ⟶ transportedSheaf K J Λ B N :=
  PresheafOfModules.sheafifyMap
    (M₀ := transportedPresheaf K J Λ B M) (A := B.obj ((V J Λ).obj M))
    (M₀' := transportedPresheaf K J Λ B N) (A' := B.obj ((V J Λ).obj N))
    (toSheafify K ((Functor.const Dᵒᵖ).obj (RingCat.of Λ)))
    (eqToHom (show (transportedPresheaf K J Λ B M).presheaf =
      (B.obj ((V J Λ).obj M)).obj by rfl)) (eqToHom (show (transportedPresheaf K J Λ B N).presheaf =
      (B.obj ((V J Λ).obj N)).obj by rfl))
    (transportedPresheafMap K J Λ B f) (B.map ((V J Λ).map f))
    (by ext T x; rfl)

private def transportedModuleFunctor [HasWeakSheafify K RingCat.{u}] :
    Modules J Λ ⥤ Modules K Λ where
  obj := transportedSheaf K J Λ B
  map := transportedSheafMap K J Λ B
  map_id := by
    intro M
    ext T x
    change (B.map ((V J Λ).map (𝟙 M))).hom.app T x = x
    rw [Functor.map_id, Functor.map_id]
    rfl
  map_comp := by
    intro M N P f g
    ext T x
    change (B.map ((V J Λ).map (f ≫ g))).hom.app T x =
      (B.map ((V J Λ).map g)).hom.app T ((B.map ((V J Λ).map f)).hom.app T x)
    rw [Functor.map_comp, Functor.map_comp]
    rfl


private def transportedUnderlyingIso [HasWeakSheafify K RingCat.{u}] :
    transportedModuleFunctor K J Λ B ⋙ V K Λ ≅ V J Λ ⋙ B :=
  NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro M N f; ext T x; rfl)

private theorem transported_scalarEndo [HasWeakSheafify K RingCat.{u}]
    (M : Modules J Λ) (r : Λ) :
    scalarEndo K Λ ((transportedModuleFunctor K J Λ B).obj M) r =
      B.map (scalarEndo J Λ M r) := by
  ext T x
  exact transportedSheaf_constant_smul K J Λ B M T r x

private def linearHomOfScalars
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ, scalarEndo J Λ M r ≫ f = f ≫ scalarEndo J Λ N r) : M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk f.hom (by
      intro T r x
      exact congrArg (fun k ↦ k.hom.app T x) (hf r))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).symm g⟩

private theorem linearHomOfScalars_forget
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ, scalarEndo J Λ M r ≫ f = f ≫ scalarEndo J Λ N r) :
    (V J Λ).map (linearHomOfScalars J Λ f hf) = f := rfl

variable [HasWeakSheafify K RingCat.{u}]
  (B' : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) [B'.Additive]
  (a : B ⊣ B')

private def moduleUnit : 𝟭 (Modules J Λ) ⟶
    transportedModuleFunctor K J Λ B ⋙ transportedModuleFunctor J K Λ B' where
  app M := linearHomOfScalars J Λ (a.unit.app ((V J Λ).obj M)) (by
    intro r
    dsimp only [Functor.comp_obj, Functor.id_obj]
    erw [transported_scalarEndo, transported_scalarEndo]
    exact a.unit.naturality (scalarEndo J Λ M r))
  naturality := by
    intro M N f
    apply (V J Λ).map_injective
    change (V J Λ).map f ≫ a.unit.app ((V J Λ).obj N) =
      a.unit.app ((V J Λ).obj M) ≫ B'.map (B.map ((V J Λ).map f))
    exact a.unit.naturality ((V J Λ).map f)

private def moduleCounit :
    transportedModuleFunctor J K Λ B' ⋙ transportedModuleFunctor K J Λ B ⟶ 𝟭 (Modules K Λ) where
  app M := linearHomOfScalars K Λ (a.counit.app ((V K Λ).obj M)) (by
    intro r
    dsimp only [Functor.comp_obj, Functor.id_obj]
    erw [transported_scalarEndo, transported_scalarEndo]
    exact a.counit.naturality (scalarEndo K Λ M r))
  naturality := by
    intro M N f
    apply (V K Λ).map_injective
    change B.map (B'.map ((V K Λ).map f)) ≫ a.counit.app ((V K Λ).obj N) =
      a.counit.app ((V K Λ).obj M) ≫ (V K Λ).map f
    exact a.counit.naturality ((V K Λ).map f)

@[irreducible] private def moduleAdjunction :
    transportedModuleFunctor K J Λ B ⊣ transportedModuleFunctor J K Λ B' where
  unit := moduleUnit K J Λ B B' a
  counit := moduleCounit K J Λ B B' a
  left_triangle_components M := by
    apply (V K Λ).map_injective
    change B.map (a.unit.app ((V J Λ).obj M)) ≫
      a.counit.app (B.obj ((V J Λ).obj M)) = 𝟙 _
    exact a.left_triangle_components _
  right_triangle_components M := by
    apply (V J Λ).map_injective
    change a.unit.app (B'.obj ((V K Λ).obj M)) ≫
      B'.map (a.counit.app ((V K Λ).obj M)) = 𝟙 _
    exact a.right_triangle_components _


private theorem moduleAdjunction_unit (M : Modules J Λ) :
    (V J Λ).map ((moduleAdjunction K J Λ B B' a).unit.app M) =
      a.unit.app ((V J Λ).obj M) := by
  unfold moduleAdjunction
  rfl


private instance transportedLimits [PreservesFiniteLimits B] :
    PreservesFiniteLimits (transportedModuleFunctor K J Λ B) := by
  have : PreservesFiniteLimits (V J Λ ⋙ B) := inferInstance
  have : PreservesFiniteLimits (transportedModuleFunctor K J Λ B ⋙ V K Λ) :=
    preservesFiniteLimits_of_natIso (transportedUnderlyingIso K J Λ B).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (V K Λ)

private instance transportedAdditive : (transportedModuleFunctor K J Λ B).Additive where
  map_add := by
    intro M N f g
    apply (V K Λ).map_injective
    change B.map ((V J Λ).map (f + g)) =
      B.map ((V J Λ).map f) + B.map ((V J Λ).map g)
    rw [Functor.map_add, Functor.map_add]

end ModuleAction
section Assembly
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ R) (hL : PreservesFiniteLimits L)

private theorem scalarEndo_unique (M : Modules J Λ) (r : Λ)
    (a : (V J Λ).obj M ⟶ (V J Λ).obj M) (ha : IsScalar J Λ M r a) :
    a = scalarEndo J Λ M r := by
  ext T x
  exact ha T x

private theorem assembledTransport
    (c : L.obj ((constantSheaf J (Type u)).obj Λ) ≅ CoeffSet K Λ)
    (p : L.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hcadd : ∀ m m', IsRingAdd J Λ m → IsRingAdd K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
        L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          c.hom =
      prod.map
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫ c.hom)
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫ c.hom)
        ≫ m')
    (hcmul : ∀ m m', IsRingMul J Λ m → IsRingMul K Λ m' →
      inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
        L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫
          c.hom =
      prod.map
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫ c.hom)
        (L.map ((constantCommuteCompose J (forget RingCat.{u})).hom.app (RingCat.of Λ)) ≫ c.hom)
        ≫ m')
    (hcscalar : ∀ r : Λ,
      L.map ((constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫
        c.hom ≫ (constantCommuteCompose K (forget RingCat.{u})).hom.app (RingCat.of Λ) =
      p.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) :
    Nonempty (ConstantLeftModuleInverseImageLift J K Λ L R adj hL) := by
  let := hL
  let : PreservesLimits R := adj.rightAdjoint_preservesLimits
  let : (abInverse K J L).Additive := Functor.additive_of_preserves_binary_products _
  let : (abDirect K J R).Additive := Functor.additive_of_preserves_binary_products _
  let B := abInverse K J L
  let B' := abDirect K J R
  let a := abAdjunction K J L R adj
  let F := transportedModuleFunctor K J Λ B
  let G := transportedModuleFunctor J K Λ B'
  let aM := moduleAdjunction K J Λ B B' a
  let eL := abSheafLiftSetIso K (U J ⋙ L)
  let eR := abSheafLiftSetIso J (U K ⋙ R)
  let eM := transportedUnderlyingIso K J Λ B
  let eD := transportedUnderlyingIso J K Λ B'
  let eS : F ⋙ W K Λ ≅ W J Λ ⋙ L :=
    Functor.isoWhiskerRight eM (U K) ≪≫ Functor.isoWhiskerLeft (V J Λ) eL
  let : PreservesColimits F := aM.leftAdjoint_preservesColimits
  refine ⟨{
    ringUnderlying := c
    ring_add := hcadd
    ring_mul := hcmul
    pointIso := p
    constant_scalar := hcscalar
    moduleFunctor := F
    moduleDirect := G
    moduleAdj := aM
    additive := inferInstance
    preservesFiniteLimits := inferInstance
    preservesFiniteColimits := inferInstance
    abelianInverse := B
    abelianDirect := B'
    abelianAdj := a
    abelianSetIso := eL
    abelianDirectSetIso := eR
    abelian_addition := addition_transport K J L B eL
    abelian_unit := ?_
    underlyingIso := eM
    directUnderlyingIso := eD
    moduleSetIso := eS
    moduleSetIso_compatibility := ?_
    scalar_compatibility := ?_
    unit_compatibility := ?_ }⟩
  · intro A
    dsimp only [a]
    rw [abAdjunction_unit, abUnit_forget]
    dsimp only [abUnitSets, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, eL, eR, B]
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← R.map_comp, Iso.inv_hom_id_app, R.map_id, Category.comp_id]
    erw [Category.comp_id]
  · intro M
    rfl
  · intro M r f g hf hg
    rw [scalarEndo_unique J Λ M r f hf,
      scalarEndo_unique K Λ (F.obj M) r g hg]
    change scalarEndo K Λ ((transportedModuleFunctor K J Λ B).obj M) r ≫ 𝟙 _ =
      𝟙 _ ≫ B.map (scalarEndo J Λ M r)
    rw [transported_scalarEndo, Category.id_comp, Category.comp_id]
  · intro M
    dsimp only [aM]
    rw [moduleAdjunction_unit]
    change a.unit.app ((V J Λ).obj M) ≫ 𝟙 _ ≫ B'.map (𝟙 _) = _
    rw [Functor.map_id]
    erw [Category.id_comp, Category.comp_id]
end Assembly

end TransportConstruction

/-- Transport of abelian and constant left-module operations, including adjunctions and
exactness. Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), fixed-ring
paragraph; Modules on Sites, Tag 04JC
(blueprint: lem-pe-constant-left-module-transport).

Proof: Regard a constant sheaf as a coproduct of terminal sheaves. The left adjoint
preserves this coproduct and the terminal object, giving the coefficient comparison
normalized on scalar summands. Apply the functor and its product comparisons to the
ring operations. Their compatibility is checked on constant sections and then locally
on covers, since every coefficient section is locally constant. Transport abelian
group objects using the finite-product-preserving adjunction and the equivalence with
abelian sheaves. For a module action a, transport it as L(a) after the inverse product
comparison and the inverse coefficient comparison. The same finite-product diagrams
prove the module axioms. The right adjoint transports actions after restricting along
the coefficient map R(c) after the adjunction unit. Naturality of the abelian adjunction
bijection says that a map commutes with each constant scalar exactly when its mate
does. Local constancy upgrades this condition to linearity for all coefficient
sections, so the bijection restricts to a module adjunction with the asserted unit.
Kernels are equalizers on underlying sets, hence preserved by the left exact functor;
cokernels are preserved by the lifted left adjoint. Addition of maps is transported
using products and addition, so the module functor is additive and exact. -/
theorem constantLeftModuleTransport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L) :
    Nonempty (ConstantLeftModuleInverseImageLift J K Λ L R adj hL) := by
  let := hL
  exact assembledTransport K J Λ L R adj hL
    (normalizedRingComparison J K L R adj Λ)
    ((constantComparison J K L R adj).app PUnit.{u+1})
    (fun m m' hm hm' ↦ ringOperation_transport J K L R adj Λ m m'
      (fun p ↦ p.1 + p.2) (ringAddition_constants J Λ m hm)
      (ringAddition_constants K Λ m' hm'))
    (fun m m' hm hm' ↦ ringOperation_transport J K L R adj Λ m m'
      (fun p ↦ p.1 * p.2) (ringMultiplication_constants J Λ m hm)
      (ringMultiplication_constants K Λ m' hm'))
    (normalizedRingComparison_scalar J K L R adj Λ)

end CategoryTheory
