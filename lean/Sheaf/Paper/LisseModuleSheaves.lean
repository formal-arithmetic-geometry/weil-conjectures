module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Lisse sheaves of finite modules and module objects

Source: literature/stacks-project/etale-cohomology.tex, Lemma 0DV5, proof of (1)--(3),
with sites-modules Lemma 093S (1)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Sheaves of left `Λ`-modules on `Y_et` are `Sheaf Y.smallEtaleTopology (ModuleCat.{u+1} Λ)`
with `Λ : Type (u + 1)` (STATE: the encoding of the six-functor and constructible chapters).
`FLC(Y)` is `IsFiniteLocallyConstantEtaleSheafOfSets` (def-weil-pbc-etale-sheaves).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- A sheaf of left `Λ`-modules on `Y_et` is *lisse* when there are an etale covering
`{U_i → Y}` and finite left `Λ`-modules `M_i` with `F|_{U_i}` isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf (the sheafified constant presheaf) of `M_i`.
Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
def IsLisseModuleSheaf (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M)

/-- A `Λ`-module structure on a sheaf of sets `A` in the sense of commutative diagrams:
morphisms `+ : A × A → A`, `0 : * → A` from the final object, `- : A → A` and `λ · : A → A`
for every `λ ∈ Λ`, satisfying the axioms of a left `Λ`-module as equalities of morphisms
(products are those of all sheaves of sets). Source: Stacks Project, Lemma 0DV5, proof of
(2)--(3) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure ModuleObjectStruct (Λ : Type (u + 1)) [Ring Λ]
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  /-- Addition. -/
  add : A ⨯ A ⟶ A
  /-- Zero, from the final object. -/
  zero : ⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1))) ⟶ A
  /-- Negation. -/
  neg : A ⟶ A
  /-- Scalar multiplication by each element of `Λ`. -/
  smul : Λ → (A ⟶ A)
  add_assoc : prod.map add (𝟙 A) ≫ add =
    (prod.associator A A A).hom ≫ prod.map (𝟙 A) add ≫ add
  add_comm : (prod.braiding A A).hom ≫ add = add
  zero_add : prod.lift (terminal.from A ≫ zero) (𝟙 A) ≫ add = 𝟙 A
  neg_add_cancel : prod.lift neg (𝟙 A) ≫ add = terminal.from A ≫ zero
  one_smul : smul 1 = 𝟙 A
  mul_smul (r s : Λ) : smul (r * s) = smul s ≫ smul r
  smul_add (r : Λ) : add ≫ smul r = prod.map (smul r) (smul r) ≫ add
  add_smul (r s : Λ) : smul (r + s) = prod.lift (smul r) (smul s) ≫ add
  smul_zero (r : Λ) : zero ≫ smul r = zero
  zero_smul : smul 0 = terminal.from A ≫ zero

variable (Y Λ) in
/-- A `Λ`-module object of `FLC(Y)`: a finite locally constant sheaf of sets with a
`Λ`-module structure in the sense of commutative diagrams. Source: Stacks Project,
Lemma 0DV5 (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure LambdaModuleObject where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf Y.smallEtaleTopology (Type (u + 1))
  isFLC : IsFiniteLocallyConstantEtaleSheafOfSets sheaf
  /-- The module operations. -/
  str : ModuleObjectStruct Λ sheaf

namespace LambdaModuleObject

/-- A morphism of `Λ`-module objects: a morphism of `FLC(Y)` commuting with addition, zero,
negation and every scalar multiplication. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
@[ext]
structure Hom (A B : LambdaModuleObject Y Λ) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : A.sheaf ⟶ B.sheaf
  add : A.str.add ≫ hom = prod.map hom hom ≫ B.str.add
  zero : A.str.zero ≫ hom = B.str.zero
  neg : A.str.neg ≫ hom = hom ≫ B.str.neg
  smul (r : Λ) : A.str.smul r ≫ hom = hom ≫ B.str.smul r

/-- The category of `Λ`-module objects of `FLC(Y)`. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
instance : Category (LambdaModuleObject Y Λ) where
  Hom := Hom
  id A := ⟨𝟙 _, by simp, by simp, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.add, Category.assoc, g.add,
      ← Category.assoc, prod.map_map], by rw [← Category.assoc, f.zero, g.zero],
    by rw [← Category.assoc, f.neg, Category.assoc, g.neg, Category.assoc],
    fun r => by rw [← Category.assoc, f.smul, Category.assoc, g.smul, Category.assoc]⟩

end LambdaModuleObject

variable (Y Λ) in
/-- The category of lisse sheaves of left `Λ`-modules, with `Λ`-linear maps of sheaves.
Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
abbrev LisseModuleSheafCategory : Type (u + 2) :=
  ObjectProperty.FullSubcategory
    (IsLisseModuleSheaf (Y := Y) (Λ := Λ))

/-- A module-object structure on the underlying sheaf of sets of a sheaf of `Λ`-modules `F`
is the one of `F` when, on the sections over every `U`, its addition, zero, negation and
scalar multiplications are those of the `Λ`-module `F(U)`. Source: Stacks Project,
Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
def ModuleObjectStruct.IsUnderlying (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F)) : Prop :=
  (∀ U x, S.add.hom.app U x =
      @id (F.obj.obj U) ((prod.fst : _ ⨯ _ ⟶ (sheafForget _).obj F).hom.app U x) +
        @id (F.obj.obj U) ((prod.snd : _ ⨯ _ ⟶ (sheafForget _).obj F).hom.app U x)) ∧
    (∀ U x, S.zero.hom.app U x = (0 : F.obj.obj U)) ∧
    (∀ U (x : F.obj.obj U), S.neg.hom.app U x = -x) ∧
    ∀ (r : Λ) U (x : F.obj.obj U), (S.smul r).hom.app U x = r • x

/-- Clause (1): a sheaf of left modules over a finite ring `Λ` is lisse if and only if its
underlying sheaf of sets lies in `FLC(Y)`. Source: Stacks Project, Lemma 0DV5 (1), using
Lemma 093S (1) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: if `F` is lisse, choose an etale covering on which it is isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf of a finite left `Λ`-module `M_i`; forgetting the module
structure gives an isomorphism of sheaves of sets with the constant finite sheaf underlying
`M_i`, so the underlying sheaf lies in `FLC(Y)`. Conversely, trivialize the underlying sheaf
on an etale cover, and also the finite products that occur as sources of the operations.
Each operation sends every element of its finite constant source to a section of the finite
constant target, which after an etale refinement is a constant section; refining over the
finite source makes the operation a map of finite constant sets. As `Λ` is finite there are
finitely many operations, so one common refinement makes all of them constant. The module
axioms hold as equalities of sheaf maps, so the local constant finite set is a finite left
`Λ`-module and the local identification is an isomorphism of sheaves of `Λ`-modules. -/
theorem lisseModuleSheaf_iff_underlying_finiteLocallyConstant [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsLisseModuleSheaf F ↔
      IsFiniteLocallyConstantEtaleSheafOfSets ((sheafForget Y.smallEtaleTopology).obj F) := by
  sorry

/-- The underlying sheaf of sets of a sheaf of `Λ`-modules carries exactly one module-object
structure given on sections by the operations of the modules `F(U)`. Source: Stacks Project,
Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: products of sheaves of sets are computed on sections, and the operations of the
modules `F(U)` commute with the restriction maps, so they are morphisms of sheaves; the
module axioms hold on sections. A morphism of sheaves is determined by its sections. -/
theorem existsUnique_moduleObjectStruct_isUnderlying
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃! S : ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F), S.IsUnderlying F := by
  sorry

/-- The module-object structure of the underlying sheaf of sets of a sheaf of `Λ`-modules:
its addition, zero, negation and scalar multiplications. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
noncomputable def underlyingModuleObjectStruct
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ModuleObjectStruct Λ ((sheafForget Y.smallEtaleTopology).obj F) :=
  (existsUnique_moduleObjectStruct_isUnderlying F).exists.choose

/-- A `Λ`-linear map of sheaves commutes with the underlying addition, zero, negation and
scalar multiplications. Source: Stacks Project, Lemma 0DV5, proof of (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: on sections over every `U` the map is `Λ`-linear, and morphisms of sheaves of sets
are determined by their sections. -/
theorem underlyingModuleObjectStruct_map
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G) :
    let φ := (sheafForget Y.smallEtaleTopology).map f
    (underlyingModuleObjectStruct F).add ≫ φ =
        prod.map φ φ ≫ (underlyingModuleObjectStruct G).add ∧
      (underlyingModuleObjectStruct F).zero ≫ φ = (underlyingModuleObjectStruct G).zero ∧
      (underlyingModuleObjectStruct F).neg ≫ φ = φ ≫ (underlyingModuleObjectStruct G).neg ∧
      ∀ r : Λ, (underlyingModuleObjectStruct F).smul r ≫ φ =
        φ ≫ (underlyingModuleObjectStruct G).smul r := by
  sorry

variable (Y Λ) in
/-- The functor of clause (2): a lisse sheaf `F` goes to its underlying sheaf of sets (in
`FLC(Y)` by clause (1)) with the addition, zero, negation and scalar multiplications of `F`;
a `Λ`-linear map goes to its underlying map of sheaves of sets. Source: Stacks Project,
Lemma 0DV5 (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
noncomputable def lisseToModuleObject [Finite Λ] :
    LisseModuleSheafCategory Y Λ ⥤ LambdaModuleObject Y Λ where
  obj F := ⟨(sheafForget Y.smallEtaleTopology).obj F.obj,
    (lisseModuleSheaf_iff_underlying_finiteLocallyConstant F.obj).mp F.property,
    underlyingModuleObjectStruct F.obj⟩
  map f := ⟨(sheafForget Y.smallEtaleTopology).map f.hom,
    (underlyingModuleObjectStruct_map f.hom).1, (underlyingModuleObjectStruct_map f.hom).2.1,
    (underlyingModuleObjectStruct_map f.hom).2.2.1, (underlyingModuleObjectStruct_map f.hom).2.2.2⟩
  map_id F := LambdaModuleObject.Hom.ext ((sheafForget Y.smallEtaleTopology).map_id F.obj)
  map_comp f g := LambdaModuleObject.Hom.ext
    ((sheafForget Y.smallEtaleTopology).map_comp f.hom g.hom)

/-- Clause (2): the functor sending a lisse sheaf of left `Λ`-modules to its underlying sheaf
of sets with its addition, zero, negation and scalar multiplications is an isomorphism of
categories (an equivalence that is bijective on objects) onto the `Λ`-module objects of
`FLC(Y)`. Source: Stacks Project, Lemma 0DV5 (2)--(3)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: by clause (1) the functor lands in `FLC(Y)`. Conversely a module object of `FLC(Y)`
gives on every `U` a `Λ`-module structure on its sections, compatible with restriction, so a
sheaf of `Λ`-modules, lisse by clause (1). Forgetting and restoring the operations leaves
every operation unchanged, and a module object already has exactly the corresponding
sheaf-of-modules structure. A map is preserved and recovered precisely when it commutes with
addition, zero, negation and scalar multiplication. So the functor is bijective on objects and
on morphisms: an isomorphism of categories, hence an equivalence. -/
theorem lisseToModuleObject_isIso_of_categories [Finite Λ] :
    (lisseToModuleObject Y Λ).IsEquivalence ∧
      Function.Bijective (lisseToModuleObject Y Λ).obj := by
  sorry

end AlgebraicGeometry.Scheme
