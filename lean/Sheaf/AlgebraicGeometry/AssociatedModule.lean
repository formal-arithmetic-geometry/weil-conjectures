module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Sheaf of modules associated to a module over global sections

Source: Stacks Project, Modules, Lemma 01BH construction (3) and Definition 01BI
(blueprint: def-weil-pbc-associated-module).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

namespace AlgebraicGeometry

variable (X : SheafedSpace CommRingCat.{u})

/-- The structure sheaf `O_X` regarded as a sheaf of rings (Stacks, Modules, Lemma 01BH (3))
(blueprint: def-weil-pbc-associated-module). -/
abbrev associatedRingSheaf :
    Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology (X : Type u))
    (forget₂ CommRingCat RingCat)).obj X.sheaf

/-- The restriction map `R = O_X(X) → O_X(U)` making `O_X(U)` an `R`-algebra
(Stacks, Modules, Lemma 01BH (3)) (blueprint: def-weil-pbc-associated-module). -/
abbrev associatedRestriction (U : (Opens (X : Type u))ᵒᵖ) :
    X.presheaf.obj (op (⊤ : Opens (X : Type u))) ⟶ X.presheaf.obj U :=
  X.presheaf.map (homOfLE le_top).op

/-- The base change `O_X(U) ⊗_R M` of `M` along the restriction map
(Stacks, Modules, Lemma 01BH (3)) (blueprint: def-weil-pbc-associated-module). -/
noncomputable abbrev associatedExtension
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (U : (Opens (X : Type u))ᵒᵖ) : ModuleCat (X.presheaf.obj U) :=
  (ModuleCat.extendScalars (associatedRestriction X U).hom).obj M

/-- The restriction on scalar extensions sends `a ⊗ m` to `a|_V ⊗ m`.
For fixed `a`, the map `m ↦ a|_V ⊗ m` is additive, and the resulting map
in `a` is additive. The tensor balancing relation is preserved because
`ρ^U_V ∘ ρ^X_U = ρ^X_V`, by the presheaf composition law. Thus the tensor
universal property gives an additive map. It is `O_X(U)`-linear into the
restriction of scalars, since `ρ^U_V(ba) = ρ^U_V(b)ρ^U_V(a)`; this equality
extends from pure tensors by additivity. Any other such linear map agrees
on pure tensors, hence on their finite sums, proving uniqueness
(Stacks, Modules, Lemma 01BH (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedExtension_restriction_existsUnique
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    {U V : (Opens (X : Type u))ᵒᵖ} (f : U ⟶ V) :
    ∃! r : associatedExtension X M U ⟶
        (ModuleCat.restrictScalars ((associatedRingSheaf X).obj.map f).hom).obj
          (associatedExtension X M V),
      ∀ (a : X.presheaf.obj U) (m : M),
        r (a ⊗ₜ[(X.presheaf.obj (op (⊤ : Opens (X : Type u)))),
          (associatedRestriction X U).hom] m) =
          (X.presheaf.map f a) ⊗ₜ[(X.presheaf.obj (op (⊤ : Opens (X : Type u)))),
            (associatedRestriction X V).hom] m := by
  sorry

/-- The restriction `ρ^U_V ⊗ id_M` of the tensor presheaf, the unique map of
`associatedExtension_restriction_existsUnique` (Stacks, Modules, Lemma 01BH (3))
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedExtensionRestriction
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    {U V : (Opens (X : Type u))ᵒᵖ} (f : U ⟶ V) :=
  Classical.choose (associatedExtension_restriction_existsUnique X M f)

/-- Restriction of scalar extensions respects identities and composition.
The defining unique map sends `a ⊗ m` to `a|_V ⊗ m`. For the identity,
`a|_U = a`, and the scalar-restriction identity isomorphism also acts as
the identity on elements. For composition, applying the two restrictions
sends `a ⊗ m` to `(a|_V)|_W ⊗ m = a|_W ⊗ m`, by the presheaf composition
law; the scalar-restriction composition isomorphism acts identically on
elements. In each case the two linear maps agree on pure tensors, which
generate the tensor product, so they are equal
(Stacks, Modules, Lemma 01BH (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedExtensionRestriction_laws
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) :
    (∀ U, associatedExtensionRestriction X M (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((associatedRingSheaf X).obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((associatedRingSheaf X).obj.map_id U))).inv.app _) ∧
    (∀ U V W (f : U ⟶ V) (g : V ⟶ W),
      associatedExtensionRestriction X M (f ≫ g) =
        associatedExtensionRestriction X M f ≫
          (ModuleCat.restrictScalars _).map (associatedExtensionRestriction X M g) ≫
          (ModuleCat.restrictScalarsComp' _ _ _
            (congrArg RingCat.Hom.hom ((associatedRingSheaf X).obj.map_comp f g))).inv.app _) := by
  sorry

/-- The tensor presheaf `U ↦ O_X(U) ⊗_{Γ(X,O_X)} M`, with restrictions
`ρ ⊗ id`, from Stacks, Modules, Lemma 01BH (3).
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModulePresheaf
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) :
    PresheafOfModules.{u} (associatedRingSheaf X).obj where
  obj U := associatedExtension X M U
  map f := associatedExtensionRestriction X M f
  map_id U := (associatedExtensionRestriction_laws X M).1 U
  map_comp f g := (associatedExtensionRestriction_laws X M).2 _ _ _ f g

/-- The component `id ⊗ f : O_X(U) ⊗_R M → O_X(U) ⊗_R N` of the map induced by `f`
(Stacks, Modules, Lemma 01BH (2), (3)) (blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModulePresheafMapApp
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) (U : (Opens (X : Type u))ᵒᵖ) :
    (associatedModulePresheaf X M).obj U ⟶
      (associatedModulePresheaf X N).obj U :=
  (ModuleCat.extendScalars (associatedRestriction X U).hom).map f

/-- Base change of a linear map commutes with restriction: scalar extension
sends `a ⊗ m` to `a ⊗ f(m)`, and the chosen restriction sends it to
`a|_V ⊗ m` by its defining existence-and-uniqueness theorem. Therefore
both composites send `a ⊗ m` to `a|_V ⊗ f(m)`. Both are linear over
`O_X(U)` into the restricted target; since pure tensors generate their
source, equality on these tensors proves equality of the morphisms
(Stacks, Modules, Lemma 01BH (2), (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedModulePresheafMap_naturality
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) {U V : (Opens (X : Type u))ᵒᵖ} (i : U ⟶ V) :
    (associatedModulePresheaf X M).map i ≫
      (ModuleCat.restrictScalars ((associatedRingSheaf X).obj.map i).hom).map
        (associatedModulePresheafMapApp X f V) =
      associatedModulePresheafMapApp X f U ≫
        (associatedModulePresheaf X N).map i := by
  sorry

/-- The componentwise maps `id ⊗ f` form the morphism of tensor presheaves
from Stacks, Modules, Lemma 01BH (2), (3).
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModulePresheafMap
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) : associatedModulePresheaf X M ⟶ associatedModulePresheaf X N where
  app U := associatedModulePresheafMapApp X f U
  naturality i := associatedModulePresheafMap_naturality X f i

/-- On every open, base change sends the identity to the identity and preserves
composition; hence the induced presheaf morphisms do too (Stacks, Modules,
Lemma 01BH (2); blueprint: def-weil-pbc-associated-module). -/
theorem associatedModulePresheafMap_laws
    (M N P : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (f : M ⟶ N) (g : N ⟶ P) :
    associatedModulePresheafMap X (𝟙 M) = 𝟙 _ ∧
      associatedModulePresheafMap X (f ≫ g) =
        associatedModulePresheafMap X f ≫ associatedModulePresheafMap X g := by
  constructor
  · ext U x
    simp [associatedModulePresheafMap, associatedModulePresheafMapApp]
    rfl
  · ext U x
    simp [associatedModulePresheafMap, associatedModulePresheafMapApp]
    rfl

/-- The tensor presheaf construction is functorial in the module, by the
componentwise maps `id ⊗ f` (Stacks, Modules, Lemma 01BH (2), (3)).
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModulePresheafFunctor :
    ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))) ⥤
      PresheafOfModules.{u} (associatedRingSheaf X).obj where
  obj M := associatedModulePresheaf X M
  map f := associatedModulePresheafMap X f
  map_id M := (associatedModulePresheafMap_laws X M M M (𝟙 M) (𝟙 M)).1
  map_comp f g := (associatedModulePresheafMap_laws X _ _ _ f g).2

/-- Sheafification makes the associated-module construction into a functor.
The component at `M` is the sheafification of `U ↦ O_X(U) ⊗_R M` and its map
at `f` is the unique map induced by `id ⊗ f` (Stacks, Modules, Lemma 01BH (2),
(3); blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModuleFunctor :
    ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))) ⥤
      SheafOfModules.{u} (associatedRingSheaf X) :=
  associatedModulePresheafFunctor X ⋙
    PresheafOfModules.sheafification (𝟙 (associatedRingSheaf X).obj)

/-- The sheafification of the tensor presheaf. For each open `U`, restriction
from `X` gives an `R`-algebra structure on `O_X(U)`, so base change gives
`P_M(U) = O_X(U) ⊗_R M`. The restrictions `ρ ⊗ id` respect identity and
composition and are semilinear, hence form a presheaf of `O_X`-modules.
Sheafification yields `F_M` and its universal `O_X`-linear map `σ_M`.
The unit `m ↦ 1 ⊗ m` followed by `σ_M` gives the linear canonical section
map. A linear map `f` induces `id ⊗ f` on the presheaves, and the universal
property induces `F_f`; uniqueness proves identity, composition, and
compatibility with canonical sections. This is Stacks, Modules, Lemma 01BH
construction (3) and Definition 01BI
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModule (X : SheafedSpace CommRingCat.{u})
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat RingCat)).obj X.sheaf) :=
  (associatedModuleFunctor X).obj M

/-- The `O_X`-linear sheafification map `P_M ⟶ F_M`; its universal property is
the sheafification adjunction (Stacks, Modules, Lemma 01BH (3)).
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModuleSheafificationMap
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) :
    associatedModulePresheaf X M ⟶ (associatedModule X M).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (associatedRingSheaf X).obj)).unit.app (associatedModulePresheaf X M)

/-- Restriction from the whole space to itself is the identity ring map,
since it comes from the identity inclusion (Stacks, Modules, Lemma 01BH (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedRestriction_top :
    (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom =
      RingHom.id (X.presheaf.obj (op (⊤ : Opens (X : Type u)))) := by
  simp [associatedRestriction]

/-- The `R`-linear canonical section map, characterized by the sheafification
image of `1 ⊗ m` (Stacks, Modules, Lemma 01BH (3), Definition 01BI).
(blueprint: def-weil-pbc-associated-module). -/
noncomputable def associatedModuleCanonicalSection
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) :
    M ⟶ (associatedModule X M).val.obj (op (⊤ : Opens (X : Type u))) :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map
      (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom ≫
    (ModuleCat.restrictScalars _).map
      ((associatedModuleSheafificationMap X M).app
        (op (⊤ : Opens (X : Type u)))) ≫
    (ModuleCat.restrictScalarsId'
      (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom
      (associatedRestriction_top X)).hom.app _

/-- On an element `m`, the canonical section is `σ_{M,X}(1 ⊗ m)`.
The extension-of-scalars unit sends `m` to `1 ⊗ m`; the final scalar
restriction isomorphism is the identity on elements because restriction
from `X` to itself is the identity (Stacks, Modules, Lemma 01BH (3),
Definition 01BI; blueprint: def-weil-pbc-associated-module). -/
theorem associatedModuleCanonicalSection_apply
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))) (m : M) :
    associatedModuleCanonicalSection X M m =
      (associatedModuleSheafificationMap X M).app
        (op (⊤ : Opens (X : Type u)))
          ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map
            (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom :
              M ⟶ (ModuleCat.restrictScalars _).obj
                (associatedExtension X M (op (⊤ : Opens (X : Type u))))) m) := by
  rfl

/-- Every `O_X`-linear map from the tensor presheaf to a sheaf factors uniquely
through the sheafification map. Apply the sheafification adjunction to the
identity morphism of the structure sheaf; its unit is `associatedModuleSheafificationMap`.
The adjunction bijection gives existence and uniqueness of the factorization
(Stacks, Modules, Lemma 01BH (3); blueprint: def-weil-pbc-associated-module). -/
theorem associatedModuleSheafificationMap_universal
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (F : SheafOfModules.{u} (associatedRingSheaf X))
    (h : associatedModulePresheaf X M ⟶ F.val) :
    ∃! g : associatedModule X M ⟶ F,
      associatedModuleSheafificationMap X M ≫ g.val = h := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (associatedRingSheaf X).obj)
  let e := adj.homEquiv (associatedModulePresheaf X M) F
  refine ⟨e.symm h, ?_, ?_⟩
  · have he := e.apply_symm_apply h
    rw [Adjunction.homEquiv_unit] at he
    ext U x
    exact congrArg (fun k => k.app U x) he
  · intro g hg
    apply e.injective
    rw [e.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    ext U x
    exact congrArg (fun k => k.app U x) hg

/-- Naturality of sheafification gives the equality after composing with
`σ_M`: at each open the presheaf map is `id ⊗ f`. Apply the naturality
square of the unit of the sheafification adjunction (Stacks, Modules,
Lemma 01BH (2), (3); blueprint: def-weil-pbc-associated-module). -/
theorem associatedModuleMap_sheafification_natural
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) :
    associatedModuleSheafificationMap X M ≫ ((associatedModuleFunctor X).map f).val =
      associatedModulePresheafMap X f ≫ associatedModuleSheafificationMap X N := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (associatedRingSheaf X).obj)).unit.naturality
      (associatedModulePresheafMap X f)).symm

/-- The map `F_f` is uniquely determined by `F_f ∘ σ_M = σ_N ∘ P_f`.
The functor map has this equality by naturality of the unit. Any other map
with the equality agrees with it by the universal property of sheafification
(Stacks, Modules, Lemma 01BH (2), (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedModuleMap_unique
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) (g : associatedModule X M ⟶ associatedModule X N)
    (hg : associatedModuleSheafificationMap X M ≫ g.val =
      associatedModulePresheafMap X f ≫ associatedModuleSheafificationMap X N) :
    g = (associatedModuleFunctor X).map f := by
  obtain ⟨k, _, hk⟩ := associatedModuleSheafificationMap_universal X M
    (associatedModule X N)
    (associatedModulePresheafMap X f ≫ associatedModuleSheafificationMap X N)
  exact (hk g hg).trans
    (hk ((associatedModuleFunctor X).map f)
      (associatedModuleMap_sheafification_natural X f)).symm

/-- The canonical sections are natural in `M`. Evaluate the naturality
square of sheafification at the whole space and apply it to `1 ⊗ m`;
`P_f(1 ⊗ m) = 1 ⊗ f(m)` by base change. Thus both composites send `m`
to `σ_N(1 ⊗ f(m))` (Stacks, Modules, Lemma 01BH (2), (3)).
(blueprint: def-weil-pbc-associated-module). -/
theorem associatedModuleCanonicalSection_natural
    {M N : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u))))}
    (f : M ⟶ N) :
    associatedModuleCanonicalSection X M ≫
      ((associatedModuleFunctor X).map f).val.app
        (op (⊤ : Opens (X : Type u))) =
      f ≫ associatedModuleCanonicalSection X N := by
  ext m
  have h := congrArg (fun k => k.app (op (⊤ : Opens (X : Type u)))
    (ModuleCat.ExtendRestrictScalarsAdj.Unit.map
      (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom m))
    (associatedModuleMap_sheafification_natural X f)
  change ((associatedModuleFunctor X).map f).val.app
    (op (⊤ : Opens (X : Type u)))
    ((associatedModuleSheafificationMap X M).app (op (⊤ : Opens (X : Type u)))
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map
        (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom m)) =
    (associatedModuleSheafificationMap X N).app (op (⊤ : Opens (X : Type u)))
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map
        (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom (f m))
  exact h

end AlgebraicGeometry
