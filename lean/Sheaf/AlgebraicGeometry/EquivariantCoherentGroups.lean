module

public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Data for equivariant coherent proper pushforward

Source: Milne, Algebraic Groups, Section 22d, supporting proper-pushforward
construction; Stacks 03LF, 01T0, 02O5 and 02O6.
(blueprint: def-sfb-equivariant-coherent-groups)

Coherent objects, integral quotients, rational representations and their tensor
operations are imported from the Q60 nodes. Only the remaining geometric,
higher-image, subgroup-restriction and point-comparison interfaces are defined here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.EquivariantCoherent.ProperPushforwardData

variable (k : Type u) [Field k]

/-- An affine finite-type group scheme over the field.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure Group where
  scheme : Over (Spec (.of k))
  group : GrpObj scheme
  affine : IsAffine scheme.left
  finiteType : LocallyOfFiniteType scheme.hom
  quasiCompact : QuasiCompact scheme.hom

attribute [instance] Group.group Group.affine Group.finiteType Group.quasiCompact

/-- A scheme with an algebraic left action; no finiteness is imposed here.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure Space (G : Group k) where
  scheme : Over (Spec (.of k))
  action : ModObj G.scheme scheme

attribute [instance] Space.action

/-- The separated finite-type condition for a scheme over the field.
Source: Stacks 01T0 (blueprint: def-sfb-equivariant-coherent-groups). -/
def Space.IsFiniteSeparated {G : Group k} (X : Space k G) : Prop :=
  IsSeparated X.scheme.hom ∧ LocallyOfFiniteType X.scheme.hom ∧ QuasiCompact X.scheme.hom

/-- The existing linearization in the fibre-action direction, kept folded when
elaborating higher-image comparisons. No new linearization data are introduced.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-groups). -/
@[irreducible]
def actionIso {G : Group k} {X : Space k G}
    {D : ActionGroupoidModel G.scheme X.scheme} (M : Coherent D) :
    (Scheme.Modules.tensorPullback (source G.scheme X.scheme)).obj (underlying M) ≅
      (Scheme.Modules.tensorPullback (target G.scheme X.scheme)).obj (underlying M) :=
  (linearization M).symm

/-- Higher direct images use the recorded shared derived-category construction.
Only a localization model is selected; the modules and their derived direct images are
unchanged. Source: Stacks 0A1G (blueprint: def-sfb-equivariant-coherent-groups). -/
def higher {G : Group k} {X Y : Space k G} (f : X.scheme ⟶ Y.scheme) (q : ℕ) :
    X.scheme.left.Modules ⥤ Y.scheme.left.Modules :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.scheme.left.toRingedSpace))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.scheme.left.toRingedSpace))
  schemeModuleHigherDirectImage f.left (q : ℤ)


/-- A separated finite-type action scheme, retaining the unrestricted action space.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure FiniteSpace (G : Group k) where
  space : Space k G
  finiteSeparated : space.IsFiniteSeparated k

/-- A proper equivariant morphism, with its original scheme morphism.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure ProperMap {G : Group k} (X Y : Space k G) where
  map : X.scheme ⟶ Y.scheme
  equivariant : IsModHom G.scheme map
  proper : IsProper map.left

attribute [instance] ProperMap.equivariant ProperMap.proper

/-- A closed subgroup scheme, including nonreduced closed subgroups.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure ClosedSubgroup (G : Group k) where
  group : Group k
  map : group.scheme ⟶ G.scheme
  hom : IsMonHom map
  closed : IsClosedImmersion map.left

attribute [instance] ClosedSubgroup.hom ClosedSubgroup.closed

/-- Restriction of the action on the same underlying scheme.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
structure RestrictedSpace {G : Group k} (H : ClosedSubgroup k G) (X : Space k G) where
  action : ModObj H.group.scheme X.scheme
  compatibility : ∀ (T : Over (Spec (.of k))) (h : T ⟶ H.group.scheme) (x : T ⟶ X.scheme),
    CategoryTheory.CartesianMonoidalCategory.lift h x ≫ action.smul = (h ≫ H.map) • x

/-- The restricted action has literally the original underlying scheme.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
def RestrictedSpace.space {G : Group k} {H : ClosedSubgroup k G} {X : Space k G}
    (D : RestrictedSpace k H X) : Space k H.group :=
  ⟨X.scheme, D.action⟩

/-- Restriction preserves the separated finite-type condition without changing it.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
def RestrictedSpace.finiteSpace {G : Group k} {H : ClosedSubgroup k G}
    {X : FiniteSpace k G} (D : RestrictedSpace k H X.space) : FiniteSpace k H.group :=
  ⟨D.space k, X.finiteSeparated⟩

/-- Restriction retains the module and pulls the existing descent isomorphism along
H times X to G times X, using the section-normalized pullback compositors.
Source: Stacks 03LF (blueprint: def-sfb-equivariant-coherent-groups). -/
def IsRestriction {G : Group k} {H : ClosedSubgroup k G} {X : Space k G}
    (D : RestrictedSpace k H X) {DX : ActionGroupoidModel G.scheme X.scheme}
    (M : Coherent DX) :
    ∀ (DH : @ActionGroupoidModel (Spec (.of k)) H.group.scheme X.scheme
      H.group.group D.action),
      @Coherent (Spec (.of k)) H.group.scheme X.scheme H.group.group D.action DH → Prop := by
  letI := D.action
  exact fun DH N ↦ ∃ e : underlying M ≅ underlying N,
    ∀ (ht : (lift (fst H.group.scheme X.scheme ≫ H.map)
          (snd H.group.scheme X.scheme)).left ≫ target G.scheme X.scheme =
        target H.group.scheme (D.space k).scheme)
      (hs : (lift (fst H.group.scheme X.scheme ≫ H.map)
          (snd H.group.scheme X.scheme)).left ≫ source G.scheme X.scheme =
        source H.group.scheme (D.space k).scheme),
      (Scheme.Modules.tensorPullback
          (lift (fst H.group.scheme X.scheme ≫ H.map) (snd H.group.scheme X.scheme)).left).map
            (linearization M).hom ≫
        (Scheme.Modules.tensorPullbackSectionComp
          (lift (fst H.group.scheme X.scheme ≫ H.map) (snd H.group.scheme X.scheme)).left
          (source G.scheme X.scheme)).inv.app (underlying M) ≫
        eqToHom (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj (underlying M)) hs) ≫
        (Scheme.Modules.tensorPullback (source H.group.scheme (D.space k).scheme)).map e.hom =
      (Scheme.Modules.tensorPullbackSectionComp
          (lift (fst H.group.scheme X.scheme ≫ H.map) (snd H.group.scheme X.scheme)).left
          (target G.scheme X.scheme)).inv.app (underlying M) ≫
        eqToHom (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj (underlying M)) ht) ≫
        (Scheme.Modules.tensorPullback (target H.group.scheme (D.space k).scheme)).map e.hom ≫
        (linearization N).hom

/-- Spec k with its unique action.
Source: Milne 22d (blueprint: def-sfb-equivariant-coherent-groups). -/
@[irreducible]
def point (G : Group k) : Space k G :=
  ⟨Over.mk (𝟙 (Spec (.of k))), ModObj.trivialAction G.scheme _⟩

/-- The base point is a separated finite-type scheme over k.
Source: Stacks 01T0 (blueprint: def-sfb-equivariant-coherent-groups). -/
def finitePoint (G : Group k) : FiniteSpace k G :=
  ⟨point k G, by
    unfold Space.IsFiniteSeparated point
    change IsSeparated (𝟙 (Spec (.of k))) ∧
      LocallyOfFiniteType (𝟙 (Spec (.of k))) ∧ QuasiCompact (𝟙 (Spec (.of k)))
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The point comparison identifies precisely the already defined associated bundles.
Source: Milne 22d and Stacks 03LF
(blueprint: def-sfb-equivariant-coherent-groups). -/
def IsPointEquivalence (G : Group k)
    (D : ActionGroupoidModel G.scheme (point k G).scheme)
    (e : GZero D ≃+ RepresentationGZero k Γ(G.scheme.left, ⊤)) : Prop :=
  ∀ (V : Representation k G.scheme) (M : Coherent D),
    IsAssociated k V M → e (classOf M) = representationClass V

/-- The existing Zariski cohomology vector space, with the structure-map scalar action.
Source: Stacks 02O6 (blueprint: def-sfb-equivariant-coherent-groups). -/
def cohomologyVector {G : Group k} {X : Space k G}
    {D : ActionGroupoidModel G.scheme X.scheme} (M : Coherent D) (q : ℕ) :
    ModuleCat.{u} k :=
  letI : X.scheme.left.Over (Spec (.of k)) := ⟨X.scheme.hom⟩
  ModuleCat.of k (Scheme.Modules.H (underlying M) q)

end AlgebraicGeometry.EquivariantCoherent.ProperPushforwardData
