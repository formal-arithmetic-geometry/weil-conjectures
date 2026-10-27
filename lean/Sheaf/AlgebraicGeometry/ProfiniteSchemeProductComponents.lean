/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.ProfiniteProductMaps
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Connected.Clopen
import all Sheaf.Paper.ProfiniteTestObjectFunctor
import all Sheaf.Paper.RelativeProfiniteTestLabels
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Finite-quotient scheme products and their component topology

Source: Stacks 097D, `lemma-construct-profinite`, and 0BR1, `lemma-profinite-group`;
the explicit ring, gluing and component arguments are the agent expansion in the DAG
(blueprint: lem-sfb-profinite-scheme-product-components).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The quotient projection in every coordinate, including the empty power.
Source: Stacks 0BR1 (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerProjection (G : ProfiniteGrp.{u}) (q : ℕ) (N : OpenNormalSubgroup G) :
    C((Fin q → G), (Fin q → G ⧸ N.toSubgroup)) :=
  ⟨fun a i ↦ QuotientGroup.mk (a i),
    continuous_pi fun i ↦ QuotientGroup.continuous_mk.comp (continuous_apply i)⟩

/-- Compatible tuples in the finite quotient powers, with the subspace topology.
Source: Stacks 0BR1 (blueprint: lem-sfb-profinite-scheme-product-components). -/
def FinitePowerLimit (G : ProfiniteGrp.{u}) (q : ℕ) :=
  {a : ∀ N : OpenNormalSubgroup G, Fin q → G ⧸ N.toSubgroup //
    ∀ (N M : OpenNormalSubgroup G) (h : N ⟶ M) (i : Fin q),
      (ProfiniteGrp.toFiniteQuotientFunctor G).map h (a N i) = a M i}

/-- The compatible-family subspace topology.
Source: Stacks 0BR1 (blueprint: lem-sfb-profinite-scheme-product-components). -/
instance instTopologicalSpaceFinitePowerLimit (G : ProfiniteGrp.{u}) (q : ℕ) :
    TopologicalSpace (FinitePowerLimit G q) :=
  inferInstanceAs (TopologicalSpace {a : ∀ N : OpenNormalSubgroup G,
    Fin q → G ⧸ N.toSubgroup // ∀ (N M : OpenNormalSubgroup G) (h : N ⟶ M) (i : Fin q),
      (ProfiniteGrp.toFiniteQuotientFunctor G).map h (a N i) = a M i})

/-- The canonical map to compatible finite quotient tuples.
Source: Stacks 0BR1 (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerToLimit (G : ProfiniteGrp.{u}) (q : ℕ) :
    (Fin q → G) → FinitePowerLimit G q :=
  fun a ↦ ⟨fun N ↦ finitePowerProjection G q N a, fun _ _ _ _ ↦ rfl⟩

/-- The directed system of finite product rings, contravariant in quotient labels.
Source: Stacks 097D (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerRingDiagram (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A] :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ CommRingCat.{u} where
  obj N := .of ((Fin q → G ⧸ N.unop.toSubgroup) → A)
  map h := CommRingCat.ofHom (RingHom.pi fun a ↦ Pi.evalRingHom (fun _ ↦ A)
    (fun i ↦ (ProfiniteGrp.toFiniteQuotientFunctor G).map h.unop (a i)))
  map_id N := by
    ext a b
    change a (fun i ↦ (ProfiniteGrp.toFiniteQuotientFunctor G).map (𝟙 N.unop) (b i)) = a b
    erw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext a b
    change a (fun i ↦ (ProfiniteGrp.toFiniteQuotientFunctor G).map (g.unop ≫ f.unop)
      (b i)) = a (fun i ↦ (ProfiniteGrp.toFiniteQuotientFunctor G).map f.unop
        ((ProfiniteGrp.toFiniteQuotientFunctor G).map g.unop (b i)))
    erw [CategoryTheory.Functor.map_comp]
    rfl

/-- The specified coprojection into locally constant functions: precompose with `G^q → Q_N`.
Source: Stacks 097D (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerRingInclusion (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A]
    (N : OpenNormalSubgroup G) :
    ((Fin q → G ⧸ N.toSubgroup) → A) →+* LocallyConstant (Fin q → G) A where
  toFun f := (⟨f, IsLocallyConstant.of_discrete f⟩ :
    LocallyConstant (Fin q → G ⧸ N.toSubgroup) A).comap (finitePowerProjection G q N)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ring cocone with the prescribed finite-stage precomposition maps.
Source: Stacks 097D (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerRingCocone (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A] :
    Cocone (finitePowerRingDiagram G q A) where
  pt := .of (LocallyConstant (Fin q → G) A)
  ι := { app := fun N ↦ CommRingCat.ofHom (finitePowerRingInclusion G q A N.unop)
         naturality := fun _ _ _ ↦ rfl }

/-- The locally constant ring map induced by a coefficient map and a group homomorphism.
Source: Stacks 097D (blueprint: lem-sfb-profinite-scheme-product-components). -/
def finitePowerLCRingMap {G H : ProfiniteGrp.{u}} (ρ : H →* G) (hρ : Continuous ρ)
    (q : ℕ) {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    LocallyConstant (Fin q → G) A →+* LocallyConstant (Fin q → H) B :=
  (LocallyConstant.mapRingHom φ).comp
    (LocallyConstant.comapRingHom (ContinuousMap.piMap fun _ : Fin q ↦ ⟨ρ, hρ⟩))

/-- All canonical comparisons asserted by the node, together with their normalizations.
This packages one statement; the maps and diagrams it refers to are the actual profinite
test products and quotient/precomposition constructions, rather than chosen substitutes.
Source: Stacks 0BR1, 097D, 01YW and the DAG's explicit ring and gluing arguments
(blueprint: lem-sfb-profinite-scheme-product-components). -/
structure ProfiniteSchemeProductComparisons where
  /-- The canonical group map is a homeomorphism; it already is a group homomorphism. -/
  group_limit : ∀ G : ProfiniteGrp.{u}, IsHomeomorph (ProfiniteGrp.toLimit G)
  /-- Quotient projections generate the topology. -/
  group_topology : ∀ G : ProfiniteGrp.{u},
    Topology.IsInducing (fun g : G ↦ fun N : OpenNormalSubgroup G ↦
      (QuotientGroup.mk g : G ⧸ N.toSubgroup))
  /-- Finite powers commute with the indicated inverse limit. -/
  power_limit : ∀ (G : ProfiniteGrp.{u}) (q : ℕ), IsHomeomorph (finitePowerToLimit G q)
  /-- Finite quotient powers generate the finite power's topology. -/
  power_topology : ∀ (G : ProfiniteGrp.{u}) (q : ℕ),
    Topology.IsInducing (fun a : Fin q → G ↦ fun N : OpenNormalSubgroup G ↦
      finitePowerProjection G q N a)
  /-- The projections to the actual finite coproducts. -/
  projections : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ),
    (Functor.const (OpenNormalSubgroup G)).obj
      (profiniteProduct T (Profinite.of (Fin q → G))) ⟶ finiteLabelDiagram T G q
  /-- The scheme product is the inverse limit. -/
  scheme_limit : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ), IsLimit
    (⟨profiniteProduct T (Profinite.of (Fin q → G)), projections T G q⟩ :
      Cone (finiteLabelDiagram T G q))
  /-- The inverse-limit identification is over T. -/
  projection_base : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G),
    (projections T G q).app N ≫ Sigma.desc (fun _ : Fin q → G ⧸ N.toSubgroup ↦ 𝟙 T) =
      profiniteProductBase T (Profinite.of (Fin q → G))
  /-- Sections have their specified quotient label. -/
  projection_section : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) (a : Fin q → G),
    profiniteProductSection T (Profinite.of (Fin q → G)) a ≫ (projections T G q).app N =
      Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ T) (finitePowerProjection G q N a)
  /-- The colimit identification is induced by precomposition, with no restrictions on A. -/
  ring_colimit : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A],
    IsColimit (finitePowerRingCocone G q A)
  /-- The scheme comparison on an affine chart. -/
  affine : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A],
    profiniteProduct (Spec (.of A)) (Profinite.of (Fin q → G)) ≅
      Spec (.of (LocallyConstant (Fin q → G) A))
  /-- Constants recover the structure projection on the affine chart. -/
  affine_base : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A],
    (affine G q A).hom ≫ Spec.map
        (CommRingCat.ofHom (LocallyConstant.constRingHom (X := Fin q → G) (Y := A))) =
      profiniteProductBase (Spec (.of A)) (Profinite.of (Fin q → G))
  /-- Evaluation recovers the constant-label sections as scheme maps. -/
  affine_section : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A]
    (a : Fin q → G),
    profiniteProductSection (Spec (.of A)) (Profinite.of (Fin q → G)) a ≫
      (affine G q A).hom = Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom a))
  /-- The affine comparison has the prescribed finite-stage ring maps. -/
  affine_stage : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A]
    (N : OpenNormalSubgroup G),
    (projections (Spec (.of A)) G q).app N ≫
        sigmaSpec (fun _ : Fin q → G ⧸ N.toSubgroup ↦ CommRingCat.of A) =
      (affine G q A).hom ≫ Spec.map (CommRingCat.ofHom (finitePowerRingInclusion G q A N))
  /-- An affine open's actual inverse image is its own profinite product. -/
  open_base_change : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (A : Type u) [CommRing A] (j : Spec (.of A) ⟶ T) [IsOpenImmersion j],
    profiniteProduct (Spec (.of A)) (Profinite.of (Fin q → G)) ≅
      pullback j (profiniteProductBase T (Profinite.of (Fin q → G)))
  /-- The inverse-image comparison is over the affine open. -/
  open_base_change_fst : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (A : Type u) [CommRing A] (j : Spec (.of A) ⟶ T) [IsOpenImmersion j],
    (open_base_change T G q A j).hom ≫ pullback.fst _ _ =
      profiniteProductBase (Spec (.of A)) (Profinite.of (Fin q → G))
  /-- Its other projection is the existing map of actual test products. -/
  open_base_change_snd : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (A : Type u) [CommRing A] (j : Spec (.of A) ⟶ T) [IsOpenImmersion j],
    (open_base_change T G q A j).hom ≫ pullback.snd _ _ =
      profiniteProductMap j (𝟙 (Profinite.of (Fin q → G)))
  /-- The global topology comparison. -/
  space : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ),
    profiniteProduct T (Profinite.of (Fin q → G)) ≃ₜ T × (Fin q → G)
  /-- The homeomorphism is over the underlying space of T. -/
  space_base : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (x : profiniteProduct T (Profinite.of (Fin q → G))),
    (space T G q x).1 = profiniteProductBase T (Profinite.of (Fin q → G)) x
  /-- Constant-label sections go to their indicated fibres. -/
  space_section : ∀ (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (a : Fin q → G) (t : T),
    space T G q (profiniteProductSection T (Profinite.of (Fin q → G)) a t) = (t, a)
  /-- On every affine chart the global comparison is the evaluation-prime formula:
  the point over `𝔭` with label `a` is the prime `{h | h a ∈ 𝔭}` of `LC(P, A)`. -/
  affine_space : ∀ (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u) [CommRing A]
    (x : profiniteProduct (Spec (.of A)) (Profinite.of (Fin q → G)))
    (h : LocallyConstant (Fin q → G) A),
    h ∈ PrimeSpectrum.asIdeal (R := LocallyConstant (Fin q → G) A) ((affine G q A).hom x) ↔
      h (space (Spec (.of A)) G q x).2 ∈
        PrimeSpectrum.asIdeal (R := A) (space (Spec (.of A)) G q x).1
  /-- The components are exactly the slices, when T is connected and nonempty. -/
  component_fibres : ∀ (T : Scheme.{u}) [ConnectedSpace T] (G : ProfiniteGrp.{u}) (q : ℕ)
    (x : profiniteProduct T (Profinite.of (Fin q → G))),
    connectedComponent x = {y | (space T G q y).2 = (space T G q x).2}
  /-- The label projection is open. -/
  label_open : ∀ (T : Scheme.{u}) [ConnectedSpace T] (G : ProfiniteGrp.{u}) (q : ℕ),
    IsOpenMap (fun x ↦ (space T G q x).2)
  /-- The label projection is a quotient map. -/
  label_quotient : ∀ (T : Scheme.{u}) [ConnectedSpace T] (G : ProfiniteGrp.{u}) (q : ℕ),
    Topology.IsQuotientMap (fun x ↦ (space T G q x).2)
  /-- The connected-component quotient has exactly the profinite topology. -/
  components : ∀ (T : Scheme.{u}) [ConnectedSpace T] (G : ProfiniteGrp.{u}) (q : ℕ),
    ConnectedComponents (profiniteProduct T (Profinite.of (Fin q → G))) ≃ₜ (Fin q → G)
  /-- Normalize the component identification by the global label map. -/
  components_mk : ∀ (T : Scheme.{u}) [ConnectedSpace T] (G : ProfiniteGrp.{u}) (q : ℕ)
    (x : profiniteProduct T (Profinite.of (Fin q → G))),
    components T G q (ConnectedComponents.mk x) = (space T G q x).2
  /-- Naturality of the finite-stage comparisons, for any quotient through which ρ factors. -/
  projection_natural : ∀ (T T' : Scheme.{u}) (f : T' ⟶ T) (G H : ProfiniteGrp.{u})
    (ρ : H →* G) (hρ : Continuous ρ) (q : ℕ) (N : OpenNormalSubgroup G)
    (M : OpenNormalSubgroup H)
    (b : (Fin q → H ⧸ M.toSubgroup) → (Fin q → G ⧸ N.toSubgroup)),
    (∀ a : Fin q → H,
      b (finitePowerProjection H q M a) = finitePowerProjection G q N (fun i ↦ ρ (a i))) →
    profiniteProductMap f (labelMap G H ρ hρ q) ≫ (projections T G q).app N =
      (projections T' H q).app M ≫
        Sigma.desc (fun c ↦ f ≫ Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ T) (b c))
  /-- Naturality on affine charts, hence in particular on affine restrictions. -/
  affine_natural : ∀ (G H : ProfiniteGrp.{u}) (ρ : H →* G) (hρ : Continuous ρ)
    (q : ℕ) (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B),
    profiniteProductMap (Spec.map (CommRingCat.ofHom φ)) (labelMap G H ρ hρ q) ≫
        (affine G q A).hom =
      (affine H q B).hom ≫ Spec.map (CommRingCat.ofHom (finitePowerLCRingMap ρ hρ q φ))
  /-- Naturality under arbitrary scheme maps and continuous group homomorphisms. -/
  space_natural : ∀ (T T' : Scheme.{u}) (f : T' ⟶ T) (G H : ProfiniteGrp.{u})
    (ρ : H →* G) (hρ : Continuous ρ) (q : ℕ)
    (x : profiniteProduct T' (Profinite.of (Fin q → H))),
    space T G q (profiniteProductMap f (labelMap G H ρ hρ q) x) =
      (f (space T' H q x).1, fun i ↦ ρ ((space T' H q x).2 i))

private theorem groupLimit (G : ProfiniteGrp.{u}) : IsHomeomorph (ProfiniteGrp.toLimit G) := by
  exact (ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor G).toHomeomorph.isHomeomorph

private theorem groupTopology (G : ProfiniteGrp.{u}) :
    Topology.IsInducing (fun g : G ↦ fun N : OpenNormalSubgroup G ↦
      (QuotientGroup.mk g : G ⧸ N.toSubgroup)) := by
  have (N : OpenNormalSubgroup G) : DiscreteTopology (G.diagram.obj N) := ⟨rfl⟩
  let e (N : OpenNormalSubgroup G) : (G.diagram.obj N) ≃ₜ G ⧸ N.toSubgroup :=
    { toEquiv := Equiv.refl _
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact (Topology.IsInducing.piMap fun N ↦ (e N).isInducing).comp
    (Topology.IsInducing.subtypeVal.comp (groupLimit G).isInducing)

private theorem powerLimit (G : ProfiniteGrp.{u}) (q : ℕ) :
    IsHomeomorph (finitePowerToLimit G q) := by
  have : T2Space (FinitePowerLimit G q) :=
    inferInstanceAs (T2Space {a : ∀ N : OpenNormalSubgroup G,
      Fin q → G ⧸ N.toSubgroup // ∀ (N M : OpenNormalSubgroup G) (h : N ⟶ M) (i : Fin q),
        (ProfiniteGrp.toFiniteQuotientFunctor G).map h (a N i) = a M i})
  apply isHomeomorph_iff_continuous_bijective.mpr
  constructor
  · exact (continuous_pi fun N ↦ (finitePowerProjection G q N).continuous).subtype_mk _
  constructor
  · intro a b h
    funext i
    apply ProfiniteGrp.toLimit_injective G
    apply Subtype.ext
    funext N
    exact congrArg (fun z : FinitePowerLimit G q ↦ z.val N i) h
  · intro a
    let b (i : Fin q) : (ProfiniteGrp.limit (ProfiniteGrp.diagram G)) :=
      ⟨fun N ↦ a.val N i, fun {N M} h ↦ a.property N M h i⟩
    choose c hc using fun i ↦ ProfiniteGrp.toLimit_surjective G (b i)
    refine ⟨c, Subtype.ext ?_⟩
    funext N i
    exact congrArg (fun z : (ProfiniteGrp.limit (ProfiniteGrp.diagram G)) ↦ z.val N) (hc i)

private theorem powerTopology (G : ProfiniteGrp.{u}) (q : ℕ) :
    Topology.IsInducing (fun a : Fin q → G ↦ fun N : OpenNormalSubgroup G ↦
      finitePowerProjection G q N a) := by
  exact Topology.IsInducing.subtypeVal.comp (powerLimit G q).isInducing

private noncomputable def quotientPowers (G : ProfiniteGrp.{u}) (q : ℕ) :
    OpenNormalSubgroup G ⥤ Profinite.{u} where
  obj N := Profinite.of (Fin q → G ⧸ N.toSubgroup)
  map h := CompHausLike.ofHom _
    ⟨fun a i ↦ (ProfiniteGrp.toFiniteQuotientFunctor G).map h (a i),
      continuous_of_discreteTopology⟩
  map_id N := by
    ext a i
    change (ProfiniteGrp.toFiniteQuotientFunctor G).map (𝟙 N) (a i) = a i
    exact QuotientGroup.map_id_apply N.toSubgroup (leOfHom (𝟙 N)) (a i)
  map_comp f g := by
    ext a i
    change (ProfiniteGrp.toFiniteQuotientFunctor G).map (f ≫ g) (a i) = _
    erw [Functor.map_comp]
    rfl

private noncomputable def quotientPowerCone (G : ProfiniteGrp.{u}) (q : ℕ) :
    Cone (quotientPowers G q) where
  pt := Profinite.of (Fin q → G)
  π := { app := fun N ↦ CompHausLike.ofHom _ (finitePowerProjection G q N)
         naturality := fun _ _ _ ↦ rfl }

private theorem quotientPowerSurjective (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) : Function.Surjective (finitePowerProjection G q N) := by
  intro a
  choose b hb using fun i ↦ QuotientGroup.mk_surjective (a i)
  exact ⟨b, funext hb⟩

private noncomputable def quotientPowerIsLimit (G : ProfiniteGrp.{u}) (q : ℕ) :
    IsLimit (quotientPowerCone G q) := by
  let e := IsHomeomorph.homeomorph _ (powerLimit G q)
  let a (s : Cone (quotientPowers G q)) : C(s.pt, FinitePowerLimit G q) :=
    ⟨fun x ↦ ⟨fun N ↦ s.π.app N x, fun N M h i ↦
      congrArg (fun f : s.pt ⟶ (quotientPowers G q).obj M ↦ f x i) (s.w h)⟩,
      (continuous_pi fun N ↦ (s.π.app N).hom.hom.continuous).subtype_mk _⟩
  refine
    { lift := fun s ↦ CompHausLike.ofHom _
        ⟨fun x ↦ e.symm (a s x), e.symm.continuous.comp (a s).continuous⟩
      fac := ?_
      uniq := ?_ }
  · intro s N
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact congrArg (fun z : FinitePowerLimit G q ↦ z.val N i) (e.apply_symm_apply (a s x))
  · intro s m hm
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    apply congrFun (e.injective ?_) i
    apply Subtype.ext
    funext N j
    have h := congrArg (fun f : s.pt ⟶ (quotientPowers G q).obj N ↦ f x j) (hm N)
    change finitePowerProjection G q N (m x) j = _ at h
    exact h.trans (congrArg (fun z : FinitePowerLimit G q ↦ z.val N j)
      (e.apply_symm_apply (a s x))).symm

private theorem quotientIndicesNonempty (G : ProfiniteGrp.{u}) :
    Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩

attribute [local instance] quotientIndicesNonempty

private noncomputable def ringColimit (G : ProfiniteGrp.{u}) (q : ℕ)
    (A : Type u) [CommRing A] : IsColimit (finitePowerRingCocone G q A) := by
  have : ReflectsColimitsOfShape (OpenNormalSubgroup G)ᵒᵖ (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (CategoryTheory.forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro f
    obtain ⟨N, g, hg⟩ := Profinite.exists_locallyConstant
      (quotientPowerCone G q) (quotientPowerIsLimit G q) f
    refine ⟨op N, g.toFun, ?_⟩
    exact hg
  · intro N f g h
    refine ⟨N, 𝟙 N, ?_⟩
    suffices f = g by simpa using this
    funext a
    obtain ⟨b, hb⟩ := quotientPowerSurjective G q N.unop a
    have hh := congrArg (fun k : LocallyConstant (Fin q → G) A ↦ k b) h
    change f (finitePowerProjection G q N.unop b) =
      g (finitePowerProjection G q N.unop b) at hh
    simpa only [hb] using hh

private theorem specMap_coeff (P : Profinite.{u}) {A B R : Type*}
    [CommRing A] [CommRing B] [CommRing R] (φ : R →+* A)
    (k : LocallyConstant P A →+* B) :
    LocallyConstant.specMap (k.comp (LocallyConstant.mapRingHom φ)) =
      LocallyConstant.specMap k := by
  ext p
  obtain ⟨⟨a, t⟩, ht⟩ := LocallyConstant.toPrimeSpectrum_surjective
    (PrimeSpectrum.comap k p)
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := R)).symm
      (PrimeSpectrum.comap (k.comp (LocallyConstant.mapRingHom φ)) p)).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm
      (PrimeSpectrum.comap k p)).1
  rw [PrimeSpectrum.comap_comp_apply, ← ht]
  have hc : PrimeSpectrum.comap (LocallyConstant.mapRingHom φ)
      (LocallyConstant.toPrimeSpectrum (a, t)) =
      LocallyConstant.toPrimeSpectrum (a, PrimeSpectrum.comap φ t) := by
    ext h
    rfl
  rw [hc]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := R)).symm
    (LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := R)
      (a, PrimeSpectrum.comap φ t))).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm
      (LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A) (a, t))).1
  simp only [Homeomorph.symm_apply_apply]

private noncomputable abbrev lcCoeff (P : Profinite.{u}) (A : Type u) [CommRing A] :
    CommRingCat.of (LocallyConstant P ℤ) ⟶ CommRingCat.of (LocallyConstant P A) :=
  CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom A))

private noncomputable abbrev lcConst (P : Profinite.{u}) (A : Type u) [CommRing A] :
    CommRingCat.of A ⟶ CommRingCat.of (LocallyConstant P A) :=
  CommRingCat.ofHom (LocallyConstant.constRingHom (X := P) (Y := A))

private noncomputable abbrev intMap (A : Type u) [CommRing A] :
    CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of A :=
  CommRingCat.ofHom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom)

private theorem lcPushout (P : Profinite.{u}) (A : Type u) [CommRing A] :
    IsPushout (intMap (LocallyConstant P ℤ)) (intMap A) (lcCoeff P A) (lcConst P A) := by
  have hw : intMap (LocallyConstant P ℤ) ≫ lcCoeff P A = intMap A ≫ lcConst P A := by
    ext z p
    simp only [lcCoeff, lcConst, intMap, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom]
    simp
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (LocallyConstant.liftPrimeSpectrum s.inr.hom
      (LocallyConstant.specMap s.inl.hom))) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply LocallyConstant.ringHom_ext_of_specMap
    · exact RingHom.ext_int _ _
    · change LocallyConstant.specMap ((LocallyConstant.liftPrimeSpectrum s.inr.hom
        (LocallyConstant.specMap s.inl.hom)).comp
        (LocallyConstant.mapRingHom (Int.castRingHom A))) = _
      rw [specMap_coeff, LocallyConstant.specMap_liftPrimeSpectrum]
  · intro s
    ext a
    exact LocallyConstant.liftPrimeSpectrum_algebraMap _ _ a
  · intro s m h₁ h₂
    apply CommRingCat.hom_ext
    apply LocallyConstant.ringHom_ext_of_specMap
    · change m.hom.comp (LocallyConstant.constRingHom (X := P) (Y := A)) = _
      rw [show m.hom.comp (LocallyConstant.constRingHom (X := P) (Y := A)) = s.inr.hom
        from congrArg CommRingCat.Hom.hom h₂]
      ext a
      exact (LocallyConstant.liftPrimeSpectrum_algebraMap _ _ a).symm
    · change LocallyConstant.specMap m.hom = LocallyConstant.specMap
        (LocallyConstant.liftPrimeSpectrum s.inr.hom (LocallyConstant.specMap s.inl.hom))
      rw [LocallyConstant.specMap_liftPrimeSpectrum]
      have h := congrArg (fun k ↦ LocallyConstant.specMap (CommRingCat.Hom.hom k)) h₁
      change LocallyConstant.specMap (m.hom.comp
        (LocallyConstant.mapRingHom (Int.castRingHom A))) = _ at h
      rw [specMap_coeff] at h
      exact h

private theorem affinePullback (P : Profinite.{u}) (A : Type u) [CommRing A] :
    IsPullback (Spec.map (lcCoeff P A)) (Spec.map (lcConst P A))
      (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P))
      (ProEtale.toSpecZ (Spec (.of A))) := by
  have h := (lcPushout P A).op.map Scheme.Spec
  have h₁ : ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P) =
      Spec.map (intMap (LocallyConstant P ℤ)) := specULiftZIsTerminal.hom_ext _ _
  have h₂ : ProEtale.toSpecZ (Spec (.of A)) = Spec.map (intMap A) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [h₁, h₂]
  exact h.flip

private noncomputable def affineIso (P : Profinite.{u}) (A : Type u) [CommRing A] :
    profiniteProduct (Spec (.of A)) P ≅ Spec (.of (LocallyConstant P A)) :=
  (affinePullback P A).isoPullback.symm

private theorem affineIso_base (P : Profinite.{u}) (A : Type u) [CommRing A] :
    (affineIso P A).hom ≫ Spec.map (lcConst P A) =
      profiniteProductBase (Spec (.of A)) P := by
  exact (affinePullback P A).isoPullback_inv_snd

private theorem affineIso_label (P : Profinite.{u}) (A : Type u) [CommRing A] :
    (affineIso P A).hom ≫ Spec.map (lcCoeff P A) =
      pullback.fst (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P))
        (ProEtale.toSpecZ (Spec (.of A))) := by
  exact (affinePullback P A).isoPullback_inv_fst

private theorem toSpecZ_intMap (A : Type u) [CommRing A] :
    ProEtale.toSpecZ (Spec (.of A)) = Spec.map (intMap A) :=
  specULiftZIsTerminal.hom_ext _ _

private noncomputable abbrev productLabel (T : Scheme.{u}) (P : Profinite.{u}) :
    profiniteProduct T P ⟶ ProEtale.profiniteToScheme.obj P :=
  pullback.fst _ _

private theorem section_base (T : Scheme.{u}) (P : Profinite.{u}) (p : P) :
    profiniteProductSection T P p ≫ profiniteProductBase T P = 𝟙 T := by
  exact pullback.lift_snd _ _ _

private theorem section_label (T : Scheme.{u}) (P : Profinite.{u}) (p : P) :
    profiniteProductSection T P p ≫ productLabel T P = ProEtale.toSpecZ T ≫
      Spec.map (CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp (LocallyConstant.evalRingHom p))) := by
  exact pullback.lift_fst _ _ _

private theorem affineIso_section (P : Profinite.{u}) (A : Type u) [CommRing A] (a : P) :
    profiniteProductSection (Spec (.of A)) P a ≫ (affineIso P A).hom =
      Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom a)) := by
  apply (affinePullback P A).hom_ext
  · rw [Category.assoc, affineIso_label]
    change profiniteProductSection _ _ _ ≫ productLabel _ _ = _
    rw [section_label, toSpecZ_intMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, affineIso_base, section_base, ← Spec.map_comp, ← Spec.map_id]
    rfl

private noncomputable def finiteSectionsIsColimit (T : Scheme.{u}) (P : Profinite.{u}) [Finite P] :
    IsColimit (Cofan.mk (profiniteProduct T P) (profiniteProductSection T P)) := by
  let j := (ProEtale.finite_labels T P).choose
  let hj := (ProEtale.finite_labels T P).choose_spec.1.some
  have hbase := (ProEtale.finite_labels T P).choose_spec.2.1
  have he : j = profiniteProductSection T P := by
    funext a
    apply pullback.hom_ext
    · change j a ≫ productLabel T P = profiniteProductSection T P a ≫ productLabel T P
      rw [section_label]
      have hh := (hbase a).2
      change j a ≫ productLabel T P = _ at hh
      rw [hh]
      congr 2
    · change j a ≫ profiniteProductBase T P =
        profiniteProductSection T P a ≫ profiniteProductBase T P
      rw [section_base]
      exact (hbase a).1
  change IsColimit (Cofan.mk (profiniteProduct T P) j) at hj
  rw [he] at hj
  exact hj

private noncomputable def finiteSectionsIso (T : Scheme.{u}) (P : Profinite.{u}) [Finite P] :
    profiniteProduct T P ≅ ∐ (fun _ : P ↦ T) :=
  (finiteSectionsIsColimit T P).coconePointUniqueUpToIso (coproductIsCoproduct (fun _ : P ↦ T))

private theorem finiteSectionsIso_section (T : Scheme.{u}) (P : Profinite.{u}) [Finite P]
    (a : P) : profiniteProductSection T P a ≫ (finiteSectionsIso T P).hom =
      Sigma.ι (fun _ : P ↦ T) a :=
  (finiteSectionsIsColimit T P).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun _ : P ↦ T)) ⟨a⟩

private theorem productMap_base {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProductMap f a ≫ profiniteProductBase T P =
      profiniteProductBase T' P' ≫ f := by
  simp [profiniteProductMap, profiniteProductBase, ProEtale.profiniteToProEtOf,
    MorphismProperty.Over.pullback]

private theorem productMap_comp {T₀ T₁ T₂ : Scheme.{u}} (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂)
    {P₀ P₁ P₂ : Profinite.{u}} (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) :
    profiniteProductMap f a ≫ profiniteProductMap g b =
      profiniteProductMap (f ≫ g) (a ≫ b) := by
  apply pullback.hom_ext <;>
    simp [profiniteProductMap, Category.assoc, ← Functor.map_comp]

private theorem productMap_label {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProductMap f a ≫ productLabel T P =
      productLabel T' P' ≫ ProEtale.profiniteToScheme.map a := by
  exact pullback.lift_fst _ _ _

private theorem product_hom_ext {T : Scheme.{u}} {P : Profinite.{u}} {Z : Scheme.{u}}
    {a b : Z ⟶ profiniteProduct T P}
    (h₁ : a ≫ productLabel T P = b ≫ productLabel T P)
    (h₂ : a ≫ profiniteProductBase T P = b ≫ profiniteProductBase T P) : a = b :=
  pullback.hom_ext h₁ h₂

private theorem productMap_section {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) (p : P') :
    profiniteProductSection T' P' p ≫ profiniteProductMap f a =
      f ≫ profiniteProductSection T P (a p) := by
  apply product_hom_ext
  · rw [Category.assoc, productMap_label, ← Category.assoc, section_label]
    conv_rhs => rw [Category.assoc, section_label, ← Category.assoc, ProEtale.comp_toSpecZ]
    change (ProEtale.toSpecZ T' ≫ Spec.map _) ≫ Spec.map _ =
      ProEtale.toSpecZ T' ≫ Spec.map _
    rw [Category.assoc, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, productMap_base, ← Category.assoc, section_base,
      Category.assoc, section_base, Category.id_comp, Category.comp_id]

private theorem finiteSectionsIso_base (T : Scheme.{u}) (P : Profinite.{u}) [Finite P] :
    (finiteSectionsIso T P).hom ≫ Sigma.desc (fun _ : P ↦ 𝟙 T) =
      profiniteProductBase T P := by
  apply (finiteSectionsIsColimit T P).hom_ext
  rintro ⟨p⟩
  change profiniteProductSection T P p ≫ _ = profiniteProductSection T P p ≫ _
  rw [← Category.assoc, finiteSectionsIso_section, Sigma.ι_desc]
  rw [section_base]

private theorem finiteSectionsIso_natural {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} [Finite P] [Finite P'] (a : P' ⟶ P) :
    profiniteProductMap f a ≫ (finiteSectionsIso T P).hom =
      (finiteSectionsIso T' P').hom ≫
        Sigma.desc (fun p : P' ↦ f ≫ Sigma.ι (fun _ : P ↦ T) (a p)) := by
  apply (finiteSectionsIsColimit T' P').hom_ext
  rintro ⟨p⟩
  change profiniteProductSection T' P' p ≫ _ = profiniteProductSection T' P' p ≫ _
  rw [← Category.assoc, productMap_section, Category.assoc, finiteSectionsIso_section,
    ← Category.assoc, finiteSectionsIso_section, Sigma.ι_desc]

private theorem affineIso_natural {P P' : Profinite.{u}} (a : P' ⟶ P)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    profiniteProductMap (Spec.map (CommRingCat.ofHom φ)) a ≫ (affineIso P A).hom =
      (affineIso P' B).hom ≫ Spec.map (CommRingCat.ofHom
        ((LocallyConstant.mapRingHom φ).comp (LocallyConstant.comapRingHom a.hom.hom))) := by
  apply (affinePullback P A).hom_ext
  · rw [Category.assoc, affineIso_label]
    change profiniteProductMap _ _ ≫ productLabel _ _ = _
    rw [productMap_label]
    have hh : (affineIso P' B).hom ≫ Spec.map (lcCoeff P' B) =
        productLabel (Spec (.of B)) P' := affineIso_label P' B
    rw [← hh, Category.assoc, Category.assoc]
    congr 1
    change Spec.map (lcCoeff P' B) ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((LocallyConstant.mapRingHom (Int.castRingHom B)).comp
        (LocallyConstant.comapRingHom a.hom.hom))) =
      Spec.map (CommRingCat.ofHom
        (((LocallyConstant.mapRingHom φ).comp (LocallyConstant.comapRingHom a.hom.hom)).comp
          (LocallyConstant.mapRingHom (Int.castRingHom A))))
    congr 2
    ext h p
    simp
  · rw [Category.assoc, affineIso_base, productMap_base,
      ← affineIso_base P' B, Category.assoc, Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

private noncomputable def productBaseChange {T T' : Scheme.{u}} (f : T' ⟶ T)
    (P : Profinite.{u}) :
    profiniteProduct T' P ≅ pullback f (profiniteProductBase T P) :=
  ((pullbackSymmetry f (pullback.snd
      (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P)) (ProEtale.toSpecZ T))) ≪≫
    pullbackLeftPullbackSndIso
      (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P)) (ProEtale.toSpecZ T) f ≪≫
      pullback.congrHom rfl (ProEtale.comp_toSpecZ f)).symm

private theorem productBaseChange_fst {T T' : Scheme.{u}} (f : T' ⟶ T)
    (P : Profinite.{u}) :
    (productBaseChange f P).hom ≫ pullback.fst _ _ = profiniteProductBase T' P := by
  change (productBaseChange f P).hom ≫ pullback.fst f
    (pullback.snd (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P))
      (ProEtale.toSpecZ T)) =
    pullback.snd (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P)) (ProEtale.toSpecZ T')
  simp [productBaseChange]

private theorem productBaseChange_snd {T T' : Scheme.{u}} (f : T' ⟶ T)
    (P : Profinite.{u}) :
    (productBaseChange f P).hom ≫ pullback.snd _ _ = profiniteProductMap f (𝟙 P) := by
  apply product_hom_ext
  · change (productBaseChange f P).hom ≫ pullback.snd f
        (pullback.snd (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P))
          (ProEtale.toSpecZ T)) ≫
        pullback.fst (ProEtale.toSpecZ (ProEtale.profiniteToScheme.obj P))
          (ProEtale.toSpecZ T) = _
    simp [productBaseChange, productLabel, profiniteProductMap]
    rfl
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      productBaseChange_fst, productMap_base]

private noncomputable def spaceMap (T : Scheme.{u}) (P : Profinite.{u}) :
    C(profiniteProduct T P, T × P) :=
  (profiniteProductBase T P).base.hom.prodMk (ProEtale.label T P)

private theorem spaceMap_natural {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) (x : profiniteProduct T' P') :
    spaceMap T P (profiniteProductMap f a x) =
      (f (spaceMap T' P' x).1, a (spaceMap T' P' x).2) := by
  apply Prod.ext
  · exact congrArg (fun k : profiniteProduct T' P' ⟶ T ↦ k x) (productMap_base f a)
  · change ProEtale.label T P (profiniteProductMap f a x) = _
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      ((profiniteProductMap f a ≫ productLabel T P) x)).1 = _
    rw [productMap_label]
    obtain ⟨⟨p, t⟩, ht⟩ := LocallyConstant.toPrimeSpectrum_surjective (productLabel T' P' x)
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      (PrimeSpectrum.comap (LocallyConstant.comapRingHom a.hom.hom)
        (productLabel T' P' x))).1 = _
    change _ = a (((LocallyConstant.homeomorphPrimeSpectrum (T := P') (R := ℤ)).symm
      (productLabel T' P' x)).1)
    rw [← ht]
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      (LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ) (a p, t))).1 =
      a (((LocallyConstant.homeomorphPrimeSpectrum (T := P') (R := ℤ)).symm
        (LocallyConstant.homeomorphPrimeSpectrum (T := P') (R := ℤ) (p, t))).1)
    simp only [Homeomorph.symm_apply_apply]

private noncomputable def affineSpace (P : Profinite.{u}) (A : Type u) [CommRing A] :
    profiniteProduct (Spec (.of A)) P ≃ₜ Spec (.of A) × P :=
  (Scheme.homeoOfIso (affineIso P A)).trans
    ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm.trans
      (Homeomorph.prodComm _ _))

private theorem affineSpace_eq (P : Profinite.{u}) (A : Type u) [CommRing A] :
    ⇑(affineSpace P A) = spaceMap (Spec (.of A)) P := by
  funext x
  apply Prod.ext
  · change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm
      ((affineIso P A).hom x)).2 = profiniteProductBase (Spec (.of A)) P x
    rw [LocallyConstant.homeomorphPrimeSpectrum_symm_snd]
    exact congrArg (fun k : profiniteProduct (Spec (.of A)) P ⟶ Spec (.of A) ↦ k x)
      (affineIso_base P A)
  · change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm
      ((affineIso P A).hom x)).1 = ProEtale.label (Spec (.of A)) P x
    have h := specMap_coeff P (Int.castRingHom A) (RingHom.id (LocallyConstant P A))
    have hx := congrArg (fun k ↦ k ((affineIso P A).hom x)) h
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      (Spec.map (lcCoeff P A) ((affineIso P A).hom x))).1 =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).symm
        ((affineIso P A).hom x)).1 at hx
    rw [← hx]
    change _ = ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      (productLabel (Spec (.of A)) P x)).1
    exact congrArg (fun k : profiniteProduct (Spec (.of A)) P ⟶
      ProEtale.profiniteToScheme.obj P ↦
        ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm (k x)).1)
      (affineIso_label P A)

private theorem affine_space_formula (P : Profinite.{u}) (A : Type u) [CommRing A]
    (x : profiniteProduct (Spec (.of A)) P) (h : LocallyConstant P A) :
    h ∈ ((affineIso P A).hom x).asIdeal ↔
      h (spaceMap (Spec (.of A)) P x).2 ∈ (spaceMap (Spec (.of A)) P x).1.asIdeal := by
  rw [← affineSpace_eq]
  have hx := (LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := A)).apply_symm_apply
    ((affineIso P A).hom x)
  conv_lhs => rw [← hx]
  rfl

private theorem quotientPowersFinite (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) : Finite ((quotientPowers G q).obj N) :=
  inferInstanceAs (Finite (Fin q → G ⧸ N.toSubgroup))

attribute [local instance] quotientPowersFinite

private noncomputable def schemeDiagramIso (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    (quotientPowers G q) ⋙
        (ProEtale.profiniteToProEtOf T ⋙ Scheme.ProEt.forget T ⋙ Over.forget T) ≅
      finiteLabelDiagram T G q :=
  NatIso.ofComponents (fun N ↦ finiteSectionsIso T
    (Profinite.of (Fin q → G ⧸ N.toSubgroup))) (by
      intro N M h
      exact finiteSectionsIso_natural (𝟙 T) ((quotientPowers G q).map h))

private noncomputable def projections (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    (Functor.const (OpenNormalSubgroup G)).obj
      (profiniteProduct T (Profinite.of (Fin q → G))) ⟶ finiteLabelDiagram T G q :=
  ((ProEtale.profiniteToProEtOf T ⋙ Scheme.ProEt.forget T ⋙ Over.forget T).mapCone
    (quotientPowerCone G q)).π ≫ (schemeDiagramIso T G q).hom

private noncomputable def schemeLimit (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    IsLimit (⟨profiniteProduct T (Profinite.of (Fin q → G)), projections T G q⟩ :
      Cone (finiteLabelDiagram T G q)) := by
  have : IsConnected (OpenNormalSubgroup G) := IsCofiltered.isConnected _
  let F := ProEtale.profiniteToProEt ⋙ Scheme.ProEt.forget ProEtale.specZ.{u}
  have hsch : IsLimit (ProEtale.profiniteToScheme.mapCone (quotientPowerCone G q)) :=
    isLimitOfPreserves Scheme.Spec
      (ProEtale.lc_limit (quotientPowerCone G q) (quotientPowerIsLimit G q)
        (quotientPowerSurjective G q)).some
  have hover : IsLimit (F.mapCone (quotientPowerCone G q)) :=
    isLimitOfReflects (Over.forget ProEtale.specZ) hsch
  let h := isLimitOfPreserves (Over.pullback (ProEtale.toSpecZ T)) hover
  exact (IsLimit.postcomposeHomEquiv (schemeDiagramIso T G q) _).symm
    (isLimitOfPreserves (Over.forget T) h)

private theorem projections_section (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) (a : Fin q → G) :
    profiniteProductSection T (Profinite.of (Fin q → G)) a ≫ (projections T G q).app N =
      Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ T) (finitePowerProjection G q N a) := by
  change profiniteProductSection _ _ _ ≫
    profiniteProductMap (𝟙 T) ((quotientPowerCone G q).π.app N) ≫ _ = _
  rw [← Category.assoc, productMap_section, Category.id_comp]
  exact finiteSectionsIso_section T (Profinite.of (Fin q → G ⧸ N.toSubgroup))
    (finitePowerProjection G q N a)

private theorem projections_base (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) :
    (projections T G q).app N ≫ Sigma.desc (fun _ : Fin q → G ⧸ N.toSubgroup ↦ 𝟙 T) =
      profiniteProductBase T (Profinite.of (Fin q → G)) := by
  change (profiniteProductMap (𝟙 T) ((quotientPowerCone G q).π.app N) ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ profiniteProductMap (𝟙 T)
      ((quotientPowerCone G q).π.app N) ≫ k)
      (finiteSectionsIso_base T ((quotientPowers G q).obj N))).trans
        ((productMap_base (𝟙 T) ((quotientPowerCone G q).π.app N)).trans
          (Category.comp_id _)))

private theorem chart_lift {T : Scheme.{u}} {A : Type u} [CommRing A]
    (j : Spec (.of A) ⟶ T) (P : Profinite.{u}) (x : profiniteProduct T P)
    (t : Spec (.of A)) (ht : j t = profiniteProductBase T P x) :
    ∃ a : profiniteProduct (Spec (.of A)) P,
      profiniteProductBase (Spec (.of A)) P a = t ∧ profiniteProductMap j (𝟙 P) a = x := by
  obtain ⟨z, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := profiniteProductBase T P) t x ht
  refine ⟨(productBaseChange j P).inv z, ?_, ?_⟩
  · have h := productBaseChange_fst j P
    have hh := congrArg (fun k ↦ (productBaseChange j P).inv ≫ k) h
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hh
    exact (congrArg (fun k : pullback j (profiniteProductBase T P) ⟶ Spec (.of A) ↦ k z)
      hh).symm.trans h₁
  · have h := productBaseChange_snd j P
    have hh := congrArg (fun k ↦ (productBaseChange j P).inv ≫ k) h
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hh
    exact (congrArg (fun k : pullback j (profiniteProductBase T P) ⟶ profiniteProduct T P ↦
      k z) hh).symm.trans h₂

private theorem chart_open {T : Scheme.{u}} {A : Type u} [CommRing A]
    (j : Spec (.of A) ⟶ T) [IsOpenImmersion j] (P : Profinite.{u}) :
    IsOpenMap (profiniteProductMap j (𝟙 P)) := by
  rw [← productBaseChange_snd]
  exact (Scheme.Hom.isOpenEmbedding (pullback.snd j (profiniteProductBase T P))).isOpenMap.comp
    (Scheme.homeoOfIso (productBaseChange j P)).isOpenMap

private theorem spaceMap_bijective (T : Scheme.{u}) (P : Profinite.{u}) :
    Function.Bijective (spaceMap T P) := by
  constructor
  · intro x y h
    let U := T.affineOpenCover
    obtain ⟨t, ht⟩ := U.covers (profiniteProductBase T P x)
    obtain ⟨a, ha, hax⟩ := chart_lift (U.f _) P x t ht
    have hbase : profiniteProductBase T P x = profiniteProductBase T P y :=
      congrArg Prod.fst h
    obtain ⟨b, hb, hby⟩ := chart_lift (U.f _) P y t (ht.trans hbase)
    have hab : affineSpace P (U.X (U.idx (profiniteProductBase T P x))) a =
        affineSpace P (U.X (U.idx (profiniteProductBase T P x))) b := by
      rw [affineSpace_eq]
      apply Prod.ext
      · exact ha.trans hb.symm
      · have hx := congrArg Prod.snd (spaceMap_natural (U.f _) (𝟙 P) a)
        have hy := congrArg Prod.snd (spaceMap_natural (U.f _) (𝟙 P) b)
        change (spaceMap T P (profiniteProductMap (U.f _) (𝟙 P) a)).2 =
          (spaceMap _ P a).2 at hx
        change (spaceMap T P (profiniteProductMap (U.f _) (𝟙 P) b)).2 =
          (spaceMap _ P b).2 at hy
        exact hx.symm.trans ((congrArg (fun z : profiniteProduct T P ↦
          (spaceMap T P z).2) hax).trans ((congrArg Prod.snd h).trans
            ((congrArg (fun z : profiniteProduct T P ↦
              (spaceMap T P z).2) hby).symm.trans hy)))
    exact hax.symm.trans ((congrArg (profiniteProductMap (U.f _) (𝟙 P))
      ((affineSpace P _).injective hab)).trans hby)
  · rintro ⟨t, p⟩
    let U := T.affineOpenCover
    obtain ⟨a, ha⟩ := U.covers t
    let x := (affineSpace P (U.X (U.idx t))).symm (a, p)
    refine ⟨profiniteProductMap (U.f _) (𝟙 P) x, ?_⟩
    rw [spaceMap_natural, ← affineSpace_eq]
    have hx : affineSpace P (U.X (U.idx t)) x = (a, p) :=
      (affineSpace P _).apply_symm_apply _
    rw [hx, ha]
    rfl

private theorem spaceMap_open (T : Scheme.{u}) (P : Profinite.{u}) :
    IsOpenMap (spaceMap T P) := by
  intro V hV
  apply isOpen_iff_forall_mem_open.mpr
  rintro _ ⟨x, hx, rfl⟩
  let U := T.affineOpenCover
  obtain ⟨t, ht⟩ := U.covers (profiniteProductBase T P x)
  obtain ⟨a, ha, hax⟩ := chart_lift (U.f _) P x t ht
  let j := U.f (U.idx (profiniteProductBase T P x))
  let k := profiniteProductMap j (𝟙 P)
  let e := affineSpace P (U.X (U.idx (profiniteProductBase T P x)))
  let m : Spec (U.X (U.idx (profiniteProductBase T P x))) × P → T × P :=
    Prod.map j id
  refine ⟨m '' (e '' (k ⁻¹' V)), ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨k b, hb, ?_⟩
    exact (spaceMap_natural j (𝟙 P) b).trans
      (congrArg m (congrFun (affineSpace_eq P _) b).symm)
  · exact ((Scheme.Hom.isOpenEmbedding j).isOpenMap.prodMap IsOpenMap.id) _
      (e.isOpenMap _ (hV.preimage k.continuous))
  · refine ⟨e a, ⟨a, ?_, rfl⟩, ?_⟩
    · change profiniteProductMap (U.f _) (𝟙 P) a ∈ V
      exact Set.mem_of_eq_of_mem hax hx
    · exact ((spaceMap_natural j (𝟙 P) a).trans
        (congrArg m (congrFun (affineSpace_eq P _) a).symm)).symm.trans
          (congrArg (spaceMap T P) hax)

private noncomputable def spaceIso (T : Scheme.{u}) (P : Profinite.{u}) :
    profiniteProduct T P ≃ₜ T × P :=
  IsHomeomorph.homeomorph _
    ⟨(spaceMap T P).continuous, spaceMap_open T P, spaceMap_bijective T P⟩

private theorem spaceIso_section (T : Scheme.{u}) (P : Profinite.{u}) (a : P) (t : T) :
    spaceIso T P (profiniteProductSection T P a t) = (t, a) := by
  apply Prod.ext
  · exact congrArg (fun k : T ⟶ T ↦ k t) (section_base T P a)
  · change ProEtale.label T P (profiniteProductSection T P a t) = a
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      ((profiniteProductSection T P a ≫ productLabel T P) t)).1 = a
    rw [section_label]
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := P) (R := ℤ)).symm
      (LocallyConstant.toPrimeSpectrum
        (a, PrimeSpectrum.comap ULift.ringEquiv.symm.toRingHom (ProEtale.toSpecZ T t)))).1 = a
    exact congrArg Prod.fst ((LocallyConstant.homeomorphPrimeSpectrum
      (T := P) (R := ℤ)).symm_apply_apply _)

private theorem componentFibres (T : Scheme.{u}) [ConnectedSpace T] (P : Profinite.{u})
    (x : profiniteProduct T P) :
    connectedComponent x = {y | (spaceIso T P y).2 = (spaceIso T P x).2} := by
  let e := spaceIso T P
  have hprod : connectedComponent (e x) =
      {p : T × P | p.2 = (e x).2} := by
    rw [connectedComponent_prod, PreconnectedSpace.connectedComponent_eq_univ,
      connectedComponent_eq_singleton]
    ext p
    simp
  apply Set.Subset.antisymm
  · intro y hy
    have h := e.continuous.mapsTo_connectedComponent x hy
    rw [hprod] at h
    exact h
  · intro y hy
    have h : e y ∈ connectedComponent (e x) := by rwa [hprod]
    have hh := e.symm.continuous.mapsTo_connectedComponent (e x) h
    simpa only [e.symm_apply_apply] using hh

private theorem labelOpen (T : Scheme.{u}) (P : Profinite.{u}) :
    IsOpenMap (fun x ↦ (spaceIso T P x).2) :=
  isOpenMap_snd.comp (spaceIso T P).isOpenMap

private theorem labelQuotient (T : Scheme.{u}) [ConnectedSpace T] (P : Profinite.{u}) :
    Topology.IsQuotientMap (fun x ↦ (spaceIso T P x).2) :=
  isQuotientMap_snd.comp (spaceIso T P).isQuotientMap

private noncomputable def componentIso (T : Scheme.{u}) [ConnectedSpace T] (P : Profinite.{u}) :
    ConnectedComponents (profiniteProduct T P) ≃ₜ P := by
  let f : profiniteProduct T P → P := fun x ↦ (spaceIso T P x).2
  have hf : Continuous f := continuous_snd.comp (spaceIso T P).continuous
  let g := hf.connectedComponentsLift
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
      apply ConnectedComponents.coe_eq_coe'.mpr
      rw [componentFibres]
      exact hab
    · intro p
      obtain ⟨x, hx⟩ := (labelQuotient T P).surjective p
      exact ⟨ConnectedComponents.mk x, hx⟩
  have hq : Topology.IsQuotientMap g :=
    ConnectedComponents.isQuotientMap_coe.of_comp_isQuotientMap (labelQuotient T P)
  exact IsHomeomorph.homeomorph g
    ((isHomeomorph_iff_isQuotientMap_injective).mpr ⟨hq, hg.injective⟩)

private theorem componentIso_mk (T : Scheme.{u}) [ConnectedSpace T] (P : Profinite.{u})
    (x : profiniteProduct T P) :
    componentIso T P (ConnectedComponents.mk x) = (spaceIso T P x).2 := rfl

private theorem affine_sections_ext (A : Type u) [CommRing A] (P : Profinite.{u})
    (B : CommRingCat.{u}) (f g : profiniteProduct (Spec (.of A)) P ⟶ Spec B)
    (h : ∀ a : P, profiniteProductSection (Spec (.of A)) P a ≫ f =
      profiniteProductSection (Spec (.of A)) P a ≫ g) : f = g := by
  apply (cancel_epi (affineIso P A).inv).mp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((affineIso P A).inv ≫ f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((affineIso P A).inv ≫ g)
  rw [← hφ, ← hψ]
  congr 1
  apply CommRingCat.hom_ext
  ext b a
  have he := h a
  have hf : f = (affineIso P A).hom ≫ Spec.map φ := by
    rw [hφ, Iso.hom_inv_id_assoc]
  have hg : g = (affineIso P A).hom ≫ Spec.map ψ := by
    rw [hψ, Iso.hom_inv_id_assoc]
  rw [hf, hg, ← Category.assoc, ← Category.assoc, affineIso_section,
    ← Spec.map_comp, ← Spec.map_comp] at he
  exact congrArg (fun k : B ⟶ CommRingCat.of A ↦ k.hom b) (Spec.map_injective he)

private theorem affineIso_stage (G : ProfiniteGrp.{u}) (q : ℕ) (A : Type u)
    [CommRing A] (N : OpenNormalSubgroup G) :
    (projections (Spec (.of A)) G q).app N ≫
        sigmaSpec (fun _ : Fin q → G ⧸ N.toSubgroup ↦ CommRingCat.of A) =
      (affineIso (Profinite.of (Fin q → G)) A).hom ≫
        Spec.map (CommRingCat.ofHom (finitePowerRingInclusion G q A N)) := by
  apply affine_sections_ext A (Profinite.of (Fin q → G)) _
  intro a
  rw [← Category.assoc, projections_section, ι_sigmaSpec,
    ← Category.assoc, affineIso_section, ← Spec.map_comp]
  rfl

private theorem projections_natural (T T' : Scheme.{u}) (f : T' ⟶ T)
    (G H : ProfiniteGrp.{u}) (ρ : H →* G) (hρ : Continuous ρ) (q : ℕ)
    (N : OpenNormalSubgroup G) (M : OpenNormalSubgroup H)
    (b : (Fin q → H ⧸ M.toSubgroup) → (Fin q → G ⧸ N.toSubgroup))
    (hb : ∀ a : Fin q → H,
      b (finitePowerProjection H q M a) = finitePowerProjection G q N (fun i ↦ ρ (a i))) :
    profiniteProductMap f (labelMap G H ρ hρ q) ≫ (projections T G q).app N =
      (projections T' H q).app M ≫ Sigma.desc (fun c ↦ f ≫
        Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ T) (b c)) := by
  let v : (quotientPowers H q).obj M ⟶ (quotientPowers G q).obj N :=
    CompHausLike.ofHom _ ⟨b, continuous_of_discreteTopology⟩
  change profiniteProductMap f (labelMap G H ρ hρ q) ≫
      profiniteProductMap (𝟙 T) ((quotientPowerCone G q).π.app N) ≫
        (finiteSectionsIso T ((quotientPowers G q).obj N)).hom =
    (profiniteProductMap (𝟙 T') ((quotientPowerCone H q).π.app M) ≫
      (finiteSectionsIso T' ((quotientPowers H q).obj M)).hom) ≫ _
  rw [Category.assoc]
  erw [← finiteSectionsIso_natural f v]
  rw [← Category.assoc, productMap_comp, ← Category.assoc, productMap_comp]
  have hv : labelMap G H ρ hρ q ≫ (quotientPowerCone G q).π.app N =
      (quotientPowerCone H q).π.app M ≫ v := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (hb a).symm
  simp only [Category.comp_id, Category.id_comp]
  rw [hv]

/-- The canonical finite-quotient, affine, topological and component comparisons exist.
Source: Stacks 0BR1 and 097D, with 01YW for affine inverse limits
(blueprint: lem-sfb-profinite-scheme-product-components).

Proof: Open normal subgroups form an identity neighbourhood basis, their cosets are clopen,
and compactness makes their quotients finite. The canonical compatible-family map is
injective by Hausdorffness and surjective by the closed-coset finite-intersection property.
A continuous bijection from compact to Hausdorff is a homeomorphism. Apply this coordinatewise
to finite powers, including the empty power. The profinite test-object functor carries this
presentation to the inverse limit of finite coproducts; the relative test-label comparison
identifies its scheme with the actual fibre product used here and fixes evaluation sections.
On an affine open, finite coproducts are spectra of product rings. Every locally constant
function factors through a finite quotient, and equality is detected at a common refinement
by surjectivity of the quotient maps. This proves the displayed ring cocone is colimiting.
Spec carries that colimit to the affine inverse limit, with exactly the precomposition maps.
The locally constant prime-spectrum homeomorphism identifies each affine chart with its
product with the label space. Its evaluation-prime formula gives the base and label
coordinates, so the charts glue, even if their intersections are not affine. The sections
are the indicated fibres. For connected nonempty T, each slice is connected and every
connected subset has singleton image in the totally disconnected label space. Thus the
slices are precisely the components. The projection is an open surjection, hence quotient,
and induces the claimed component homeomorphism. Coefficient maps, precomposition, and
evaluation commute; affine-local verification proves naturality for arbitrary scheme maps
and continuous group homomorphisms. Empty schemes and zero rings give empty spectra, and
q = 0 gives singleton label sets and the identity comparison of T. -/
theorem profinite_scheme_product_components : Nonempty ProfiniteSchemeProductComparisons.{u} := by
  refine ⟨{
    group_limit := groupLimit
    group_topology := groupTopology
    power_limit := powerLimit
    power_topology := powerTopology
    projections := projections
    scheme_limit := schemeLimit
    projection_base := projections_base
    projection_section := projections_section
    ring_colimit := ringColimit
    affine := fun G q A _ ↦ affineIso (Profinite.of (Fin q → G)) A
    affine_base := fun G q A _ ↦ affineIso_base (Profinite.of (Fin q → G)) A
    affine_section := fun G q A _ ↦ affineIso_section (Profinite.of (Fin q → G)) A
    affine_stage := affineIso_stage
    open_base_change := fun _ G q _ _ j _ ↦ productBaseChange j (Profinite.of (Fin q → G))
    open_base_change_fst := fun _ G q _ _ j _ ↦
      productBaseChange_fst j (Profinite.of (Fin q → G))
    open_base_change_snd := fun _ G q _ _ j _ ↦
      productBaseChange_snd j (Profinite.of (Fin q → G))
    space := fun T G q ↦ spaceIso T (Profinite.of (Fin q → G))
    space_base := fun _ _ _ _ ↦ rfl
    space_section := fun T G q ↦ spaceIso_section T (Profinite.of (Fin q → G))
    affine_space := fun G q A _ ↦ affine_space_formula (Profinite.of (Fin q → G)) A
    component_fibres := fun T _ G q ↦ componentFibres T (Profinite.of (Fin q → G))
    label_open := fun T _ G q ↦ labelOpen T (Profinite.of (Fin q → G))
    label_quotient := fun T _ G q ↦ labelQuotient T (Profinite.of (Fin q → G))
    components := fun T _ G q ↦ componentIso T (Profinite.of (Fin q → G))
    components_mk := fun T _ G q ↦ componentIso_mk T (Profinite.of (Fin q → G))
    projection_natural := projections_natural
    affine_natural := fun G H ρ hρ q A B _ _ φ ↦
      affineIso_natural (labelMap G H ρ hρ q) φ
    space_natural := fun _ _ f _ _ ρ hρ q x ↦ spaceMap_natural f (labelMap _ _ ρ hρ q) x
  }⟩

end AlgebraicGeometry.Scheme.UniversalCover
