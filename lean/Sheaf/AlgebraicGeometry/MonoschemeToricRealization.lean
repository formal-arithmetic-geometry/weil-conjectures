/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/

import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Fine monoschemes, toric realization, and normalized towers

Source: ILO, Travaux de Gabber, Exposé VIII, 2.2.1--2.2.8, 3.1.3--3.1.22,
3.2.1--3.2.2 and 3.2.14--3.2.15 (blueprint: def-trf-monoscheme-toric-realization).

Monoids are written multiplicatively, so products below encode the additive direct sums.
The realization is the actual colimit of the affine monoid-algebra diagram. The named
localization obligations justify that colimit; they do not choose undetermined data.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry
namespace Monoscheme

/-- The unsharpened affine monoidal space, with the dependency's actual localization sheaf.
Source: ILO VIII 3.1.3 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def affine (P : Type u) [CommMonoid P] : SheafedSpace CommMonCat.{u} where
  carrier := TopCat.of (FineFan.MonoidPrime P)
  presheaf := (FineFan.spectrumSheaf P).obj
  IsSheaf := (FineFan.spectrumSheaf P).property

/-- An affine chart is an isomorphism onto an open, without quotienting its monoid by units.
Source: ILO VIII 3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
structure Chart (X : SheafedSpace CommMonCat.{u}) where
  openSet : Opens X
  monoid : CommMonCat.{u}
  fine : FineFan.IsFine monoid
  iso : X.restrict openSet.isOpenEmbedding ≅ affine monoid

/-- Fine monoschemes with finite affine covers; the empty cover is permitted.
Source: ILO VIII 3.1.3 and 3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
structure Fine where
  space : SheafedSpace CommMonCat.{u}
  finiteCover : ∃ n : ℕ, ∃ c : Fin n → Chart space,
    ∀ x : space, ∃ i : Fin n, x ∈ (c i).openSet

/-- Local homomorphisms on actual stalks define the morphisms of monoschemes.
Source: ILO VIII 3.1.5--3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
structure Hom (G F : Fine.{u}) where
  map : G.space ⟶ F.space
  isLocal : FineFan.IsLocalMorphism map

/-- Torsion-freeness is imposed on the group completion of every stalk.
Source: ILO VIII 3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
def Fine.IsTorsionFree (M : Fine.{u}) : Prop :=
  ∀ (x : M.space) (g : Algebra.GrothendieckGroup (FineFan.stalk M.space.presheaf x))
    (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A smooth stalk is a finite free monoid times a finite free group, including both ranks zero.
Source: ILO VIII 3.1.13--3.1.15 (blueprint: def-trf-monoscheme-toric-realization). -/
def Fine.IsSmooth (M : Fine.{u}) : Prop :=
  ∀ x : M.space, ∃ r t : ℕ, Nonempty
    ((FineFan.stalk M.space.presheaf x) ≃*
      (Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)))

/-- Smooth maps extend the given stalk map by the indicated free factors.
Source: ILO VIII 3.1.13--3.1.15 (blueprint: def-trf-monoscheme-toric-realization). -/
def Hom.IsSmooth {G F : Fine.{u}} (f : Hom G F) : Prop :=
  ∀ x : G.space, ∃ r t : ℕ,
    ∃ e : ((FineFan.stalk F.space.presheaf (f.map.hom.base x)) ×
      Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ)) ≃*
        (FineFan.stalk G.space.presheaf x),
      ∀ p, e (p, 1, 1) = FineFan.stalkMap f.map x p

/-- Sharpening uses sheafification of the sectionwise quotient by units.
Source: ILO VIII 3.1.11 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def sharpening (M : Fine.{u}) : SheafedSpace CommMonCat.{u} where
  carrier := M.space.carrier
  presheaf := (FineFan.sharpSheaf M.space.presheaf).obj
  IsSheaf := (FineFan.sharpSheaf M.space.presheaf).property

/-- Sharpening is a fine fan, with the same underlying topological space.
Source: ILO VIII 3.1.11 (blueprint: def-trf-monoscheme-toric-realization).
Proof: on an affine chart the quotient sheaf is precisely the dependency's sharp
model. Its stalks are sharp. These local identifications give affine fan charts
covering the same open sets as the original finite monoscheme atlas. -/
theorem sharpening_properties (M : Fine.{u}) :
    (∀ x : sharpening M, FineFan.IsSharp (FineFan.stalk (sharpening M).presheaf x)) ∧
      ∀ x : sharpening M, ∃ c : FineFan.Chart (sharpening M), x ∈ c.openSet := by
  sorry

/-- The sharpening regarded as a fine fan, reusing the dependency's fan notion.
Source: ILO VIII 3.1.11 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def Fine.toFan (M : Fine.{u}) : FineFan.Fan.{u} where
  space := sharpening M
  sharp := (sharpening_properties M).1
  locallyAffine := (sharpening_properties M).2

/-- The affine opens used for gluing; the empty open is represented by the empty diagram.
Source: ILO VIII 3.1.4 and 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
def AffineOpens (M : Fine.{u}) :=
  {U : Opens M.space // ∃ (P : CommMonCat.{u}), FineFan.IsFine P ∧
    Nonempty (M.space.restrict U.isOpenEmbedding ≅ affine P)}

/-- Affine opens inherit the inclusion order.
Source: ILO VIII 3.1.4 (blueprint: def-trf-monoscheme-toric-realization). -/
instance affineOpensPartialOrder (M : Fine.{u}) : PartialOrder (AffineOpens M) :=
  inferInstanceAs (PartialOrder {U : Opens M.space // ∃ (P : CommMonCat.{u}),
    FineFan.IsFine P ∧ Nonempty (M.space.restrict U.isOpenEmbedding ≅ affine P)})

/-- The monoid-algebra functor, sending each basis element to its image basis element.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def monoidAlgebra (k : Type u) [Field k] : CommMonCat.{u} ⥤ CommRingCat.{u} where
  obj P := .of (MonoidAlgebra k P)
  map f := CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom k f.hom)
  map_id P := by
    apply CommRingCat.hom_ext
    exact MonoidAlgebra.mapDomainRingHom_id
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact MonoidAlgebra.mapDomainRingHom_comp g.hom f.hom

/-- The restriction diagram of monoid sections on all affine opens.
Source: ILO VIII 3.1.3 and 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
def affineSections (M : Fine.{u}) : (AffineOpens M)ᵒᵖ ⥤ CommMonCat.{u} where
  obj U := M.space.presheaf.obj (op U.unop.1)
  map f := M.space.presheaf.map (homOfLE f.unop.le).op
  map_id _U := M.space.presheaf.map_id _
  map_comp _f _g := M.space.presheaf.map_comp _ _

/-- The actual affine toric diagram, whose arrows are induced by monoid localization.
Source: ILO VIII 3.2.1--3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def realizationDiagram (k : Type u) [Field k] (M : Fine.{u}) :
    AffineOpens M ⥤ Scheme.{u} :=
  (affineSections M ⋙ monoidAlgebra k).rightOp ⋙ Scheme.Spec

/-- Restriction to a smaller affine open realizes as an open immersion.
Source: ILO VIII 3.1.4(iii), 3.2.2 (blueprint: def-trf-monoscheme-toric-realization).
Proof: a nonempty affine subopen of a fine monoid spectrum is D(a). Its sections
are the localization at a. The monoid algebra is the ring localization at the monomial
of a, and Spec of this localization is the corresponding principal open immersion. -/
theorem realizationDiagram_open (k : Type u) [Field k] (M : Fine.{u})
    {U V : AffineOpens M} (f : U ⟶ V) :
    IsOpenImmersion ((realizationDiagram k M).map f) := by
  sorry

/-- Common affine subopens cover the intersections of the affine toric charts.
Source: ILO VIII 3.1.4(iii), 3.2.2 (blueprint: def-trf-monoscheme-toric-realization).
Proof: inside a common upper affine open, the intersection of two affine monoid
opens is a union of principal opens. Ring localization identifies their realizations
with the corresponding principal opens in the upper chart. A point in the intersection
therefore lies in a common affine refinement, with both images equal to the given point.
For the empty monoscheme this is the empty diagram and the condition is vacuous. -/
theorem realizationDiagram_locallyDirected (k : Type u) [Field k] (M : Fine.{u}) :
    (realizationDiagram k M ⋙ Scheme.forget).IsLocallyDirected := by
  sorry

/-- The toric realization is the canonical quotient gluing of its affine monoid algebras.
Only proofs of the open-gluing conditions are postponed; the gluing data is constructed
by Mathlib and its colimit determines the object uniquely up to its canonical isomorphism.
Source: ILO VIII 3.2.1--3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def realization (k : Type u) [Field k] (M : Fine.{u}) : Scheme.{u} :=
  letI : ∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((realizationDiagram k M).map f) := realizationDiagram_open k M
  letI := realizationDiagram_locallyDirected k M
  colimit (realizationDiagram k M)

/-- The canonical embedding of an affine monoid-algebra chart in its gluing.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def realizationι (k : Type u) [Field k] (M : Fine.{u}) (U : AffineOpens M) :
    (realizationDiagram k M).obj U ⟶ realization k M :=
  letI : ∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((realizationDiagram k M).map f) := realizationDiagram_open k M
  letI := realizationDiagram_locallyDirected k M
  colimit.ι (realizationDiagram k M) U

/-- The canonical base-field maps on the affine charts form a cocone.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def baseCocone (k : Type u) [Field k] (M : Fine.{u}) :
    Cocone (realizationDiagram k M) where
  pt := Spec (.of k)
  ι :=
    { app := fun U ↦ Spec.map (CommRingCat.ofHom
        (algebraMap k (MonoidAlgebra k (M.space.presheaf.obj (op U.1)))))
      naturality := by
        intro U V f
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact MonoidAlgebra.mapDomainRingHom_comp_algebraMap _ }

/-- The structure map k[M] → Spec k is descended from the canonical algebra maps.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def realizationToBase (k : Type u) [Field k] (M : Fine.{u}) :
    realization k M ⟶ Spec (.of k) :=
  letI : ∀ {U V : AffineOpens M} (f : U ⟶ V),
      IsOpenImmersion ((realizationDiagram k M).map f) := realizationDiagram_open k M
  letI := realizationDiagram_locallyDirected k M
  colimit.desc (realizationDiagram k M) (baseCocone k M)

/-- Each chart embedding lies over k, as required for forming the product with the torus.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization).
Proof: the defining colimit-desc equation gives its restriction to every chart, namely
the Spec map of the scalar inclusion k → k[P]. -/
theorem realizationι_over (k : Type u) [Field k] (M : Fine.{u}) (U : AffineOpens M) :
    realizationι k M U ≫ realizationToBase k M = (baseCocone k M).ι.app U := by
  sorry

/-- Realization charts are open immersions into the gluing.
Source: ILO VIII 3.2.2 (blueprint: def-trf-monoscheme-toric-realization).
Proof: the arrows of the realization diagram are open immersions and its underlying
space diagram is locally directed. The open-gluing construction therefore makes each
colimit injection an open immersion, including charts in a disconnected monoscheme. -/
theorem realizationι_open (k : Type u) [Field k] (M : Fine.{u}) (U : AffineOpens M) :
    IsOpenImmersion (realizationι k M U) := by
  sorry

attribute [instance] realizationι_open

/-- A torsion-free connected component of the given, possibly disconnected, monoscheme.
The component is an actual class of points of M, rather than an unrelated connected object.
Source: ILO VIII 3.1.10(ii), 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
structure ToricComponent (M : Fine.{u}) where
  component : ConnectedComponents M.space
  torsionFree : ∀ (x : M.space), ConnectedComponents.mk x = component →
    ∀ (g : Algebra.GrothendieckGroup (FineFan.stalk M.space.presheaf x))
      (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- Affine opens contained in the indicated connected component of M.
Source: ILO VIII 3.1.10(ii), 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
def ComponentAffineOpens {M : Fine.{u}} (C : ToricComponent M) :=
  {U : AffineOpens M // ∀ x : M.space, x ∈ U.1 → ConnectedComponents.mk x = C.component}

/-- Every component has its unique generic point, lying in all its affine opens.
Source: ILO VIII 3.1.10(ii), 3.2.4 (blueprint: def-trf-monoscheme-toric-realization).
Proof: the generic point of Spec P is the empty prime and belongs to every nonempty
principal open. On intersecting affine charts these points coincide. Thus their classes
partition the affine charts into open connected components, each with one generic point.
Each component is nonempty by surjectivity of the component quotient. Its generic point
is unique because these affine opens form a basis and monoid spectra are T0. -/
theorem existsUnique_componentGenericPoint {M : Fine.{u}} (C : ToricComponent M) :
    ∃! η : M.space, ConnectedComponents.mk η = C.component ∧
      ∀ U : ComponentAffineOpens C, η ∈ U.1.1 := by
  sorry

/-- The uniquely determined generic point of this component, as a point of M.
Source: ILO VIII 3.1.10(ii) (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def ToricComponent.genericPoint {M : Fine.{u}} (C : ToricComponent M) :
    M.space :=
  Classical.choose (existsUnique_componentGenericPoint C).exists

/-- The chosen generic point lies in every affine chart of its component.
Source: ILO VIII 3.1.10(ii) (blueprint: def-trf-monoscheme-toric-realization).
Proof: apply the specification of the uniquely determined generic point. -/
theorem ToricComponent.generic {M : Fine.{u}} (C : ToricComponent M)
    (U : ComponentAffineOpens C) : C.genericPoint ∈ U.1.1 := by
  sorry

/-- The component's open subscheme of k[M], the union of its affine chart images.
This is the realization of that component inside the original realization.
Source: ILO VIII 3.2.2--3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def componentOpen (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : (realization k M).Opens :=
  ⨆ U : ComponentAffineOpens C, (realizationι k M U.1).opensRange

/-- The actual open subscheme of k[M] on which the component torus acts.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def componentRealization (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : Scheme.{u} :=
  (componentOpen k C).toScheme

/-- The component embedding into the realization of the arbitrary monoscheme M.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def componentι (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : componentRealization k C ⟶ realization k M :=
  (componentOpen k C).ι

/-- Each component chart lands in the actual component open subscheme.
Source: ILO VIII 3.2.2--3.2.4 (blueprint: def-trf-monoscheme-toric-realization).
Proof: its image is one of the opens in the defining union for componentOpen. The
image of the open-subscheme embedding is exactly that union. -/
theorem componentChart_range (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) (U : ComponentAffineOpens C) :
    Set.range (realizationι k M U.1) ⊆ Set.range (componentι k C) := by
  sorry

/-- The canonical chart map to the component open, obtained by factoring its ambient map.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def componentChart (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) (U : ComponentAffineOpens C) :
    (realizationDiagram k M).obj U.1 ⟶ componentRealization k C :=
  IsOpenImmersion.lift (componentOpen k C).ι (realizationι k M U.1)
    (componentChart_range k C U)

/-- The component's structure morphism is inherited from k[M].
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def componentToBase (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : componentRealization k C ⟶ Spec (.of k) :=
  componentι k C ≫ realizationToBase k M

/-- Component chart maps respect their specified k-structures.
Source: ILO VIII 3.2.2--3.2.4 (blueprint: def-trf-monoscheme-toric-realization).
Proof: the open-immersion lift composed with the component embedding is the original
chart embedding. Compose with realizationToBase and apply realizationι_over. -/
theorem componentChart_over (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) (U : ComponentAffineOpens C) :
    componentChart k C U ≫ componentToBase k C = (baseCocone k M).ι.app U.1 := by
  sorry

/-- The generic lattice, using the canonical completion of the generic group stalk of M.
Source: ILO VIII 3.1.4(i), 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
abbrev ToricComponent.lattice {M : Fine.{u}} (C : ToricComponent M) :=
  Algebra.GrothendieckGroup (FineFan.stalk M.space.presheaf C.genericPoint)

/-- The split torus Spec k[L] of this torsion-free connected component of arbitrary M.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def torus (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : Scheme.{u} :=
  Spec (.of (MonoidAlgebra k C.lattice))

/-- The canonical degree of a local section in the lattice of its component.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def degree {M : Fine.{u}} (C : ToricComponent M) (U : ComponentAffineOpens C) :
    (M.space.presheaf.obj (op U.1.1)) →* C.lattice :=
  (Algebra.GrothendieckGroup.of).comp
    (FineFan.germ M.space.presheaf U.1.1 C.genericPoint (C.generic U)).hom

/-- On every affine open in the component the coaction sends e^p to e^deg(p) ⊗ e^p.
Source: ILO VIII 3.2.4, 3.2.15 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def coaction (k : Type u) [Field k] {M : Fine.{u}} (C : ToricComponent M)
    (U : ComponentAffineOpens C) :
    MonoidAlgebra k (M.space.presheaf.obj (op U.1.1)) →ₐ[k]
      MonoidAlgebra k C.lattice ⊗[k]
        MonoidAlgebra k (M.space.presheaf.obj (op U.1.1)) :=
  MonoidAlgebra.lift k _ _
    { toFun := fun p ↦ (MonoidAlgebra.of k C.lattice (degree C U p)) ⊗ₜ[k]
        (MonoidAlgebra.of k _ p)
      map_one' := by simp only [map_one]; rfl
      map_mul' := fun p q ↦ by
        simp only [map_mul, Algebra.TensorProduct.tmul_mul_tmul] }

/-- The torus structure map is induced by inclusion of scalar coefficients.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def torusToBase (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : torus k C ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k C.lattice)))

/-- The canonical map from a product chart into T times the component open of k[M].
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def chartProductMap (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) (U : ComponentAffineOpens C) :
    pullback (torusToBase k C) ((baseCocone k M).ι.app U.1) ⟶
      pullback (torusToBase k C) (componentToBase k C) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ componentChart k C U)
    (by rw [Category.assoc, componentChart_over]; exact pullback.condition)

/-- The component torus action is uniquely specified by its coaction on all component charts.
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsCanonicalTorusAction (k : Type u) [Field k] {M : Fine.{u}} (C : ToricComponent M)
    (μ : pullback (torusToBase k C) (componentToBase k C) ⟶
      componentRealization k C) : Prop :=
  ∀ U : ComponentAffineOpens C, chartProductMap k C U ≫ μ =
    (pullbackSpecIso k (MonoidAlgebra k C.lattice)
      (MonoidAlgebra k (M.space.presheaf.obj (op U.1.1)))).hom ≫
        Spec.map (CommRingCat.ofHom (coaction k C U).toRingHom) ≫ componentChart k C U

/-- Existence and uniqueness of the action on the actual component open of k[M].
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization).
Proof: germs commute with restriction, so the specified coactions agree on overlaps.
By definition the component chart images cover componentOpen; their products with T
cover the product. Glue the coaction Spec maps, obtaining a unique morphism. The unit
and associativity identities hold on monomials and therefore on this cover. -/
theorem existsUnique_torusAction (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) : ∃! μ, IsCanonicalTorusAction k C μ := by
  sorry

/-- The uniquely determined torus action on the component open subscheme of k[M].
Source: ILO VIII 3.2.4 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def torusAction (k : Type u) [Field k] {M : Fine.{u}} (C : ToricComponent M) :
    pullback (torusToBase k C) (componentToBase k C) ⟶ componentRealization k C :=
  Classical.choose (existsUnique_torusAction k C).exists

/-- Equivariance of an ambient ideal on this component means equality of its pullbacks
by the action followed by the component embedding and by the second projection followed
by that same embedding. No choice of an ideal on a separate connected object is required.
Source: ILO VIII 3.2.14--3.2.15 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsComponentTorusEquivariant (k : Type u) [Field k] {M : Fine.{u}}
    (C : ToricComponent M) (J : (realization k M).IdealSheafData) : Prop :=
  J.comap (torusAction k C ≫ componentι k C) =
    J.comap (pullback.snd (torusToBase k C) (componentToBase k C) ≫ componentι k C)

/-- An ideal of k[M] is torus-equivariant componentwise, for every torsion-free component.
For a torsion-free M this quantifies over all its connected components, including finite
or empty disjoint unions. Components carrying torsion are not designated split tori.
Source: ILO VIII 3.2.4, 3.2.14--3.2.15 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsTorusEquivariant (k : Type u) [Field k] (M : Fine.{u})
    (J : (realization k M).IdealSheafData) : Prop :=
  ∀ C : ToricComponent M, IsComponentTorusEquivariant k C J

/-- Canonical unsharpened global numerator sections.
Source: ILO VIII 3.1.3 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def affineSection (P : Type u) [CommMonoid P] :
    P →* (affine P).presheaf.obj (op ⊤) :=
  (((CategoryTheory.toSheafify (Opens.grothendieckTopology (FineFan.MonoidPrime P))
    (FineFan.spectrumPresheaf P)).app (op ⊤)).hom).comp (FineFan.numerator P)

/-- The canonical germ of an unsharpened affine numerator.
Source: ILO VIII 3.1.3 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def affineGerm {P : Type u} [CommMonoid P] (x : FineFan.MonoidPrime P) :
    P →* FineFan.stalk (affine P).presheaf x :=
  (FineFan.germ (affine P).presheaf ⊤ x (by trivial)).hom.comp (affineSection P)

/-- Characterization of the canonical affine map by prime inverse images and numerator germs.
Source: ILO VIII 3.1.8 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsAffineMap {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (φ : P →* Q) (f : affine Q ⟶ affine P) : Prop :=
  (∀ (x : FineFan.MonoidPrime Q) (a : P),
    a ∈ (f.hom.base x).carrier ↔ φ a ∈ x.carrier) ∧
  (∀ (x : FineFan.MonoidPrime Q) (a : P),
    FineFan.stalkMap f x (affineGerm (f.hom.base x) a) = affineGerm x (φ a))

/-- An unsharpened affine open with specified coordinate monoid.
Source: ILO VIII 3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
structure AffineOpen (X : SheafedSpace CommMonCat.{u}) (P : Type u) [CommMonoid P] where
  openSet : Opens X
  iso : X.restrict openSet.isOpenEmbedding ≅ affine P

/-- The chart embedding in the monoscheme.
Source: ILO VIII 3.1.9 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def AffineOpen.inclusion {X : SheafedSpace CommMonCat.{u}}
    {P : Type u} [CommMonoid P] (c : AffineOpen X P) : affine P ⟶ X :=
  c.iso.inv ≫ X.ofRestrict c.openSet.isOpenEmbedding

/-- Section sets of an ideal. The predicate `IsIdealSheaf` below imposes the subsheaf axioms.
Source: ILO VIII 3.1.18 (blueprint: def-trf-monoscheme-toric-realization). -/
def IdealFamily (F : Fine.{u}) := ∀ U : Opens F.space, Set (F.space.presheaf.obj (op U))

/-- Germs belonging to an ideal are germs of actual local ideal sections.
Source: ILO VIII 3.1.18 (blueprint: def-trf-monoscheme-toric-realization). -/
def idealStalk {F : Fine.{u}} (I : IdealFamily F) (x : F.space) :
    Set (FineFan.stalk F.space.presheaf x) :=
  {t | ∃ (U : Opens F.space) (hx : x ∈ U) (s : F.space.presheaf.obj (op U)),
    s ∈ I U ∧ FineFan.germ F.space.presheaf U x hx s = t}

/-- A subsheaf of ideals: multiplicative absorption, restriction, and local membership.
The local-membership clause, with the ambient sheaf, gives the subsheaf gluing axiom.
Source: ILO VIII 3.1.18 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsIdealSheaf {F : Fine.{u}} (I : IdealFamily F) : Prop :=
  (∀ (U : Opens F.space) (s t : F.space.presheaf.obj (op U)), s ∈ I U → s * t ∈ I U) ∧
  (∀ (U V : Opens F.space) (h : V ≤ U) (s : F.space.presheaf.obj (op U)),
    s ∈ I U → F.space.presheaf.map (homOfLE h).op s ∈ I V) ∧
  (∀ (U : Opens F.space) (s : F.space.presheaf.obj (op U)),
    (∀ (x : F.space) (hx : x ∈ U),
      FineFan.germ F.space.presheaf U x hx s ∈ idealStalk I x) → s ∈ I U)

/-- Nonempty coherence is local generation by a finite nonempty list of sections.
Generation is tested on germs, so it means sheaf generation and not just global generation.
Source: ILO VIII 3.1.18 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsNonemptyCoherentIdeal {F : Fine.{u}} (I : IdealFamily F) : Prop :=
  IsIdealSheaf I ∧ ∀ x : F.space,
    ∃ (U : Opens F.space) (_hx : x ∈ U) (n : ℕ) (_hn : 0 < n)
      (s : Fin n → F.space.presheaf.obj (op U)),
      (∀ i, s i ∈ I U) ∧
      ∀ (y : F.space) (hy : y ∈ U) (t : FineFan.stalk F.space.presheaf y),
        t ∈ idealStalk I y ↔
          ∃ (i : Fin n) (q : FineFan.stalk F.space.presheaf y),
            t = FineFan.germ F.space.presheaf U y hy (s i) * q

/-- The ideal generated by the image under the monoscheme morphism, computed locally on germs.
Source: ILO VIII 3.1.18 and 3.1.22 (blueprint: def-trf-monoscheme-toric-realization). -/
def pullbackAlong {G F : Fine.{u}} (f : G.space ⟶ F.space) (I : IdealFamily F) : IdealFamily G :=
  fun U ↦ {s | ∀ (x : G.space) (hx : x ∈ U),
    ∃ (t : FineFan.stalk F.space.presheaf (f.hom.base x)) (_ht : t ∈ idealStalk I _)
      (q : FineFan.stalk G.space.presheaf x),
      FineFan.germ G.space.presheaf U x hx s = FineFan.stalkMap f x t * q}

/-- Pullback along a local monoscheme morphism, using the canonical ideal generated by its image.
Source: ILO VIII 3.1.18 (blueprint: def-trf-monoscheme-toric-realization). -/
def pullbackIdeal {G F : Fine.{u}} (f : Hom G F) (I : IdealFamily F) : IdealFamily G :=
  pullbackAlong f.map I

/-- The unit ideal is the entire monoid sheaf, including its unique empty-open section.
Source: ILO VIII 3.1.22 and 3.1.26 (blueprint: def-trf-monoscheme-toric-realization). -/
def wholeIdeal (F : Fine.{u}) : IdealFamily F := fun _ ↦ Set.univ

/-- The affine ring ideal generated by the monomials of a monoid ideal.
Source: ILO VIII 3.2.14 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def chartRingIdeal (k : Type u) [Field k] {M : Fine.{u}} (I : IdealFamily M)
    (U : AffineOpens M) : ((realizationDiagram k M).obj U).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span ((fun p ↦ MonoidAlgebra.of k _ p) '' I U.1)).map
      (Scheme.ΓSpecIso (.of (MonoidAlgebra k (M.space.presheaf.obj (op U.1))))).inv.hom)

/-- The toric ring ideal is glued from the monomial ideals on all affine charts.
The infimum of their pushforwards imposes exactly these local membership conditions;
localization compatibility of a monoid ideal identifies its pullback with each chart ideal.
Source: ILO VIII 3.2.14 (blueprint: def-trf-monoscheme-toric-realization). -/
noncomputable def ringIdeal (k : Type u) [Field k] {M : Fine.{u}} (I : IdealFamily M) :
    (realization k M).IdealSheafData :=
  ⨅ U : AffineOpens M, (chartRingIdeal k I U).map (realizationι k M U)

/-- A finite ideal is generated on an unsharpened chart by its listed monomials.
Source: ILO VIII 3.1.18--3.1.19 (blueprint: def-trf-monoscheme-toric-realization). -/
def GeneratedOnChart {F : Fine.{u}} (I : IdealFamily F)
    {P : Type u} [CommMonoid P] (c : AffineOpen F.space P) (E : Finset P) : Prop :=
  ∀ (x : FineFan.MonoidPrime P) (t : FineFan.stalk F.space.presheaf (c.inclusion.hom.base x)),
    t ∈ idealStalk I (c.inclusion.hom.base x) ↔
      ∃ (a : E) (q : FineFan.stalk F.space.presheaf (c.inclusion.hom.base x)),
        FineFan.stalkMap c.inclusion x t = affineGerm x a.1 *
          FineFan.stalkMap c.inclusion x q

/-- The prescribed saturated blowup over one affine base chart. The source is covered by
`Spec(C_a)`; the overlaps are exactly `D(b/a)`. Every chart map is normalized on `P`.
Consequently the transitions are the identity of the common localized monoids inside `P^gp`:
the images of `P` generate that group, so no other transition over `P` is possible. An open
cover with these identifications is precisely the quotient gluing, and its sheaf is the
sheaf of agreeing tuples, since the ambient object is a sheafed space.
Source: ILO VIII 3.1.19--3.1.24 (blueprint: def-trf-monoscheme-toric-realization). -/
structure BlowupPatch {B F : Fine.{u}} (b : Hom B F) (I : IdealFamily F) where
  monoid : CommMonCat.{u}
  fine : FineFan.IsFine monoid
  baseChart : AffineOpen F.space monoid
  generators : Finset monoid
  nonempty : generators.Nonempty
  generates : GeneratedOnChart I baseChart generators
  charts : ∀ a : generators, AffineOpen B.space (FineFan.saturatedChart monoid generators a.1)
  chartMap : ∀ a : generators,
    affine (FineFan.saturatedChart monoid generators a.1) ⟶ affine monoid
  canonical : ∀ a : generators,
    IsAffineMap (FineFan.chartInclusion monoid generators a.1) (chartMap a)
  overBase : ∀ a : generators,
    (charts a).inclusion ≫ b.map = chartMap a ≫ baseChart.inclusion
  cover : ∀ x : B.space,
    b.map.hom.base x ∈ baseChart.openSet ↔ ∃ a : generators, x ∈ (charts a).openSet
  overlap : ∀ (a d : generators)
    (x : FineFan.MonoidPrime (FineFan.saturatedChart monoid generators a.1)),
    (charts a).inclusion.hom.base x ∈ (charts d).openSet ↔
      FineFan.overlapElement generators a.1 d ∉ x.carrier

/-- Being the saturated blowup along the indicated ideal, specified by the exact affine
chart construction and its open gluing. This is a property of a supplied morphism, and
never chooses an object from an undetermined existence theorem.
Source: ILO VIII 3.1.19--3.1.24 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsSaturatedBlowup {B F : Fine.{u}} (b : Hom B F) (I : IdealFamily F) : Prop :=
  IsNonemptyCoherentIdeal I ∧
    ∀ x : F.space, ∃ p : BlowupPatch b I, x ∈ p.baseChart.openSet

/-- A finite saturated blowup tower with every center and its order retained.
The type `Fin n` is empty for length zero, so identity towers are included.
Source: ILO VIII 3.1.22--3.1.26 (blueprint: def-trf-monoscheme-toric-realization). -/
structure Tower (n : ℕ) where
  level : Fin (n + 1) → Fine.{u}
  center : ∀ i : Fin n, IdealFamily (level i.castSucc)
  arrow : ∀ i : Fin n, Hom (level i.succ) (level i.castSucc)
  blowup : ∀ i : Fin n, IsSaturatedBlowup (arrow i) (center i)

/-- A tower over a second base is the recursive pullback tower exactly when its
successive centers are the pulled-back original centers, and its level maps commute.
Each successive space is already the saturated blowup by `Tower.blowup`.
Source: ILO VIII 3.1.22--3.1.23 (blueprint: def-trf-monoscheme-toric-realization). -/
structure PullbackTower {n : ℕ} (T S : Tower.{u} n) where
  lift : ∀ i : Fin (n + 1), Hom (S.level i) (T.level i)
  centers : ∀ i : Fin n, S.center i = pullbackIdeal (lift i.castSucc) (T.center i)
  commutes : ∀ i : Fin n,
    (S.arrow i).map ≫ (lift i.castSucc).map = (lift i.succ).map ≫ (T.arrow i).map

/-- Contracting a tower collapses exactly the unit-center isomorphisms. The monotone
surjection records the order, and the isomorphisms identify every old level with its
contracted level. Kept arrows and centers are transported through these isomorphisms.
A unit-center saturation which is not an isomorphism must therefore remain.
Source: ILO VIII 3.1.22 and 3.1.26, saturated variant
(blueprint: def-trf-monoscheme-toric-realization). -/
structure Contraction {n m : ℕ} (T : Tower.{u} n) (S : Tower.{u} m) where
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  iso : ∀ i : Fin (n + 1), (T.level i).space ≅ (S.level (index i)).space
  adjacent : ∀ i : Fin n, index i.succ = index i.castSucc ∨
    ∃ k : Fin m, index i.castSucc = k.castSucc ∧ index i.succ = k.succ
  deleted : ∀ i : Fin n, index i.succ = index i.castSucc ↔
    T.center i = wholeIdeal (T.level i.castSucc) ∧ IsIso (T.arrow i).map
  deletedMap : ∀ (i : Fin n) (h : index i.succ = index i.castSucc),
    (T.arrow i).map ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h)
  keptMap : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (h₁ : index i.succ = k.succ),
    (T.arrow i).map ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₁) ≫
        (S.arrow k).map ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀.symm)
  keptCenter : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (_h₁ : index i.succ = k.succ),
    T.center i = pullbackAlong
      ((iso i.castSucc).hom ≫ eqToHom (congrArg (fun j ↦ (S.level j).space) h₀))
        (S.center k)

/-- The normalized blowup property retains the specified coherent center and the map over X.
The underlying construction is the already published componentwise normalization of blowup.
Source: ILO VIII 2.2.3 (blueprint: def-trf-monoscheme-toric-realization). -/
def IsNormalizedBlowup {Y X : Scheme.{u}} (b : Y ⟶ X) (J : X.IdealSheafData) : Prop :=
  (∀ U : X.affineOpens, (J.ideal U).FG) ∧
    ∃ e : Y ≅ J.normalizedBlowup, e.hom ≫ J.normalizedBlowupMap = b

/-- Finite normalized towers retain every ideal center and its order, including length zero.
Source: ILO VIII 2.2.5 (blueprint: def-trf-monoscheme-toric-realization). -/
structure NormalizedTower (n : ℕ) where
  level : Fin (n + 1) → Scheme.{u}
  reduced : ∀ i, IsReduced (level i)
  center : ∀ i : Fin n, (level i.castSucc).IdealSheafData
  arrow : ∀ i : Fin n, level i.succ ⟶ level i.castSucc
  blowup : ∀ i : Fin n, IsNormalizedBlowup (arrow i) (center i)

/-- Recursive smooth pullback retains the pulled centers and the canonical commuting squares.
Each level is already the normalized blowup of its preceding pulled center.
Source: ILO VIII 2.2.7--2.2.8 (blueprint: def-trf-monoscheme-toric-realization). -/
structure NormalizedPullback {n : ℕ} (T S : NormalizedTower.{u} n) where
  lift : ∀ i : Fin (n + 1), S.level i ⟶ T.level i
  smooth : ∀ i, Smooth (lift i)
  centers : ∀ i : Fin n, S.center i = (T.center i).comap (lift i.castSucc)
  commutes : ∀ i : Fin n, S.arrow i ≫ lift i.castSucc = lift i.succ ≫ T.arrow i

/-- Contraction deletes precisely unit-center isomorphisms, retaining nontrivial normalization.
Kept maps and centers are transported along the level identifications in their original order.
Source: ILO VIII 2.3.4, normalized variant
(blueprint: def-trf-monoscheme-toric-realization). -/
structure NormalizedContraction {n m : ℕ}
    (T : NormalizedTower.{u} n) (S : NormalizedTower.{u} m) where
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  iso : ∀ i : Fin (n + 1), T.level i ≅ S.level (index i)
  adjacent : ∀ i : Fin n, index i.succ = index i.castSucc ∨
    ∃ k : Fin m, index i.castSucc = k.castSucc ∧ index i.succ = k.succ
  deleted : ∀ i : Fin n, index i.succ = index i.castSucc ↔
    T.center i = ⊤ ∧ IsIso (T.arrow i)
  deletedMap : ∀ (i : Fin n) (h : index i.succ = index i.castSucc),
    T.arrow i ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg S.level h)
  keptMap : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (h₁ : index i.succ = k.succ),
    T.arrow i ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ eqToHom (congrArg S.level h₁) ≫
        S.arrow k ≫ eqToHom (congrArg S.level h₀.symm)
  keptCenter : ∀ (i : Fin n) (k : Fin m)
    (h₀ : index i.castSucc = k.castSucc) (_h₁ : index i.succ = k.succ),
    T.center i = (S.center k).comap
      ((iso i.castSucc).hom ≫ eqToHom (congrArg S.level h₀))

/-- A normalized desingularization tower has a regular final scheme.
Source: ILO VIII 2.3.2 (blueprint: def-trf-monoscheme-toric-realization). -/
def NormalizedTower.IsDesingularization {n : ℕ} (T : NormalizedTower.{u} n) : Prop :=
  IsRegularScheme (T.level (Fin.last n))

end Monoscheme
end AlgebraicGeometry
