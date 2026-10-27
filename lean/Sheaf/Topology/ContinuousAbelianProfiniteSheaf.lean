/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Yoneda

/-!
# Continuous-function abelian sheaves on profinite sets

Source: blueprint `lem-sfb-subfield-flat.proof.md`, first two sentences, and
`def-sfb-continuous-map-condensed-ring.proof.md`, pointwise operations and conditions (a),(b)
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).

The coefficient group has an arbitrary topology with continuous addition and negation.
No separation hypothesis is imposed. Sections are lifted only to accommodate universes.
Postcomposition is specified on sections, together with all additive functor laws.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace Profinite

/-- Continuous functions with pointwise abelian operations and precomposition restrictions.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, first paragraph,
with abelian groups in place of rings
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf). -/
noncomputable def continuousAbelianPresheaf (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1} where
  obj S := AddCommGrpCat.of (ULift.{max u v + 1} C(S.unop, G))
  map f := AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((ContinuousMap.compAddMonoidHom' f.unop.hom.hom).comp
        AddEquiv.ulift.toAddMonoidHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous-function presheaf is an abelian sheaf on the coherent profinite site.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, conditions (a),(b),
adapted to abelian groups (blueprint: lem-sfb-continuous-abelian-profinite-sheaf).

Proof: pointwise operations make each continuous-map set an abelian group; restriction
preserves these operations. Functions out of finite disjoint unions are tuples of continuous
functions, additively, including the empty union. For a surjection q of profinite sets,
compatibility on its kernel pair says exactly that a function is constant on q-fibres.
The compact-to-Hausdorff quotient-map lemma descends it to a unique continuous function,
without requiring the target group to be Hausdorff. Descent is additive by evaluating after
the surjection, so the equalizer universal property holds in abelian groups. Apply the
coherent sheaf criterion (lem-sfb-profinite-coherent-sheaf-criterion). Universe lifting
transports the same groups and restriction maps. -/
theorem isSheaf_continuousAbelianPresheaf (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousAbelianPresheaf.{u, v} G) := by
  let e : continuousAbelianPresheaf.{u, v} G ⋙
      forget AddCommGrpCat.{max u v + 1} ≅
      ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} G ⋙
        uliftFunctor.{max u v + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  have h : Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousAbelianPresheaf.{u, v} G ⋙
        forget AddCommGrpCat.{max u v + 1}) := by
    rw [Presheaf.isSheaf_of_iso_iff e,
      isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    refine ⟨inferInstance, ?_⟩
    apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} G
    intro Z B π hπ
    exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 0 2).mp hπ)
      π.hom.hom.continuous
  exact Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
    (continuousAbelianPresheaf.{u, v} G)
    (forget AddCommGrpCat.{max u v + 1}) h

/-- The actual abelian sheaf with sections C(S,G), lifted to the coefficient universe.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, continuous-function coordinate maps
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf). -/
noncomputable def continuousAbelianSheaf (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{max u v + 1} :=
  ⟨continuousAbelianPresheaf G, isSheaf_continuousAbelianPresheaf G⟩

/-- Explicit unique gluing for every finite jointly surjective profinite cover.
Compatibility is equality of values on each fibre product, expressed by pairs of points.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, conditions (a),(b)
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).

Proof: combine the finitely many functions on the disjoint union of the cover spaces.
Compatibility makes this continuous function constant on fibres of the surjection to S.
That surjection is a quotient map by compactness and Hausdorffness of S, so the function
descends continuously and uniquely. An empty jointly surjective family forces S empty
and yields its unique section. -/
theorem continuousAbelianSheaf_glue (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    (S : Profinite.{u}) (I : Type w) [Finite I] (U : I → Profinite.{u})
    (q : ∀ i, U i ⟶ S) (hq : ∀ s : S, ∃ (i : I) (x : U i), q i x = s)
    (h : ∀ i, C(U i, G))
    (hc : ∀ (i j : I) (x : U i) (y : U j), q i x = q j y → h i x = h j y) :
    ∃! a : C(S, G), ∀ (i : I) (x : U i), a (q i x) = h i x := by
  classical
  let p : C((i : I) × U i, S) :=
    ⟨fun x ↦ q x.1 x.2, continuous_sigma fun i ↦ (q i).hom.hom.continuous⟩
  have hp : Function.Surjective p := by
    intro s
    obtain ⟨i, x, hx⟩ := hq s
    exact ⟨⟨i, x⟩, hx⟩
  have hpq : Topology.IsQuotientMap p := .of_surjective_continuous hp p.continuous
  let b : C((i : I) × U i, G) :=
    ⟨fun x ↦ h x.1 x.2, continuous_sigma fun i ↦ (h i).continuous⟩
  have hb : Function.FactorsThrough b p := by
    intro x y hxy
    exact hc x.1 y.1 x.2 y.2 hxy
  refine ⟨hpq.lift b hb, ?_, ?_⟩
  · intro i x
    exact congrArg (fun a : C((i : I) × U i, G) ↦ a ⟨i, x⟩) (hpq.lift_comp b hb)
  · intro a ha
    ext s
    obtain ⟨i, x, rfl⟩ := hq s
    exact (ha i x).trans
      (congrArg (fun a : C((i : I) × U i, G) ↦ a ⟨i, x⟩) (hpq.lift_comp b hb)).symm

/-- Sections over the empty profinite space form the zero abelian group.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, condition (a), empty case
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).

Proof: there is precisely one function from an empty space to G; it is the zero section.
Thus every element of the lifted continuous-map group is zero, including when G itself
is the zero group. -/
theorem continuousAbelianSheaf_empty (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] (S : Profinite.{u}) [IsEmpty S] :
    ∀ a : (continuousAbelianSheaf.{u, v} G).obj.obj (op S), a = 0 := by
  intro a
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact isEmptyElim x

/-- Postcomposition with a continuous additive homomorphism, on the prescribed sections.
Its components are additive, and associativity of composition gives naturality.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, additive coordinate maps,
and `def-sfb-continuous-map-condensed-ring.proof.md`, functoriality
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf). -/
noncomputable def continuousAbelianSheafMap {G H : Type v} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : G →ₜ+ H) :
    continuousAbelianSheaf.{u, v} G ⟶ continuousAbelianSheaf.{u, v} H :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        (AddEquiv.ulift.symm.toAddMonoidHom.comp
          ((f.toAddMonoidHom.compLeftContinuous S.unop f.continuous).comp
            AddEquiv.ulift.toAddMonoidHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The identity law of the continuous-function sheaf functor.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, functoriality
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).
Proof: on every section a, postcomposition with the identity sends a to a. Extensionality
of homomorphisms, natural transformations and sheaf morphisms gives the identity. -/
theorem continuousAbelianSheafMap_id (G : Type v) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] :
    continuousAbelianSheafMap.{u, v} (ContinuousAddMonoidHom.id G) =
      𝟙 (continuousAbelianSheaf.{u, v} G) := by
  ext S a
  rfl

/-- The composition law of the continuous-function sheaf functor.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, functoriality
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).
Proof: on each section a, (g composed with f) composed with a is g composed with
(f composed with a). Extensionality gives equality of the sheaf morphisms. -/
theorem continuousAbelianSheafMap_comp {G H K : Type v}
    [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [IsTopologicalAddGroup K]
    (f : G →ₜ+ H) (g : H →ₜ+ K) :
    continuousAbelianSheafMap.{u, v} (g.comp f) =
      continuousAbelianSheafMap f ≫ continuousAbelianSheafMap g := by
  ext S a
  rfl

/-- Additivity of the continuous-function sheaf functor on every hom group.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, additive coordinate maps
(blueprint: lem-sfb-continuous-abelian-profinite-sheaf).
Proof: the sum f+g is continuous and additive. Evaluation on a section a and a point s
gives (f+g)(a(s)) = f(a(s))+g(a(s)). Addition of abelian-sheaf morphisms is sectionwise,
so extensionality gives the asserted equality of sheaf morphisms. -/
theorem continuousAbelianSheafMap_add {G H : Type v} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f g : G →ₜ+ H) :
    continuousAbelianSheafMap.{u, v} (f + g) =
      continuousAbelianSheafMap f + continuousAbelianSheafMap g := by
  ext S a
  rfl

end Profinite
