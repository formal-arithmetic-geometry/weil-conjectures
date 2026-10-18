/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentToposRepair
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.CategoryTheory.Sites.GeometricMorphism

/-!
# Finite coproducts of coherent topoi

Source: Stacks Project, Sites, Tags 00VH, 00VM, 00W2 and 00WI; Orgogozo, §8.1
(blueprint: lem-trf-finite-coproduct-topos-coherent).

The disjoint union is Mathlib's sigma category, with its actual objects and morphisms.
Its topology is characterized on every sieve by restriction to the unique component.
All auxiliary predicates below only expand clauses of this node.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe w uE uF u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FiniteCoproductTopos

/-- The topology of the disjoint-union site is exactly the component topologies.
Source: Stacks, 00VH and 00ZC (blueprint: lem-trf-finite-coproduct-topos-coherent). -/
def IsDisjointUnionTopology {I : Type w} (C : I → Type w)
    [∀ i, SmallCategory (C i)] (JC : ∀ i, GrothendieckTopology (C i))
    (J : GrothendieckTopology (Σ i, C i)) : Prop :=
  ∀ (i : I) (U : C i) (R : Sieve ((Sigma.incl i : C i ⥤ Σ k, C k).obj U)),
    R ∈ J ⟨i, U⟩ ↔ R.functorPullback (Sigma.incl i) ∈ JC i U

/-- Coherence of an object, using exactly the existing coherent-object predicate and
packaging the ambient coproduct and finite-limit structures as in the dependency repair.
Source: Orgogozo, §8.1 (blueprint: lem-trf-finite-coproduct-topos-coherent). -/
def IsCoherent {E : Type u} [Category.{v} E] (A : E) : Prop :=
  ∃ hC : HasCoproducts.{w, v, u} E, ∃ hL : HasFiniteLimits E,
    @CategoryTheory.IsCoherentObject.{w, u, v} E _ hC hL A

/-- Restriction to the component is precomposition with its actual inclusion.
Source: Stacks, 00VM (blueprint: lem-trf-finite-coproduct-topos-coherent). -/
def RestrictsToComponents {I : Type w} {C : I → Type w}
    [∀ i, SmallCategory (C i)] (JC : ∀ i, GrothendieckTopology (C i))
    {E : I → Type uE} [∀ i, Category.{w} (E i)]
    (p : ∀ i, E i ≌ Sheaf (JC i) (Type w))
    (J : GrothendieckTopology (Σ i, C i))
    (e : Sheaf J (Type w) ≌ (∀ i, E i)) : Prop :=
  ∀ i, Nonempty
    ((e.functor ⋙ Pi.eval E i) ⋙ ((p i).functor ⋙ sheafToPresheaf (JC i) (Type w)) ≅
      sheafToPresheaf J (Type w) ⋙
        (Functor.whiskeringLeft (C i)ᵒᵖ (Σ k, C k)ᵒᵖ (Type w)).obj (Sigma.incl i).op)

/-- The complete coproduct-topos conclusion. The topology and restriction equivalence
are fixed by their component formulas; no arbitrary replacement construction is assumed.
Source: Stacks, 00VH, 00VM, 00W2, 00WI; Orgogozo, §8.1
(blueprint: lem-trf-finite-coproduct-topos-coherent). -/
structure Witness {I : Type w} [Finite I]
    {C : I → Type w} [∀ i, SmallCategory (C i)]
    (JC : ∀ i, GrothendieckTopology (C i))
    (E : I → Type uE) [∀ i, Category.{w} (E i)]
    (p : ∀ i, E i ≌ Sheaf (JC i) (Type w))
    (J : GrothendieckTopology (Σ i, C i)) where
  topology : IsDisjointUnionTopology C JC J
  equivalence : Sheaf J (Type w) ≌ (∀ i, E i)
  restriction : RestrictsToComponents JC p J equivalence
  limits_componentwise : ∀ (K : Type w) [SmallCategory K]
    (F : K ⥤ Sheaf J (Type w)) (c : Cone F),
    Nonempty (IsLimit c) ↔ ∀ i,
      Nonempty (IsLimit ((equivalence.functor ⋙ Pi.eval E i).mapCone c))
  colimits_componentwise : ∀ (K : Type w) [SmallCategory K]
    (F : K ⥤ Sheaf J (Type w)) (c : Cocone F),
    Nonempty (IsColimit c) ↔ ∀ i,
      Nonempty (IsColimit ((equivalence.functor ⋙ Pi.eval E i).mapCocone c))
  epimorphisms_componentwise : ∀ {A B : Sheaf J (Type w)} (f : A ⟶ B),
    Epi f ↔ ∀ i, Epi (equivalence.functor.map f i)
  inclusion : ∀ i, GeometricMorphism (E i) (Sheaf J (Type w))
  inclusion_inverse : ∀ i,
    (inclusion i).inverse ≅ equivalence.functor ⋙ Pi.eval E i
  inclusion_direct_same : ∀ i,
    ((inclusion i).direct ⋙ equivalence.functor) ⋙ Pi.eval E i ≅ 𝟭 (E i)
  inclusion_direct_other : ∀ (i k : I), k ≠ i → ∀ A : E i,
    Nonempty (IsTerminal (equivalence.functor.obj ((inclusion i).direct.obj A) k))
  universal : ∀ (F : Type uF) [Category.{w} F], IsGrothendieckTopos.{w} F →
    ∀ a : ∀ i, GeometricMorphism (E i) F,
    ∃ (b : GeometricMorphism (Sheaf J (Type w)) F)
      (β : ∀ i, ((inclusion i).comp b).direct ≅ (a i).direct),
      Nonempty (b.inverse ⋙ equivalence.functor ≅ Functor.pi' (fun i ↦ (a i).inverse)) ∧
      (∀ A : ∀ i, E i,
        ∃ π : ∀ i, b.direct.obj (equivalence.inverse.obj A) ⟶ (a i).direct.obj (A i),
          Nonempty (IsLimit (Fan.mk (b.direct.obj (equivalence.inverse.obj A)) π))) ∧
      (∀ (b' : GeometricMorphism (Sheaf J (Type w)) F)
        (β' : ∀ i, ((inclusion i).comp b').direct ≅ (a i).direct),
        ∃! γ : b.direct ≅ b'.direct,
          ∀ i, Functor.isoWhiskerLeft (inclusion i).direct γ ≪≫ β' i = β i)
  presentation_independent : ∀ (C' : I → Type w) [∀ i, SmallCategory (C' i)]
    (JC' : ∀ i, GrothendieckTopology (C' i))
    (_p' : ∀ i, E i ≌ Sheaf (JC' i) (Type w))
    (J' : GrothendieckTopology (Σ i, C' i)), IsDisjointUnionTopology C' JC' J' →
      Nonempty (Sheaf J (Type w) ≌ Sheaf J' (Type w))
  coherent : (∀ i, CoherentToposRepair.IsCoherentTopos.{w, uE, w} (E i)) →
    CoherentToposRepair.IsCoherentTopos.{w, w + 1, w} (Sheaf J (Type w)) ∧
      (∀ A : ∀ i, E i, IsCoherent.{w} (equivalence.inverse.obj A) ↔
        ∀ i, IsCoherent.{w} (A i))
  empty_case : IsEmpty I → Nonempty (Sheaf J (Type w) ≌ Discrete PUnit.{w + 1})

/-- Finite coproduct topoi, their restriction equivalence, componentwise limits, colimits
and epimorphisms, the component geometric morphisms, the coproduct universal property,
presentation independence, componentwise coherence, and the empty-index case.

Source: Stacks Project, Sites, Tags 00VH, 00VM, 00W2 and 00WI; Orgogozo, §8.1
(blueprint: lem-trf-finite-coproduct-topos-coherent).

Proof (postponed), following the six DAG steps:
1. On the sigma category a presheaf is a tuple of presheaves. The sheaf equalizer
   condition is checked on one component at a time, yielding mutually inverse restriction
   and extension equivalences. Limits, colimits and epimorphisms are componentwise.
   When the index is empty there is exactly one sheaf and one arrow. This uses
   def-weil-pbc-sites-and-cohomology, Stacks 00VH, 00VM, 00W2 and 00WI.
2. Projection to component i is left exact. Its right adjoint inserts the given object
   at i and terminal objects elsewhere: all other Hom components are singletons.
   This is the geometric morphism of def-trf-geometric-morphism.
3. Given the a_i, assemble their inverse images into a tuple. Their right adjoint is
   the product of their direct images by the natural Hom adjunction calculation.
   Restriction to each component identifies the composite with a_i. The same calculation
   gives the unique compatible natural isomorphism between two such extensions.
4. Products of equivalences of component sheaf presentations transport this construction,
   proving independence of the presentations.
5. A tuple is quasi-compact iff each component is: extend component covers using identities
   elsewhere, and conversely unite the finitely many finite subcover index sets. The initial
   object is quasi-compact by strictness. Test quasi-separatedness by objects supported in
   one component with initial objects elsewhere; conversely take fibre products componentwise.
   Thus coherence is componentwise, using def-trf-coherent-topos and
   lem-trf-set-sheaf-finite-extensivity.
6. Enlarge the chosen coherent generating subcategories by their initial objects. Products
   of these categories are small, finite-limit-closed and consist of coherent objects.
   Component-supported generators cover every tuple componentwise. This proves coherence
   of the total topos. The empty product has its sole object as coherent generator.
-/
theorem finite_coproduct_topos_coherent {I : Type w} [Finite I]
    (C : I → Type w) [∀ i, SmallCategory (C i)]
    (JC : ∀ i, GrothendieckTopology (C i))
    (E : I → Type uE) [∀ i, Category.{w} (E i)]
    (p : ∀ i, E i ≌ Sheaf (JC i) (Type w)) :
    ∃ J : GrothendieckTopology (Σ i, C i), Nonempty (Witness.{w, uE, uF} JC E p J) := by
  sorry

end CategoryTheory.FiniteCoproductTopos
