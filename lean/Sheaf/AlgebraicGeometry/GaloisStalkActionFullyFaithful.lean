/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants

/-!
# Full faithfulness of the canonical Galois stalk functor

Source: Stacks Project, Tags 03QT and 04JM.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 03QT and 04JM, theorem-equivalence-sheaves-point
and the direct proof of lemma-global-sections-point.
(blueprint: lem-exc-galois-stalk-action-fully-faithful).

Any lift of the stalk functor with the canonical formula on germs is fully faithful.

Proof: Let A be the subfield of Omega consisting of the elements algebraic over K.
It is algebraically closed: roots in Omega of polynomials over A are algebraic over
K. It contains the image of Ks. Each pointed lift to an etale K-scheme factors
uniquely through Spec A, since its point has finite separable residue field over K.
These natural bijections of lifts identify the pointed-neighbourhood categories,
their stalk colimits, and the germ maps. Automorphisms of Omega preserve A and their
restrictions give the same change-of-lift action. Apply fieldSections_stalkInvariants
at A and transfer its invariant-section bijections to Omega. The given formula
identifies the action transported by j with that action, since every g extends to
Omega and every germ has a representative. Thus for every finite separable
intermediate field L of Ks, sections of F over Spec L are the invariants of T(F)
under Gal(Ks/L). These identifications are natural in F and in every K-embedding
of fields, by the embedding compatibility in fieldSections_stalkInvariants.
Every etale K-scheme is a disjoint union of spectra of finite separable fields.
Choose embeddings of these fields into Ks. The sheaf condition for the covering
by components identifies its sections with the product of the corresponding
invariant sets. An equivariant map T(F) -> T(F') restricts to maps on all these
invariant sets. The embedding compatibility makes the resulting section maps
natural for all maps of etale schemes, independent of the chosen embeddings.
They define a sheaf morphism, whose map on germs is the original map, since every
germ is represented on one finite separable component. Conversely the same
section bijections show that a sheaf morphism is determined by its stalk map.
Naturality of j identifies these operations with T.map, proving both surjectivity
and injectivity on every hom-set. For the empty etale scheme use the empty product;
for separably closed K the invariant sets are the entire stalks. -/
theorem galoisStalkActionFunctor_full_faithful
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] :
    let S := Spec (.of K)
    let J := S.smallEtaleTopology
    let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let p := pointSmallEtale s
    let G := Gal(Ks/K)
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type (max (u + 1) v)) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type (max (u + 1) v)) (G := G))
    ∀ (T : Sheaf J (Type (max (u + 1) v)) ⥤
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : T ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅ p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((T.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) →
      T.Full ∧ T.Faithful := by sorry

end AlgebraicGeometry.Scheme
