/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-!
# Canonical set-valued stalk equivalence over an algebraically closed extension

Source: Stacks Project, Tags 03QT and 03QW.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 03QT and 03QW.
(blueprint: lem-exc-abelian-sheaves-gmodules-action).

Proof: For any pointed etale neighbourhood, change its lift by an automorphism of
Omega extending g. Finite separable residue fields show independence from the chosen
extension, compatibility with restrictions, and open stabilizers. This defines the
canonical discrete G-action on germs. The geometric stalk commutes with finite limits
and colimits. On representable sheaves its action is the usual action on separable
points. Sections over finite separable extensions are the fixed points of the
corresponding open subgroups, so equivariant stalk maps reconstruct all sheaf maps.
To use the existing sections/invariants theorem, which assumes an algebraic geometric
point, take the subfield A of elements of Omega algebraic over K. It is an algebraic
closure of K and contains Ks. Every lift to an etale K-scheme factors uniquely through
Spec A, since its residue field is finite separable. These natural bijections identify
the pointed-neighbourhood diagrams, hence the two stalks and all germ maps. Restricting
automorphisms of Omega to A identifies their actions. Apply the sections/invariants
theorem at A and transfer its bijections and restriction formulas to Omega.
For essential surjectivity, decompose a discrete G-set into its finite orbits. Each
orbit is a small G-set, represented by a finite etale scheme by the field/G-set
equivalence. Take the coproduct of these representable sheaves in Type w, where
w = max (u + 1) v. Stalks preserve coproducts, equivariantly for the action on germs,
so its stalk is the original G-set. This works even when the orbit index set is too
large for a coproduct scheme in the site's universe. Use the stalk as the underlying
functor to get j. The definition by change of lift gives the displayed formula.
Only algebraic elements in Omega occur in the finite separable fibres, so the same
argument applies when Omega has transcendental elements over K. For separably closed
K the G-action is trivial and the construction is ordinary evaluation at the point. -/
theorem abelianSheaves_equiv_discreteGModules_action
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
    ∃ (Eset : Sheaf J (Type (max (u + 1) v)) ≌
        DiscreteContAction (Type (max (u + 1) v)) G)
      (j : Eset.functor ⋙ V ⋙ Action.forget (Type (max (u + 1) v)) G ≅
        p.sheafFiber),
      (∀ (F : Sheaf J (Type (max (u + 1) v))) (g : G)
          (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : S.Etale) (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        (j.hom.app F) ((Eset.functor.obj F).obj.obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z) := by
  sorry

end AlgebraicGeometry.Scheme
