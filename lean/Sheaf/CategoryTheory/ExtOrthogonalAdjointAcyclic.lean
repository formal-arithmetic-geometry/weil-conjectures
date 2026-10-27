/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.AcyclicCoproductExtOrthogonalHom

/-!
# Acyclicity transferred by an Ext-orthogonal additive adjunction

Source: Stacks Project, Cohomology on Sites, Tag 07AC,
`lemma-existence-derived-lower-shriek`, proof of condition (2)
(blueprint: lem-trf-ext-orthogonal-adjoint-acyclic).
-/

@[expose] public section

set_option autoImplicit false

universe u w uB vB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An additive left adjoint preserves bounded-above acyclic complexes of coproducts
of a family Ext-orthogonal to the right adjoint of every injective.

Source: Stacks Project, Cohomology on Sites, Tag 07AC, proof of condition (2)
(blueprint: lem-trf-ext-orthogonal-adjoint-acyclic).

Positive Ext is computed by Hom into an injective resolution `Q`. Existence of such
`Q` with the stated vanishing expresses resolution-independent Ext vanishing.
The Hom complexes have degree-n terms Hom(P^(-n),T V) and Hom(L(P^(-n)),V),
identified by `Cochain.toSingleEquiv (neg_add_cancel n)`. Their differential is
h ↦ (-1)^(n+1) (d_P^(-n-1) ≫ h), by `Cochain.δ_toSingleMk`.
The last clause fixes the chain isomorphism to be the inverse adjunction bijection
on these terms. The two `uliftFunctor`s put abelian groups of potentially different
Hom universes in one common universe; they impose no equality of universe levels.

Proof:
1. Fix an injective V in B. Apply lem-trf-acyclic-coproduct-ext-orthogonal-hom
   with F=T V and its resolution Q from hExt. Its Ext, boundedness, acyclicity,
   and coproduct hypotheses are precisely hExt, hbounded, hacyclic, and hterms.
   It gives acyclicity of Hom(P,T V) with the stated signed differential.
2. The adjunction sends f:L X→V to T(f)∘η_X. Additivity of T makes this an
   additive bijection. Naturality of η gives α_X(f∘L(a))=α_Y(f)∘a for a:X→Y.
   Set a=d_P^(-n-1) and multiply by (-1)^(n+1). The inverse bijections therefore
   assemble into the specified chain isomorphism, so Hom(L(P),V) is acyclic too.
3. Put D=L(P). Fix r, let q:D^r→Q be coker(d_D^(r-1)), and let bar-d:Q→D^(r+1)
   be induced by d_D^r. Its kernel i:H→Q is H^r(D). Enough injectives gives a
   mono u:H→V with V injective. Extend u along i to v:Q→V. The map h=vq is a
   cocycle in Hom(D,V), hence a boundary by step 2. Absorbing the sign gives
   h=g d_D^r. Since q is epic, v=g bar-d, hence u=vi=g bar-d i=0. A zero mono
   has zero domain. Thus H^r(D)=0 for every r, proving D acyclic. -/
theorem acyclic_map_of_coproduct_ext_orthogonal_adjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (S : Sheaf J CommRingCat.{u})
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    (L : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤ B)
    (T : B ⥤ ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    [L.Additive] [T.Additive] (adj : L ⊣ T)
    {I : Type w}
    (E : I → ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hExt : ∀ (V : B) [Injective V], ∃ Q : InjectiveResolution (T.obj V),
      ∀ (i : I) (p : ℕ), 0 < p →
        IsZero ((((preadditiveCoyoneda.obj (op (E i))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj Q.cocomplex).homology p))
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n))
    (hacyclic : P.Acyclic)
    (hterms : ∀ n : ℤ, ∃ (A : Type u) (i : A → I),
      Nonempty (P.X n ≅ ∐ (fun a : A ↦ E (i a)))) :
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).Acyclic ∧
      ∀ (V : B) [Injective V],
        (CochainComplex.HomComplex P
          ((CochainComplex.singleFunctor _ 0).obj (T.obj V))).Acyclic ∧
        (CochainComplex.HomComplex ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((CochainComplex.singleFunctor B 0).obj V)).Acyclic ∧
        ∃ e : (AddCommGrpCat.uliftFunctor.{max u vB, u}.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (CochainComplex.HomComplex P
              ((CochainComplex.singleFunctor _ 0).obj (T.obj V))) ≅
          (AddCommGrpCat.uliftFunctor.{max u vB, vB}.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (CochainComplex.HomComplex ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((CochainComplex.singleFunctor B 0).obj V)),
          ∀ (n : ℤ) (h : P.X (-n) ⟶ T.obj V),
            e.hom.f n (ULift.up
              (CochainComplex.HomComplex.Cochain.toSingleMk h (neg_add_cancel n))) =
            ULift.up (CochainComplex.HomComplex.Cochain.toSingleMk
              ((adj.homEquiv (P.X (-n)) V).symm h) (neg_add_cancel n)) := by
  sorry

end CategoryTheory
