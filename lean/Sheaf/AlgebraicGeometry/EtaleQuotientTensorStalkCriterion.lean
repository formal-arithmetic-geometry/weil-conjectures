/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Normalized quotient tensor products on the étale site

Source: Stacks Project, Tags 03PT and 03PU, and the support-quotient refinement of
blueprint main-20261015, `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion).

Module-valued sheaves encode modules over the constant ring sheaf via the published
constant-scalar equivalence. The tensor is the existing sheafified tensor; its unit is
that constant ring module. The section product below is the unit multiplication, so
sections may be locally constant rather than globally constant. The stalk unit map
is the canonical identification of the constant ring stalk with the coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})

/-- The tensor of the two quotient generators, with one sent to one tensor one.
Source: support-quotient refinement of `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion). -/
def etaleQuotientTensorGenerator
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F)
    (s : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ G) :
    𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F ⊗ G :=
  (λ_ (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))).inv ≫ (q ⊗ₘ s)

/-- The specified normalized stalk identifications: on the subset there is an
A-linear identification with A carrying the quotient map to the canonical unit-stalk
identification; off the subset the stalk is zero. An identification with a zero module
and its zero map is unique, so the latter clause retains exactly the off-support data.
Source: support-quotient refinement of `lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion). -/
def EtaleQuotientStalkNormalized
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)} (S : Set T)
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
    (t (IsLocalRing.closedPoint Ω) ∈ S →
      ∃ i : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F ≅ ModuleCat.of A A,
        ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map q ≫ i.hom =
          Functor.OplaxMonoidal.η
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} A))) ∧
    (t (IsLocalRing.closedPoint Ω) ∉ S →
      IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F))

/-- Normalized quotient multiplication, with its section and stalk formulas.
Source: Stacks 03PT (exact stalks), 03PU (conservativity), and blueprint
`lem-pur-kunneth-supported`, final paragraph
(blueprint: lem-pur-etale-quotient-tensor-stalk-criterion).

Proof:
1. The constant-ring module equivalence and the sheafification-tensor comparison
identify the tensor over A_T with the sheafification of the presheaf tensor over A.
2. The geometric stalk tensor comparison sends the generator to q_t(c) tensor s_t(1).
On E intersect D this is c tensor one, inverse to multiplication. Elsewhere at least
one factor vanishes, so the tensor stalk vanishes. Its kernel is the kernel of r_t.
3. Module sheaves are abelian. Their faithful exact forgetful functor, exact stalks
and geometric-stalk conservativity imply the cokernel of the generator is zero.
The preadditive epi/cokernel criterion therefore makes the generator epic.
4. The kernel inclusion followed by r is zero on every geometric stalk, hence zero
by exactness and conservativity. This uses the normalization, not just stalk ranks.
5. The exact-epi cokernel universal property gives the unique e with m followed by e
 equal to r. Epimorphic cancellation gives uniqueness among all morphisms.
6. Its stalk is multiplication on the intersection, with inverse c tensor one;
off the intersection it is the unique zero-to-zero map. Conservativity gives the
isomorphism. The inverse is module-linear because e is module-linear and invertible.
7. Bilinearity gives q(a) tensor s(b) = m(ab) on local sections before sheafification
and hence after it. Applying e gives r(ab). Flatness is retained, though unused.
The cited proof dependencies are respectively the constant-ring equivalence,
module-sheafification tensor, stalk-tensor comparison, module-sheaf forgetful theorem,
exact geometric stalks, conservativity, and the exact-epi cokernel lemma. -/
theorem etale_quotient_tensor_stalk_criterion
    (E D : Set T) (F G H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ F)
    (s : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ G)
    (r : 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶ H)
    [Epi q] [Epi s] [Epi r]
    (hflat : exactFunctor _ _ (tensorRight F))
    (hq : EtaleQuotientStalkNormalized A T E q)
    (hs : EtaleQuotientStalkNormalized A T D s)
    (hr : EtaleQuotientStalkNormalized A T (E ∩ D) r) :
    Epi (etaleQuotientTensorGenerator A T q s) ∧
    ∃ e : F ⊗ G ≅ H,
      etaleQuotientTensorGenerator A T q s ≫ e.hom = r ∧
      (∀ f : F ⊗ G ⟶ H, etaleQuotientTensorGenerator A T q s ≫ f = r → f = e.hom) ∧
      (∀ (U : T.Etaleᵒᵖ)
        (a b : (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj.obj U),
        (e.hom.hom.app U)
          ((Functor.LaxMonoidal.μ
            (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) F G).app U
              ((q.hom.app U a) ⊗ₜ[A] (s.hom.app U b))) =
        r.hom.app U
          (((λ_ (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))).hom.hom.app U)
            ((Functor.LaxMonoidal.μ
              (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
                (𝟙_ _) (𝟙_ _)).app U (a ⊗ₜ[A] b)))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        (t (IsLocalRing.closedPoint Ω) ∈ E ∩ D →
          ∀ (iF : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj F ≅ ModuleCat.of A A)
            (iG : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj G ≅ ModuleCat.of A A)
            (iH : ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj H ≅ ModuleCat.of A A),
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map q ≫ iF.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map s ≫ iG.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map r ≫ iH.hom =
              Functor.OplaxMonoidal.η
                ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) →
            (∀ a b : A, iH.hom
              ((((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.hom)
                (Functor.LaxMonoidal.μ ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) F G
                  ((iF.inv a) ⊗ₜ[A] (iG.inv b)))) = a * b) ∧
            (∀ c : A, (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.inv)
              (iH.inv c) =
                Functor.LaxMonoidal.μ ((pointSmallEtale t).ulift.{u + 1}.sheafFiber) F G
                  ((iF.inv c) ⊗ₜ[A] (iG.inv 1)))) ∧
        (t (IsLocalRing.closedPoint Ω) ∉ E ∩ D →
          IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj (F ⊗ G)) ∧
          IsZero (((pointSmallEtale t).ulift.{u + 1}.sheafFiber).obj H) ∧
          ((pointSmallEtale t).ulift.{u + 1}.sheafFiber).map e.hom = 0)) := by
  sorry

end AlgebraicGeometry.Scheme
