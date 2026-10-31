/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  (T : A ⥤ A) [T.Additive] [T.IsEquivalence] [T.Braided]
  (B : A ⥤ A) (b : B ⟶ 𝟭 A)
structure MonoidalCyclicFlatCore where
  /-- The diagonal monoidal structure. -/
  [monoidal : MonoidalCategory (IsoAlgebra T)]
  /-- Its tensor is additive in each variable. -/
  [monoidalPreadditive : MonoidalPreadditive (IsoAlgebra T)]
  /-- Its symmetry is inherited from the underlying category. -/
  [symmetric : SymmetricCategory (IsoAlgebra T)]
  /-- Its tensor has internal right adjoints. -/
  [closed : MonoidalClosed (IsoAlgebra T)]
  /-- The forgetful functor is strong symmetric monoidal. -/
  [forgetBraided : (forget T).Braided]
  /-- The fixed-pair category is Grothendieck in the chosen universe. -/
  [grothendieck : IsGrothendieckAbelian.{w} (IsoAlgebra T)]
  /-- Countable sums used by the underlying total tensor. -/
  [countableUnderlying : HasCountableCoproducts A]
  /-- Countable sums used by the fixed-pair total tensor. -/
  [countableFixed : HasCountableCoproducts (IsoAlgebra T)]
  /-- The tensor fixed pair with the diagonal structure isomorphism. -/
  tensor_object (M N : IsoAlgebra T) :
    M ⊗ N = mk (M.carrier ⊗ N.carrier)
      ((Functor.Monoidal.μIso T M.carrier N.carrier).symm ≪≫
        tensorIso M.str N.str)
  /-- The monoidal unit with the inverse unit comparison of T. -/
  unit_object : 𝟙_ (IsoAlgebra T) = mk (𝟙_ A) (Functor.Monoidal.εIso T).symm
  /-- The forgetful tensor comparison is the identity on the specified carriers. -/
  forget_tensor (M N : IsoAlgebra T) :
    (Functor.Monoidal.μIso (forget T) M N).hom =
      eqToHom (congrArg carrier (tensor_object M N)).symm
  /-- The forgetful unit comparison is the identity on the specified carrier. -/
  forget_unit : (Functor.Monoidal.εIso (forget T)).hom =
    eqToHom (congrArg carrier unit_object).symm
  /-- Forgetting preserves finite limits. -/
  forget_leftExact : PreservesFiniteLimits (forget T)
  /-- Forgetting preserves finite colimits. -/
  forget_rightExact : PreservesFiniteColimits (forget T)
  /-- Forgetting detects isomorphisms. -/
  forget_conservative : (forget T).ReflectsIsomorphisms
  /-- All small limits are created by forgetting. -/
  forget_createsLimits : CreatesLimitsOfSize.{w, w} (forget T)
  /-- All small colimits are created by forgetting. -/
  forget_createsColimits : CreatesColimitsOfSize.{w, w} (forget T)
  /-- Internal Hom on carriers, including its canonical evaluation and twisted structure. -/
  internalHom (M N : IsoAlgebra T) :
    ∃ (h : ((ihom M).obj N).carrier ≅ (ihom M.carrier).obj N.carrier)
      (γ : T.obj ((ihom M.carrier).obj N.carrier) ≅
        (ihom (T.obj M.carrier)).obj (T.obj N.carrier)),
      γ.hom = MonoidalClosed.curry
        ((Functor.Monoidal.μIso T M.carrier ((ihom M.carrier).obj N.carrier)).hom ≫
          T.map ((ihom.ev M.carrier).app N.carrier)) ∧
      T.map h.hom ≫ γ.hom ≫ MonoidalClosed.curry
        ((M.str.inv ▷ (ihom (T.obj M.carrier)).obj (T.obj N.carrier)) ≫
          (ihom.ev (T.obj M.carrier)).app (T.obj N.carrier) ≫ N.str.hom) =
        ((ihom M).obj N).str.hom ≫ h.hom ∧
      (Functor.Monoidal.μIso (forget T) M ((ihom M).obj N)).hom ≫
        (forget T).map ((ihom.ev M).app N) =
          (M.carrier ◁ h.hom) ≫ (ihom.ev M.carrier).app N.carrier
  /-- Cyclic induction is left exact. -/
  induction_leftExact : PreservesFiniteLimits (Free.functor T)
  /-- Cyclic induction is right exact. -/
  induction_rightExact : PreservesFiniteColimits (Free.functor T)
  /-- Its adjunction is the existing degree-zero induction adjunction. -/
  induction_adjunction : Nonempty (Free.functor T ⊣ forget T)
  /-- The carrier of induction is the coproduct of the coherent integer powers. -/
  induction_carrier (N : A) : ((Free.functor T).obj N).carrier = ∐ (Free.obj T N)
  /-- Its structure reindexes the integer powers by the successor map. -/
  induction_structure (N : A) (j : ℤ) :
    T.map (Sigma.ι (Free.obj T N) j) ≫ ((Free.functor T).obj N).str.hom =
      (Free.objSucc T N j).hom ≫ Sigma.ι (Free.obj T N) (j + 1)
  /-- Induction of the given flat cover has flat values. -/
  flat_cover (M : IsoAlgebra T) :
    ObjectProperty.flat ((Free.functor T).obj (B.obj M.carrier))
  /-- The specified natural composite is epic at each fixed pair. -/
  cover_epi (M : IsoAlgebra T) :
    Epi ((Free.functor T).map (b.app M.carrier) ≫ (Free.adjunction T).counit.app M)
  /-- Flatness is detected and preserved on carriers. -/
  flat_iff (M : IsoAlgebra T) : ObjectProperty.flat M ↔ ObjectProperty.flat M.carrier
  /-- K-flatness is detected and preserved by the termwise forgetful functor. -/
  kflat_iff (P : CochainComplex (IsoAlgebra T) ℤ) :
    P.IsKFlatForTotalTensor ↔
      CochainComplex.IsKFlatForTotalTensor
        (((forget T).mapHomologicalComplex (.up ℤ)).obj P)
  /-- The acyclic tensor test agrees with the two-sided quasi-isomorphism test. -/
  kflat_acyclic_iff (P : CochainComplex (IsoAlgebra T) ℤ) :
    P.IsKFlatForTotalTensor ↔
      ∀ Q : CochainComplex (IsoAlgebra T) ℤ, Q.Acyclic →
        (HomologicalComplex.tensorObj P Q).Acyclic ∧
          (HomologicalComplex.tensorObj Q P).Acyclic


/-- The fixed-pair core data exist under the stated hypotheses.
Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, step (2),
auxiliary fixed-pair monoidal and acyclic-test construction.
(blueprint: lem-pur-monoidal-cyclic-flat-core).

Proof:
1. The created abelian structure theorem lifts every limit and colimit along `forget T`.
   Its faithful exact conservative functor reflects exactness. Filtered colimits are exact
   since their finite-limit comparisons become isomorphisms after forgetting. By the exact
   induction adjunction, induction of a generator of A is a generator of the fixed pairs.
   Thus the fixed-pair category is Grothendieck; shrinking sums gives countable coproducts.
2. On carriers define tensor and unit exactly by `tensor_object` and `unit_object`.
   Tensor maps are tensor products of the carrier maps. Naturality of the tensorator proves
   equivariance. The associator, unitors and braiding of A are equivariant by the strong
   braided functor axioms; faithfulness transfers pentagon, triangle and symmetry identities.
   The forgetful comparisons are identities. The restricted currying equivalence of
   `fixedPair_internalHom_currying` supplies the right adjoint with conjugated internal Hom.
   Its carrier evaluation is ordinary evaluation, giving the displayed normalization.
3. Use the existing integer-power induction and its degree-zero adjunction. The structural
   and carrier formulas are its defining formulas; exact sums make induction exact. Its
   counit has identity degree-zero component, so the proposed cover restricts to `b` there
   and is epic. Monoidal equivalences preserve flatness by transporting exact tensor tests.
   Thus all translates of B(UM) are flat, and their coproduct is flat by exact sums and
   preservation of coproducts by tensor. If UM is flat, exact conservative forgetting shows
   M is flat. Conversely tensor M with an induced short exact sequence. Its carrier has
   the original sequence tensored with UM as its degree-zero direct-summand retract, proving
   flatness of UM. Symmetry gives the second tensor side.
4. Exact forgetting commutes with homology and reflects acyclicity. Its tensor comparison
   identifies termwise-forgotten total tensors with underlying total tensors, since it
   preserves the countable sums defining their terms. Hence underlying K-flatness implies
   fixed-pair K-flatness. Conversely induce an acyclic test complex; exact induction keeps
   it acyclic. The underlying tensor has the original underlying tensor test as a direct
   summand, with inclusion and projection commuting with the differentials. Retracts of
   acyclic complexes are acyclic. Apply the same argument on both sides. Finally the cone
   criterion for quasi-isomorphisms and the signed tensor-cone comparison identify the
   acyclic-test condition with the two-sided quasi-isomorphism preservation condition. -/
theorem monoidalCyclicFlatCore
    (hb_epi : ∀ M : A, Epi (b.app M))
    (hb_flat : ∀ M : A, ObjectProperty.flat (B.obj M)) :
    Nonempty (MonoidalCyclicFlatCore.{u, v, w} T B b) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
