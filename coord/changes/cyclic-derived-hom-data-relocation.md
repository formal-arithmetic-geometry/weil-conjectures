# Cyclic derived Hom data declarations

## Reason

Factor the existing data declarations into a publicly reexported data module so that the
strict-extension and raw five-term lemmas can import their statements without importing
the theorem that uses them. This is dependency factoring, not a timeout workaround.
No existing name, signature, visibility, definition body, or mathematical meaning changes.
No source-library module is edited. The item is held by N3.

## Old

All 24 data declarations below lived in
`Sheaf.CategoryTheory.CyclicDerivedHomExactSequence`. The complete original module is
quoted to retain each signature and definition verbatim.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Native derived morphisms of fixed pairs

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
the native-derived foundation is the agent-formulated DAG node below. Its detailed
proof uses Stacks Project, derived.tex, Tags 0149, 0152, 013K, 070I, 070J and 0159.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence).

`exists_cyclicDerivedHomBoundary` states the invariant/coinvariant exact sequence.
The normalized boundary is the actual boundary of the off-diagonal extension.
The other three theorems state naturality for exact functors, total right derived
functors, and finite composites, including the empty composite. The last theorem
requires bounded cohomology only at the endpoints, not at intermediate stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The derived structure isomorphism D(P)D(U) ≅ D(U), obtained by localizing the termwise structure
isomorphisms and using the canonical exact-functor composition comparison.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedStructure :
    (forget F).mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      (forget F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (forget F) F).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun K ↦ K.str) (fun f ↦ f.hom.h))

/-- The underlying degree-r derived Hom group V^r. The shift is in the ordinary derived category of
the underlying abelian category.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHom (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :=
  (forget F).mapDerivedCategory.obj M ⟶ ((forget F).mapDerivedCategory.obj N)⟦r⟧

/-- The additive action u ↦ θ_N[r] D(P)(u) θ_M⁻¹, with the canonical shift comparison of the exact
functor D(P).

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomAction (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    CyclicDerivedHom F M N r →+ CyclicDerivedHom F M N r :=
  (Preadditive.rightComp _
    ((F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
      ((cyclicDerivedStructure F).hom.app N)⟦r⟧')).comp
    ((Preadditive.leftComp _ ((cyclicDerivedStructure F).inv.app M)).comp
      F.mapDerivedCategory.mapAddHom)

/-- The endomorphism 1-T on the degree-r underlying derived Hom group.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomDefect (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    CyclicDerivedHom F M N r →+ CyclicDerivedHom F M N r :=
  AddMonoidHom.id _ - cyclicDerivedHomAction F M N r

/-- The subgroup ker(1-T) in degree zero.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomInvariants (M N : DerivedCategory (IsoAlgebra F)) :=
  (cyclicDerivedHomDefect F M N 0).ker

/-- The quotient coker(1-T) in degree minus one, as an abelian group.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomCoinvariants (M N : DerivedCategory (IsoAlgebra F)) :=
  CyclicDerivedHom F M N (-1) ⧸ (cyclicDerivedHomDefect F M N (-1)).range

/-- The additive forgetting map, followed by the canonical degree-zero shift identification. It
imposes no faithfulness assertion on native derived morphisms.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedForget (M N : DerivedCategory (IsoAlgebra F)) :
    (M ⟶ N) →+ CyclicDerivedHom F M N 0 :=
  (Preadditive.rightComp _
    ((shiftFunctorZero (DerivedCategory C) ℤ).inv.app
      ((forget F).mapDerivedCategory.obj N))).comp (forget F).mapDerivedCategory.mapAddHom

/-- A family of additive boundary maps from the degree-minus-one coinvariants to native derived
morphisms, indexed by pairs with bounded cohomology. Boundedness is Mathlib’s canonical
t-structure boundedness predicate.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomBoundary :=
  ∀ (M N : DerivedCategory (IsoAlgebra F)),
    DerivedCategory.TStructure.t.bounded M → DerivedCategory.TStructure.t.bounded N →
    CyclicDerivedHomCoinvariants F M N →+ (M ⟶ N)

/-- The displayed short exact sequence. The right arrow lands in the actual invariant subgroup and
its underlying map is forgetting. Injectivity, exactness and surjectivity express both zeros and
exactness at the middle term.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryExact (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (M N : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N),
    ∃ q : (M ⟶ N) →+ CyclicDerivedHomInvariants F M N,
      (∀ f : M ⟶ N, (q f).val = cyclicDerivedForget F M N f) ∧
      Function.Injective (b M N hM hN) ∧ Function.Exact (b M N hM hN) q ∧
      Function.Surjective q

/-- The boundary square under arbitrary precomposition and postcomposition by native derived
morphisms. The representative on the right uses precisely their underlying morphisms and the
degree-minus-one shift.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryNatural (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (M N M' N' : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    (hM' : DerivedCategory.TStructure.t.bounded M')
    (hN' : DerivedCategory.TStructure.t.bounded N')
    (a : M' ⟶ M) (c : N ⟶ N') (u : CyclicDerivedHom F M N (-1)),
    a ≫ b M N hM hN (QuotientAddGroup.mk u) ≫ c =
      b M' N' hM' hN' (QuotientAddGroup.mk
        ((forget F).mapDerivedCategory.map a ≫ u ≫
          ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧'))

/-- The degree-minus-one class of the off-diagonal chain map in a split underlying extension. The
exact forgetting comparison and inverse shift-cancellation isomorphism identify Q(A) with
Q(A)[1][-1]; no arbitrary map or sign is selected.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedOffDiagonalClass
    {S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)}
    (u : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₁) :
    CyclicDerivedHom F (DerivedCategory.Q.obj S.X₃)
      ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) (-1) :=
  (forget F).mapDerivedCategoryFactors.hom.app S.X₃ ≫ DerivedCategory.Q.map u ≫
    (forget F).mapDerivedCategoryFactors.inv.app S.X₁ ≫
    (forget F).mapDerivedCategory.map
      ((shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra F)) (1 : ℤ) (-1)
        (add_neg_cancel (1 : ℤ))).inv.app (DerivedCategory.Q.obj S.X₁)) ≫
    ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.app
      ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧)

/-- Normalization by the off-diagonal extension. Here S is a short exact sequence A → E → J, s
splits its underlying projection as a chain map, and the displayed degreewise equation says that
the off-diagonal entry is θ_A P(u). The boundary on [u] must equal Mathlib’s canonical
connecting morphism Q(J) → Q(A)[1]. Every term in the equation has the carrier type written
explicitly to avoid relying on local notation.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryNormalized (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)) (hS : S.ShortExact)
    (hM : DerivedCategory.TStructure.t.bounded (DerivedCategory.Q.obj S.X₃))
    (hN : DerivedCategory.TStructure.t.bounded ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧))
    (u : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₁)
    (s : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₂),
    s ≫ ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map S.g = 𝟙 _ →
    (∀ n : ℤ,
      F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
          (S.X₂.X n).str.hom =
        ((S.X₃.X n).str.hom ≫
          @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
        (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n)) ≫
          (S.X₁.X n).str.hom ≫
            @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))) →
    b (DerivedCategory.Q.obj S.X₃) ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) hM hN
      (QuotientAddGroup.mk (cyclicDerivedOffDiagonalClass F u)) =
        DerivedCategory.triangleOfSESδ hS



/-- The invariant/coinvariant sequence with its canonical boundary and naturality.

Proof plan, following node steps 1--8 and the uniqueness implicit in its normalization:
1. Use lem-sf-free-derived-weil-resolution: the exact free/forgetful adjunction gives
   the natural triangle IUM → IUM → M → IUM[1], with the specified summand formula.
2. Under adjunction, the component of an adjunct at summand n is the iterated structure
   map composed with P^n(u). Evaluating the differential at summand zero gives
   1-(T^r)⁻¹, and the counit gives precisely the forgetting map.
3. Apply lem-weil-pbc-hom-out-of-triangle-exact and rotations to obtain the five-term
   Hom segment in degrees -1 and 0, with boundary u ↦ u_tilde[1] δ_M.
4. The identity 1-T⁻¹ = -T⁻¹(1-T) identifies the actual kernels and images. Factor through
   the actual quotient and subgroup, retaining the free-resolution sign, to get exactness.
5. Naturality of the free triangle and adjunction gives the pre/postcomposition square;
   localization of the fixed-pair equation gives commutation with T.
6. By enough injectives, lem-weil-pbc-dplus-injective-representative and the K-injective
   Hom and shift lemmas, represent a degree-minus-one underlying morphism by a chain
   map u: UJ → UA, with A representing N[-1].
7. On UA ⊕ UJ put the triangular action with diagonal θ_A, θ_J and upper entry θ_A P(u).
   Its inverse has upper entry -P(u)θ_J⁻¹. Inclusion and projection give a short exact
   fixed-pair sequence with a split underlying chain sequence.
8. In the free comparison let s be the second inclusion, e its adjunct and f the adjunct
   of u. Evaluation at summand zero gives ed_J=jf and pe=ε_J. Naturality of the canonical
   SES boundary (lem-weil-pbc-complex-ses-triangle; Stacks Tag 0152) identifies its boundary
   with f[1]δ_J. Thus it has exactly the required normalization. Every quotient class has
   such a representative. Naturality and this formula force uniqueness after transport
   along the representing isomorphisms. No derived faithfulness claim is used.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem exists_cyclicDerivedHomBoundary [IsGrothendieckAbelian.{v} C] :
    ∃! b : CyclicDerivedHomBoundary F,
      CyclicDerivedHomBoundaryExact F b ∧ CyclicDerivedHomBoundaryNatural F b ∧
        CyclicDerivedHomBoundaryNormalized F b := by
  sorry

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]

/-- The underlying degree-r map for a functor on native derived objects, an underlying functor, its
specified shift comparison, and the specified comparison with forgetting. The comparison
direction is D(U′)J ≅ H D(U).

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomTransport
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D)
    (σ : ∀ r : ℤ, shiftFunctor (DerivedCategory C) r ⋙ H ≅
      H ⋙ shiftFunctor (DerivedCategory D) r)
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H)
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) (u : CyclicDerivedHom F M N r) :
    CyclicDerivedHom G (J.obj M) (J.obj N) r :=
  α.hom.app M ≫ H.map u ≫ (σ r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
    (α.inv.app N)⟦r⟧'

/-- A map of the entire exact sequence. The representative maps are additive and commute with T in
every degree, so they induce the prescribed maps on the actual kernel and quotient. The second
clause is the forgetting square and the last clause is the connecting-map square on every
quotient representative. Only source and final target boundedness are required.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryFunctorial
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D)
    (σ : ∀ r : ℤ, shiftFunctor (DerivedCategory C) r ⋙ H ≅
      H ⋙ shiftFunctor (DerivedCategory D) r)
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H) : Prop :=
  ∀ (M N : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    (hJM : DerivedCategory.TStructure.t.bounded (J.obj M))
    (hJN : DerivedCategory.TStructure.t.bounded (J.obj N)),
    (∀ r : ℤ,
      cyclicDerivedHomTransport F G J H σ α M N r 0 = 0 ∧
      ∀ u v : CyclicDerivedHom F M N r,
        cyclicDerivedHomTransport F G J H σ α M N r (u + v) =
          cyclicDerivedHomTransport F G J H σ α M N r u +
            cyclicDerivedHomTransport F G J H σ α M N r v) ∧
    (∀ (r : ℤ) (u : CyclicDerivedHom F M N r),
      cyclicDerivedHomTransport F G J H σ α M N r (cyclicDerivedHomAction F M N r u) =
        cyclicDerivedHomAction G (J.obj M) (J.obj N) r
          (cyclicDerivedHomTransport F G J H σ α M N r u)) ∧
    (∀ f : M ⟶ N,
      cyclicDerivedHomTransport F G J H σ α M N 0 (cyclicDerivedForget F M N f) =
        cyclicDerivedForget G (J.obj M) (J.obj N) (J.map f)) ∧
    (∀ u : CyclicDerivedHom F M N (-1),
      J.map (b M N hM hN (QuotientAddGroup.mk u)) =
        b' (J.obj M) (J.obj N) hJM hJN (QuotientAddGroup.mk
          (cyclicDerivedHomTransport F G J H σ α M N (-1) u)))

variable (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)

/-- The canonical exact-functor comparison with forgetting, obtained from the strict equality of the
ordinary transported functor with H after forgetting.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedExactForgetComparison [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    (mapOfNatIso e).mapDerivedCategory ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (mapOfNatIso e) (forget G)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (mapOfNatIsoCompForgetIso e) ≪≫
      Functor.mapDerivedCategoryCompIso (forget F) L

/-- Exact functors preserve the entire sequence, including its normalized boundary.

Proof plan, node steps 6--12 in the exact case:
1. Represent M and N by bounded-below complexes J,K of injectives in the fixed-pair
   category, using lem-weil-pbc-dplus-injective-representative. Forgetting preserves
   K-injectives by lem-sf-fixed-pair-derived-forget-comparison. The K-injective Hom
   and shift lemmas represent u by UJ → U(K[-1]).
2. Construct the off-diagonal extension A → E → J as above. Its degrees split in the
   fixed-pair category because A is termwise injective; E and the cone of its inclusion
   are bounded-below complexes of injectives, hence K-injective. The cone projection to
   J has contractible kernel, so it is a quasi-isomorphism by the cohomology long exact
   sequence and a homotopy equivalence by the K-injective Hom lemma.
3. Additivity preserves finite sums, shifts, cones and chain homotopies. An exact H
   acts termwise on the derived category (lem-sf-exact-functor-derived-triangulated).
   The formula -Qπ (Qq)⁻¹ of Stacks Tag 0152 is consequently preserved, including its sign.
4. Naturality of e gives the new upper entry H(θ_A)e P′H(u); thus the image extension
   is precisely the normalized extension for the prescribed underlying morphism.
   The normalization predicates identify its boundary with the required target boundary.
5. The fixed-pair equation and the canonical comparison show additivity, T-compatibility,
   and the forgetting square. The two boundary naturality predicates transport these
   calculations from representatives to all native derived objects and morphisms.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem cyclicDerivedHom_exact_functorial [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hb' : CyclicDerivedHomBoundaryNormalized G b')
    (hn : CyclicDerivedHomBoundaryNatural F b)
    (hn' : CyclicDerivedHomBoundaryNatural G b') :
    CyclicDerivedHomBoundaryFunctorial F G b b' (mapOfNatIso e).mapDerivedCategory
      L.mapDerivedCategory (fun r ↦ L.mapDerivedCategory.commShiftIso r)
        (cyclicDerivedExactForgetComparison F G L e) := by
  sorry

/-- The unique comparison supplied by lem-sf-fixed-pair-derived-forget-comparison. Its derived-unit
equation fixes the comparison to the identity on the common K-injective computation H(UI). This
definition chooses a uniquely specified isomorphism, not an arbitrary comparison.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedRightForgetComparison [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L]
    (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF ⋙
      (forget G).mapDerivedCategory ≅
        (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC :=
  Classical.choose (exists_fixedPairDerivedForgetComparison F G L e hF hC)

/-- Total right derived functors preserve the normalized connecting map.

Proof plan, node steps 6--12 in the left exact case:
1. Use bounded-below injective representatives and the off-diagonal extension as in the
   exact-functor proof. The injectivity extension property splits its degrees, so A,E,J
   and the cone are K-injective (def-sp-injective-resolutions and the dplus/K-injective
   nodes). The cone projection is a homotopy equivalence.
2. The recorded right-derived universal pair computes RH^eq on these representatives
   by H^eq. Its shift comparison is induced by shifting K-injective resolutions; the
   universal property makes it coherent and compatible with its unit. The same argument
   supplies the underlying shift comparison for RH (lem-pc-right-derived-functor-
   triangulated, transported to the arbitrary-resolution interface).
3. Additivity of H^eq preserves the degreewise split sequence, its cone, the cone
   projection and its homotopy inverse. The formula -Qπ (Qq)⁻¹ therefore proves preservation
   of the actual SES boundary, even when H^eq is not exact on arbitrary sequences.
4. The unique comparison of lem-sf-fixed-pair-derived-forget-comparison identifies both
   computations with H(UI), and has the identity normalization there. Naturality of e
   identifies the image off-diagonal entry with θ_FA P′H(u). Normalization of b and b′
   and their morphism naturality give the left square on the specified quotient class.
5. The same unit and shift comparisons give the induced maps on every V^r. Their
   additivity and T-compatibility give the prescribed outer maps, and forgetting gives
   the right square. Resolution witnesses are universally quantified proof choices;
   their existence is the Grothendieck K-injective theorem, not an added hypothesis.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem cyclicDerivedHom_rightDerived_functorial [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L]
    (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hb' : CyclicDerivedHomBoundaryNormalized G b')
    (hn : CyclicDerivedHomBoundaryNatural F b)
    (hn' : CyclicDerivedHomBoundaryNatural G b') :
    ∃ (sF : ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ)
      (sC : (L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ),
      (fun [_sF : ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ]
        [_sC : (L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] ↦
        NatTrans.CommShift ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF) ℤ ∧
        NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ ∧
        CyclicDerivedHomBoundaryFunctorial F G b b'
          ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
          (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
          (cyclicDerivedRightForgetComparison F G L e hF hC)) (_sF := sF) (_sC := sC) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

set_option linter.checkUnivs false in
/-- One vertex of a finite composable diagram: a Grothendieck abelian category, its additive
autoequivalence, and the ordinary derived categories in chosen morphism universes. The object,
morphism, base-localization and fixed-pair-localization universes remain separate. The universe
linter is suppressed only for this data package because its sort is their common maximum.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
structure CyclicDerivedSetting where
  category : Type u
  [categoryStruct : Category.{v} category]
  [abelian : Abelian category]
  [grothendieck : IsGrothendieckAbelian.{v} category]
  action : category ⥤ category
  [additive : action.Additive]
  [equivalence : action.IsEquivalence]
  [derived : HasDerivedCategory.{w} category]
  [fixedDerived : HasDerivedCategory.{wF} (IsoAlgebra action)]

attribute [instance] CyclicDerivedSetting.categoryStruct CyclicDerivedSetting.abelian
  CyclicDerivedSetting.grothendieck CyclicDerivedSetting.additive
  CyclicDerivedSetting.equivalence CyclicDerivedSetting.derived CyclicDerivedSetting.fixedDerived

/-- One arrow of a finite composable diagram, carrying its native and underlying functors, coherent
underlying shift comparison, and comparison with forgetting. The Generated predicate below
restricts these data to exactly the functors named in the node.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
structure CyclicDerivedTransport (X Y : CyclicDerivedSetting.{u, v, w, wF}) where
  native : DerivedCategory (IsoAlgebra X.action) ⥤ DerivedCategory (IsoAlgebra Y.action)
  underlying : DerivedCategory X.category ⥤ DerivedCategory Y.category
  shifts : underlying.CommShift ℤ
  comparison : native ⋙ (forget Y.action).mapDerivedCategory ≅
    (forget X.action).mapDerivedCategory ⋙ underlying

namespace CyclicDerivedTransport

variable {X Y Z : CyclicDerivedSetting.{u, v, w, wF}}

/-- The coherent shift comparison stored in a transport datum, exposed without installing a
competing global instance.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def shiftIso (t : CyclicDerivedTransport X Y) (r : ℤ) :
    shiftFunctor (DerivedCategory X.category) r ⋙ t.underlying ≅
      t.underlying ⋙ shiftFunctor (DerivedCategory Y.category) r :=
  (fun [_s : t.underlying.CommShift ℤ] ↦ t.underlying.commShiftIso r) (_s := t.shifts)

/-- The canonical transport datum of an additive exact functor equipped with the specified
commutation isomorphism with the autoequivalences.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def exact (L : X.category ⥤ Y.category) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ⋙ Y.action ≅ X.action ⋙ L) : CyclicDerivedTransport X Y where
  native := (mapOfNatIso e).mapDerivedCategory
  underlying := L.mapDerivedCategory
  shifts := inferInstance
  comparison := cyclicDerivedExactForgetComparison X.action Y.action L e

/-- The transport datum of the recorded total right derived functors, for arbitrary K-injective
resolution witnesses. Its forgetting comparison is the unique unit-normalized one. The Generated
constructor requires that the chosen underlying shift comparison commute with the derived unit.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def rightDerived (L : X.category ⥤ Y.category) [L.Additive] [PreservesFiniteLimits L]
    (e : L ⋙ Y.action ≅ X.action ⋙ L)
    (hX : ∀ K : CochainComplex (IsoAlgebra X.action) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra X.action) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hA : ∀ K : CochainComplex X.category ℤ,
      ∃ (I : CochainComplex X.category ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (σ : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ) :
    CyclicDerivedTransport X Y where
  native := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hX
  underlying := L.rightDerivedFunctorOfQuasiIsoResolutions hA
  shifts := σ
  comparison := cyclicDerivedRightForgetComparison X.action Y.action L e hX hA

/-- Composition of two transport data. Both functors are composed, the shift structure is the
standard composite, and the forgetting comparison is the pasted comparison, with the canonical
associators.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def comp (s : CyclicDerivedTransport X Y) (t : CyclicDerivedTransport Y Z) :
    CyclicDerivedTransport X Z where
  native := s.native ⋙ t.native
  underlying := s.underlying ⋙ t.underlying
  shifts := (fun [_s : s.underlying.CommShift ℤ] [_t : t.underlying.CommShift ℤ] ↦
    inferInstanceAs ((s.underlying ⋙ t.underlying).CommShift ℤ)) (_s := s.shifts) (_t := t.shifts)
  comparison := Functor.associator s.native t.native (forget Z.action).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft s.native t.comparison ≪≫
    (Functor.associator s.native (forget Y.action).mapDerivedCategory t.underlying).symm ≪≫
    Functor.isoWhiskerRight s.comparison t.underlying ≪≫
    Functor.associator (forget X.action).mapDerivedCategory s.underlying t.underlying

/-- The transport datum of the empty composite, with identity functors and the canonical unitors.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def id (X : CyclicDerivedSetting.{u, v, w, wF}) : CyclicDerivedTransport X X where
  native := 𝟭 _
  underlying := 𝟭 _
  shifts := inferInstance
  comparison := Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

/-- Finite composites of exactly the admissible exact and total right derived transports, including
the identity. The right-derived constructor retains the canonical unit-compatible shift
comparison. No condition on the cohomological bounds of intermediate images occurs in this
inductive predicate.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
inductive Generated : {X Y : CyclicDerivedSetting.{u, v, w, wF}} →
    CyclicDerivedTransport X Y → Prop where
  | id (X : CyclicDerivedSetting.{u, v, w, wF}) : Generated (id X)
  | exact {X Y : CyclicDerivedSetting.{u, v, w, wF}}
      (L : X.category ⥤ Y.category) [L.Additive]
      [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      (e : L ⋙ Y.action ≅ X.action ⋙ L) : Generated (exact L e)
  | rightDerived {X Y : CyclicDerivedSetting.{u, v, w, wF}}
      (L : X.category ⥤ Y.category) [L.Additive] [PreservesFiniteLimits L]
      (e : L ⋙ Y.action ≅ X.action ⋙ L)
      (hX : ∀ K : CochainComplex (IsoAlgebra X.action) ℤ,
        ∃ (I : CochainComplex (IsoAlgebra X.action) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
      (hA : ∀ K : CochainComplex X.category ℤ,
        ∃ (I : CochainComplex X.category ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
      (σ : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ)
      (hσ : (fun [_s : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ] ↦
        NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ℤ) (_s := σ)) :
      Generated (rightDerived L e hX hA σ)
  | comp {X Y Z : CyclicDerivedSetting.{u, v, w, wF}}
      {s : CyclicDerivedTransport X Y} {t : CyclicDerivedTransport Y Z}
      (hs : Generated s) (ht : Generated t) : Generated (s.comp t)

end CyclicDerivedTransport

/-- Finite composites preserve the entire sequence with only endpoint boundedness.

Proof plan, node step 12, with steps 6--11 applied at each stage:
1. For an exact generator use termwise localization and the normalized extension
   computation. For a right-derived generator use K-injective resolutions, its
   unit-compatible shift comparison, and the unique forgetting comparison. These are
   precisely the calculations of the two preceding theorems on representatives.
2. Run the same calculations first for bounded-below complexes: only a lower bound was
   used in the injective, cone and off-diagonal arguments. Exact functors preserve such
   a bound termwise, and a right derived left exact functor preserves it by applying H
   to a bounded-below injective representative. An intermediate image need not have an
   upper bound. The same construction therefore supplies the auxiliary lower-bounded
   boundary during induction, without adding an intermediate boundedness hypothesis.
3. Induct on Generated. The empty word is the identity. Paste the two normalized
   squares at a composition; the associators in comp are exactly the pasted forgetting
   comparison, and the stored shift is the standard composite shift. Representative
   maps on kernels and quotients compose since the underlying additive maps do.
4. At bounded source and final target identify the auxiliary boundaries with b and b′
   by their normalization and naturality, as in exists_cyclicDerivedHomBoundary.
   This proves all three clauses of functoriality for the finite composite.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem cyclicDerivedHom_finite_composite_functorial
    {X Y : CyclicDerivedSetting.{u, v, w, wF}} (t : CyclicDerivedTransport X Y)
    (ht : t.Generated)
    (b : CyclicDerivedHomBoundary X.action) (b' : CyclicDerivedHomBoundary Y.action)
    (hb : CyclicDerivedHomBoundaryNormalized X.action b)
    (hb' : CyclicDerivedHomBoundaryNormalized Y.action b')
    (hn : CyclicDerivedHomBoundaryNatural X.action b)
    (hn' : CyclicDerivedHomBoundaryNatural Y.action b') :
    CyclicDerivedHomBoundaryFunctorial X.action Y.action b b'
      t.native t.underlying t.shiftIso t.comparison := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
```

## New

The 24 data declarations now live verbatim in `Sheaf.CategoryTheory.CyclicDerivedHomData`.
The original module publicly imports that module, and keeps its four theorem signatures
unchanged. Its proof imports are private. The complete relocated module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-! # Data for native derived morphisms of fixed pairs

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
the native-derived foundation is the agent-formulated DAG node below. Its detailed
proof uses Stacks Project, derived.tex, Tags 0149, 0152, 013K, 070I, 070J and 0159.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence).

`exists_cyclicDerivedHomBoundary` states the invariant/coinvariant exact sequence.
The normalized boundary is the actual boundary of the off-diagonal extension.
The other three theorems state naturality for exact functors, total right derived
functors, and finite composites, including the empty composite. The last theorem
requires bounded cohomology only at the endpoints, not at intermediate stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The derived structure isomorphism D(P)D(U) ≅ D(U), obtained by localizing the termwise structure
isomorphisms and using the canonical exact-functor composition comparison.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedStructure :
    (forget F).mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      (forget F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (forget F) F).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun K ↦ K.str) (fun f ↦ f.hom.h))

/-- The underlying degree-r derived Hom group V^r. The shift is in the ordinary derived category of
the underlying abelian category.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHom (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :=
  (forget F).mapDerivedCategory.obj M ⟶ ((forget F).mapDerivedCategory.obj N)⟦r⟧

/-- The additive action u ↦ θ_N[r] D(P)(u) θ_M⁻¹, with the canonical shift comparison of the exact
functor D(P).

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomAction (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    CyclicDerivedHom F M N r →+ CyclicDerivedHom F M N r :=
  (Preadditive.rightComp _
    ((F.mapDerivedCategory.commShiftIso r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
      ((cyclicDerivedStructure F).hom.app N)⟦r⟧')).comp
    ((Preadditive.leftComp _ ((cyclicDerivedStructure F).inv.app M)).comp
      F.mapDerivedCategory.mapAddHom)

/-- The endomorphism 1-T on the degree-r underlying derived Hom group.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomDefect (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    CyclicDerivedHom F M N r →+ CyclicDerivedHom F M N r :=
  AddMonoidHom.id _ - cyclicDerivedHomAction F M N r

/-- The subgroup ker(1-T) in degree zero.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomInvariants (M N : DerivedCategory (IsoAlgebra F)) :=
  (cyclicDerivedHomDefect F M N 0).ker

/-- The quotient coker(1-T) in degree minus one, as an abelian group.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomCoinvariants (M N : DerivedCategory (IsoAlgebra F)) :=
  CyclicDerivedHom F M N (-1) ⧸ (cyclicDerivedHomDefect F M N (-1)).range

/-- The additive forgetting map, followed by the canonical degree-zero shift identification. It
imposes no faithfulness assertion on native derived morphisms.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedForget (M N : DerivedCategory (IsoAlgebra F)) :
    (M ⟶ N) →+ CyclicDerivedHom F M N 0 :=
  (Preadditive.rightComp _
    ((shiftFunctorZero (DerivedCategory C) ℤ).inv.app
      ((forget F).mapDerivedCategory.obj N))).comp (forget F).mapDerivedCategory.mapAddHom

/-- A family of additive boundary maps from the degree-minus-one coinvariants to native derived
morphisms, indexed by pairs with bounded cohomology. Boundedness is Mathlib’s canonical
t-structure boundedness predicate.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
abbrev CyclicDerivedHomBoundary :=
  ∀ (M N : DerivedCategory (IsoAlgebra F)),
    DerivedCategory.TStructure.t.bounded M → DerivedCategory.TStructure.t.bounded N →
    CyclicDerivedHomCoinvariants F M N →+ (M ⟶ N)

/-- The displayed short exact sequence. The right arrow lands in the actual invariant subgroup and
its underlying map is forgetting. Injectivity, exactness and surjectivity express both zeros and
exactness at the middle term.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryExact (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (M N : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N),
    ∃ q : (M ⟶ N) →+ CyclicDerivedHomInvariants F M N,
      (∀ f : M ⟶ N, (q f).val = cyclicDerivedForget F M N f) ∧
      Function.Injective (b M N hM hN) ∧ Function.Exact (b M N hM hN) q ∧
      Function.Surjective q

/-- The boundary square under arbitrary precomposition and postcomposition by native derived
morphisms. The representative on the right uses precisely their underlying morphisms and the
degree-minus-one shift.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryNatural (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (M N M' N' : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    (hM' : DerivedCategory.TStructure.t.bounded M')
    (hN' : DerivedCategory.TStructure.t.bounded N')
    (a : M' ⟶ M) (c : N ⟶ N') (u : CyclicDerivedHom F M N (-1)),
    a ≫ b M N hM hN (QuotientAddGroup.mk u) ≫ c =
      b M' N' hM' hN' (QuotientAddGroup.mk
        ((forget F).mapDerivedCategory.map a ≫ u ≫
          ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧'))

/-- The degree-minus-one class of the off-diagonal chain map in a split underlying extension. The
exact forgetting comparison and inverse shift-cancellation isomorphism identify Q(A) with
Q(A)[1][-1]; no arbitrary map or sign is selected.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedOffDiagonalClass
    {S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)}
    (u : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₁) :
    CyclicDerivedHom F (DerivedCategory.Q.obj S.X₃)
      ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) (-1) :=
  (forget F).mapDerivedCategoryFactors.hom.app S.X₃ ≫ DerivedCategory.Q.map u ≫
    (forget F).mapDerivedCategoryFactors.inv.app S.X₁ ≫
    (forget F).mapDerivedCategory.map
      ((shiftFunctorCompIsoId (DerivedCategory (IsoAlgebra F)) (1 : ℤ) (-1)
        (add_neg_cancel (1 : ℤ))).inv.app (DerivedCategory.Q.obj S.X₁)) ≫
    ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.app
      ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧)

/-- Normalization by the off-diagonal extension. Here S is a short exact sequence A → E → J, s
splits its underlying projection as a chain map, and the displayed degreewise equation says that
the off-diagonal entry is θ_A P(u). The boundary on [u] must equal Mathlib’s canonical
connecting morphism Q(J) → Q(A)[1]. Every term in the equation has the carrier type written
explicitly to avoid relying on local notation.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryNormalized (b : CyclicDerivedHomBoundary F) : Prop :=
  ∀ (S : ShortComplex (CochainComplex (IsoAlgebra F) ℤ)) (hS : S.ShortExact)
    (hM : DerivedCategory.TStructure.t.bounded (DerivedCategory.Q.obj S.X₃))
    (hN : DerivedCategory.TStructure.t.bounded ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧))
    (u : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₁)
    (s : ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₃ ⟶
      ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj S.X₂),
    s ≫ ((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).map S.g = 𝟙 _ →
    (∀ n : ℤ,
      F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) ≫
          (S.X₂.X n).str.hom =
        ((S.X₃.X n).str.hom ≫
          @id ((S.X₃.X n).carrier ⟶ (S.X₂.X n).carrier) (s.f n)) +
        (F.map (@id ((S.X₃.X n).carrier ⟶ (S.X₁.X n).carrier) (u.f n)) ≫
          (S.X₁.X n).str.hom ≫
            @id ((S.X₁.X n).carrier ⟶ (S.X₂.X n).carrier) ((forget F).map (S.f.f n)))) →
    b (DerivedCategory.Q.obj S.X₃) ((DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧) hM hN
      (QuotientAddGroup.mk (cyclicDerivedOffDiagonalClass F u)) =
        DerivedCategory.triangleOfSESδ hS





variable {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]

/-- The underlying degree-r map for a functor on native derived objects, an underlying functor, its
specified shift comparison, and the specified comparison with forgetting. The comparison
direction is D(U′)J ≅ H D(U).

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedHomTransport
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D)
    (σ : ∀ r : ℤ, shiftFunctor (DerivedCategory C) r ⋙ H ≅
      H ⋙ shiftFunctor (DerivedCategory D) r)
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H)
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) (u : CyclicDerivedHom F M N r) :
    CyclicDerivedHom G (J.obj M) (J.obj N) r :=
  α.hom.app M ≫ H.map u ≫ (σ r).hom.app ((forget F).mapDerivedCategory.obj N) ≫
    (α.inv.app N)⟦r⟧'

/-- A map of the entire exact sequence. The representative maps are additive and commute with T in
every degree, so they induce the prescribed maps on the actual kernel and quotient. The second
clause is the forgetting square and the last clause is the connecting-map square on every
quotient representative. Only source and final target boundedness are required.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def CyclicDerivedHomBoundaryFunctorial
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D)
    (σ : ∀ r : ℤ, shiftFunctor (DerivedCategory C) r ⋙ H ≅
      H ⋙ shiftFunctor (DerivedCategory D) r)
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H) : Prop :=
  ∀ (M N : DerivedCategory (IsoAlgebra F))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    (hJM : DerivedCategory.TStructure.t.bounded (J.obj M))
    (hJN : DerivedCategory.TStructure.t.bounded (J.obj N)),
    (∀ r : ℤ,
      cyclicDerivedHomTransport F G J H σ α M N r 0 = 0 ∧
      ∀ u v : CyclicDerivedHom F M N r,
        cyclicDerivedHomTransport F G J H σ α M N r (u + v) =
          cyclicDerivedHomTransport F G J H σ α M N r u +
            cyclicDerivedHomTransport F G J H σ α M N r v) ∧
    (∀ (r : ℤ) (u : CyclicDerivedHom F M N r),
      cyclicDerivedHomTransport F G J H σ α M N r (cyclicDerivedHomAction F M N r u) =
        cyclicDerivedHomAction G (J.obj M) (J.obj N) r
          (cyclicDerivedHomTransport F G J H σ α M N r u)) ∧
    (∀ f : M ⟶ N,
      cyclicDerivedHomTransport F G J H σ α M N 0 (cyclicDerivedForget F M N f) =
        cyclicDerivedForget G (J.obj M) (J.obj N) (J.map f)) ∧
    (∀ u : CyclicDerivedHom F M N (-1),
      J.map (b M N hM hN (QuotientAddGroup.mk u)) =
        b' (J.obj M) (J.obj N) hJM hJN (QuotientAddGroup.mk
          (cyclicDerivedHomTransport F G J H σ α M N (-1) u)))

variable (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)

/-- The canonical exact-functor comparison with forgetting, obtained from the strict equality of the
ordinary transported functor with H after forgetting.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedExactForgetComparison [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
    (mapOfNatIso e).mapDerivedCategory ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (mapOfNatIso e) (forget G)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (mapOfNatIsoCompForgetIso e) ≪≫
      Functor.mapDerivedCategoryCompIso (forget F) L



/-- The unique comparison supplied by lem-sf-fixed-pair-derived-forget-comparison. Its derived-unit
equation fixes the comparison to the identity on the common K-injective computation H(UI). This
definition chooses a uniquely specified isomorphism, not an arbitrary comparison.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def cyclicDerivedRightForgetComparison [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L]
    (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF ⋙
      (forget G).mapDerivedCategory ≅
        (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctorOfQuasiIsoResolutions hC :=
  Classical.choose (exists_fixedPairDerivedForgetComparison F G L e hF hC)



end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

set_option linter.checkUnivs false in
/-- One vertex of a finite composable diagram: a Grothendieck abelian category, its additive
autoequivalence, and the ordinary derived categories in chosen morphism universes. The object,
morphism, base-localization and fixed-pair-localization universes remain separate. The universe
linter is suppressed only for this data package because its sort is their common maximum.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
structure CyclicDerivedSetting where
  category : Type u
  [categoryStruct : Category.{v} category]
  [abelian : Abelian category]
  [grothendieck : IsGrothendieckAbelian.{v} category]
  action : category ⥤ category
  [additive : action.Additive]
  [equivalence : action.IsEquivalence]
  [derived : HasDerivedCategory.{w} category]
  [fixedDerived : HasDerivedCategory.{wF} (IsoAlgebra action)]

attribute [instance] CyclicDerivedSetting.categoryStruct CyclicDerivedSetting.abelian
  CyclicDerivedSetting.grothendieck CyclicDerivedSetting.additive
  CyclicDerivedSetting.equivalence CyclicDerivedSetting.derived CyclicDerivedSetting.fixedDerived

/-- One arrow of a finite composable diagram, carrying its native and underlying functors, coherent
underlying shift comparison, and comparison with forgetting. The Generated predicate below
restricts these data to exactly the functors named in the node.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
structure CyclicDerivedTransport (X Y : CyclicDerivedSetting.{u, v, w, wF}) where
  native : DerivedCategory (IsoAlgebra X.action) ⥤ DerivedCategory (IsoAlgebra Y.action)
  underlying : DerivedCategory X.category ⥤ DerivedCategory Y.category
  shifts : underlying.CommShift ℤ
  comparison : native ⋙ (forget Y.action).mapDerivedCategory ≅
    (forget X.action).mapDerivedCategory ⋙ underlying

namespace CyclicDerivedTransport

variable {X Y Z : CyclicDerivedSetting.{u, v, w, wF}}

/-- The coherent shift comparison stored in a transport datum, exposed without installing a
competing global instance.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def shiftIso (t : CyclicDerivedTransport X Y) (r : ℤ) :
    shiftFunctor (DerivedCategory X.category) r ⋙ t.underlying ≅
      t.underlying ⋙ shiftFunctor (DerivedCategory Y.category) r :=
  (fun [_s : t.underlying.CommShift ℤ] ↦ t.underlying.commShiftIso r) (_s := t.shifts)

/-- The canonical transport datum of an additive exact functor equipped with the specified
commutation isomorphism with the autoequivalences.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def exact (L : X.category ⥤ Y.category) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ⋙ Y.action ≅ X.action ⋙ L) : CyclicDerivedTransport X Y where
  native := (mapOfNatIso e).mapDerivedCategory
  underlying := L.mapDerivedCategory
  shifts := inferInstance
  comparison := cyclicDerivedExactForgetComparison X.action Y.action L e

/-- The transport datum of the recorded total right derived functors, for arbitrary K-injective
resolution witnesses. Its forgetting comparison is the unique unit-normalized one. The Generated
constructor requires that the chosen underlying shift comparison commute with the derived unit.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def rightDerived (L : X.category ⥤ Y.category) [L.Additive] [PreservesFiniteLimits L]
    (e : L ⋙ Y.action ≅ X.action ⋙ L)
    (hX : ∀ K : CochainComplex (IsoAlgebra X.action) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra X.action) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hA : ∀ K : CochainComplex X.category ℤ,
      ∃ (I : CochainComplex X.category ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (σ : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ) :
    CyclicDerivedTransport X Y where
  native := (mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hX
  underlying := L.rightDerivedFunctorOfQuasiIsoResolutions hA
  shifts := σ
  comparison := cyclicDerivedRightForgetComparison X.action Y.action L e hX hA

/-- Composition of two transport data. Both functors are composed, the shift structure is the
standard composite, and the forgetting comparison is the pasted comparison, with the canonical
associators.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def comp (s : CyclicDerivedTransport X Y) (t : CyclicDerivedTransport Y Z) :
    CyclicDerivedTransport X Z where
  native := s.native ⋙ t.native
  underlying := s.underlying ⋙ t.underlying
  shifts := (fun [_s : s.underlying.CommShift ℤ] [_t : t.underlying.CommShift ℤ] ↦
    inferInstanceAs ((s.underlying ⋙ t.underlying).CommShift ℤ)) (_s := s.shifts) (_t := t.shifts)
  comparison := Functor.associator s.native t.native (forget Z.action).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft s.native t.comparison ≪≫
    (Functor.associator s.native (forget Y.action).mapDerivedCategory t.underlying).symm ≪≫
    Functor.isoWhiskerRight s.comparison t.underlying ≪≫
    Functor.associator (forget X.action).mapDerivedCategory s.underlying t.underlying

/-- The transport datum of the empty composite, with identity functors and the canonical unitors.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
def id (X : CyclicDerivedSetting.{u, v, w, wF}) : CyclicDerivedTransport X X where
  native := 𝟭 _
  underlying := 𝟭 _
  shifts := inferInstance
  comparison := Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

/-- Finite composites of exactly the admissible exact and total right derived transports, including
the identity. The right-derived constructor retains the canonical unit-compatible shift
comparison. No condition on the cohomological bounds of intermediate images occurs in this
inductive predicate.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
inductive Generated : {X Y : CyclicDerivedSetting.{u, v, w, wF}} →
    CyclicDerivedTransport X Y → Prop where
  | id (X : CyclicDerivedSetting.{u, v, w, wF}) : Generated (id X)
  | exact {X Y : CyclicDerivedSetting.{u, v, w, wF}}
      (L : X.category ⥤ Y.category) [L.Additive]
      [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      (e : L ⋙ Y.action ≅ X.action ⋙ L) : Generated (exact L e)
  | rightDerived {X Y : CyclicDerivedSetting.{u, v, w, wF}}
      (L : X.category ⥤ Y.category) [L.Additive] [PreservesFiniteLimits L]
      (e : L ⋙ Y.action ≅ X.action ⋙ L)
      (hX : ∀ K : CochainComplex (IsoAlgebra X.action) ℤ,
        ∃ (I : CochainComplex (IsoAlgebra X.action) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
      (hA : ∀ K : CochainComplex X.category ℤ,
        ∃ (I : CochainComplex X.category ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
      (σ : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ)
      (hσ : (fun [_s : (L.rightDerivedFunctorOfQuasiIsoResolutions hA).CommShift ℤ] ↦
        NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) ℤ) (_s := σ)) :
      Generated (rightDerived L e hX hA σ)
  | comp {X Y Z : CyclicDerivedSetting.{u, v, w, wF}}
      {s : CyclicDerivedTransport X Y} {t : CyclicDerivedTransport Y Z}
      (hs : Generated s) (ht : Generated t) : Generated (s.comp t)

end CyclicDerivedTransport



end CategoryTheory.Endofunctor.IsoAlgebra
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.CyclicDerivedHomExactSequence --uses ...`
was run for every relocated declaration family. It finds one downstream module. All
names remain available through the original public import, so no consumer adaptation is
necessary. In particular no target definition or theorem changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CyclicDerivedHomExactSequence | N3 | Publicly reexports data; proves the main boundary theorem from two new results. |
| Sheaf.CategoryTheory.CyclicDerivedLiftedCounitRepresents | N4 | Same names, types, and definitions through its unchanged public import; no edits. |

## Status

landed 20261024T224936-L-1832607 2026-10-24 (merge of deliver/N3/Sheaf.CategoryTheory.CyclicDerivedHomExactSequence)
