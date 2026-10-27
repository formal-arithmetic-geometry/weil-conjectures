module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Frobenius and Verschiebung of an affine commutative group

Source: Milne, Algebraic Groups (2017), Definition 11.39 and Proposition 11.40(a),
printed pp. 224–225 (blueprint: lem-sfb-affine-group-frobenius-verschiebung).

The coordinate twist is the ring pushout along Frobenius, with its algebra structure
from the second factor. The projection is constructed from actual tensor-basis coordinates;
its restriction to invariant tensors is asserted to be independent of that basis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.AffineGroupFrobeniusVerschiebung

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coordinate twist `C ⊗[k, Frobenius] k`, realized by its ring pushout.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def twist (C : Type u) [CommRing C] [Algebra k C] : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom (algebraMap k C)) (CommRingCat.ofHom (frobenius k p))

/-- The second-factor scalar structure on the coordinate twist.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable instance twistAlgebra (C : Type u) [CommRing C] [Algebra k C] :
    Algebra k (twist k p C) :=
  (pushout.inr (CommRingCat.ofHom (algebraMap k C))
    (CommRingCat.ofHom (frobenius k p))).hom.toAlgebra

/-- The first-factor ring map `a ↦ a ⊗ 1`; it is Frobenius-semilinear.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def first (C : Type u) [CommRing C] [Algebra k C] : C →+* twist k p C :=
  (pushout.inl (CommRingCat.ofHom (algebraMap k C))
    (CommRingCat.ofHom (frobenius k p))).hom

/-- Pure tensors `a ⊗ c` in the Frobenius twist, with scalars on the second factor.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def pure (C : Type u) [CommRing C] [Algebra k C] (a : C) (c : k) :
    twist k p C := algebraMap k (twist k p C) c * first k p C a

/-- The fixed subspace of the tensor power under permutation of its factors.
Source: Milne, p. 224 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
def invariants (C : Type u) [AddCommGroup C] [Module k C] :
    Submodule k (⨂[k] (_ : Fin p), C) :=
  ⨅ e : Equiv.Perm (Fin p),
    LinearMap.ker ((PiTensorProduct.reindex k (fun _ : Fin p ↦ C) e).toLinearMap -
      LinearMap.id)

/-- The distinct tuples in a permutation orbit, so stabilizers cause no multiplicities.
Source: Milne, p. 224 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def orbit {J : Type u} (t : Fin p → J) : Finset (Fin p → J) := by
  classical
  exact Finset.univ.image (fun e : Equiv.Perm (Fin p) ↦ t ∘ e)

/-- The sum of the distinct basis tensors in a permutation orbit.
Source: Milne, p. 224 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def orbitSum {C J : Type u} [AddCommGroup C] [Module k C]
    (B : Module.Basis J k C) (t : Fin p → J) : ⨂[k] (_ : Fin p), C :=
  ∑ s ∈ orbit p t, PiTensorProduct.tprod k (fun i ↦ B (s i))

/-- An actual coordinate projection for a chosen basis, extended to the full tensor power.
Only its restriction to invariants is intrinsic. Source: Milne, Definition 11.39
(blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def projectionForBasis {C J : Type u} [CommRing C] [Algebra k C]
    (B : Module.Basis J k C) : (⨂[k] (_ : Fin p), C) →ₗ[k] twist k p C := by
  classical
  exact (Finsupp.linearCombination k (fun t : Fin p → J ↦
    if ∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩ then
      first k p C (B (t ⟨0, (Fact.out : p.Prime).pos⟩)) else 0)).comp
        (Basis.piTensorProduct (fun _ : Fin p ↦ B)).repr.toLinearMap

/-- A concrete projection using the standard chosen vector-space basis.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def projection (C : Type u) [CommRing C] [Algebra k C] :
    (⨂[k] (_ : Fin p), C) →ₗ[k] twist k p C :=
  projectionForBasis k p (Module.Basis.ofVectorSpace k C)

/-- The canonical invariant-tensor projection, defined by restricting the concrete projection.
Basis independence is a conclusion of `frobenius_verschiebung`, not an input hypothesis.
Source: Milne, Definition 11.39 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def invariantProjection (C : Type u) [CommRing C] [Algebra k C] :
    invariants k p C →ₗ[k] twist k p C :=
  (projection k p C).comp (invariants k p C).subtype

/-- Iterated comultiplication, including the counit at arity zero, with canonical reindexing.
Source: Milne, p. 224 (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def iteratedComul (C : Type u) [CommRing C] [HopfAlgebra k C] :
    (n : ℕ) → C →ₗ[k] (⨂[k] (_ : Fin n), C)
  | 0 => (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 ↦ C)
      (Fin 0)).symm.toLinearMap.comp
      (Coalgebra.counit (R := k))
  | n + 1 =>
      (PiTensorProduct.reindex k (fun _ : Fin 1 ⊕ Fin n ↦ C)
        (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n)))).toLinearMap.comp
      ((PiTensorProduct.tmulEquiv k C).toLinearMap.comp
        ((TensorProduct.map
          (PiTensorProduct.subsingletonEquiv (R := k)
            (s := fun _ : Fin 1 ↦ C) 0).symm.toLinearMap
          (iteratedComul C n)).comp (Coalgebra.comul (R := k))))

/-- The base-changed comultiplication on a first-factor generator, computed from an actual
finite tensor presentation of the original coproduct. Source: Milne, Definition 11.39
(blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
noncomputable def twistedComulGenerator (C : Type u) [CommRing C] [HopfAlgebra k C]
    (a : C) : twist k p C ⊗[k] twist k p C :=
  ∑ i ∈ (Coalgebra.Repr.arbitrary k a).index,
    first k p C ((Coalgebra.Repr.arbitrary k a).left i) ⊗ₜ[k]
      first k p C ((Coalgebra.Repr.arbitrary k a).right i)

/-- Spectrum group operations are the specified base-changed coordinate operations, and
Frobenius and Verschiebung are their specified spectrum maps. Source: Milne, Definition 11.39
and Proposition 11.40(a) (blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
def GroupMaps
    (G : Scheme.{u}) [G.Over (Spec (CommRingCat.of k))] [IsAffine G]
    [GrpObj (G.asOver (Spec (CommRingCat.of k)))]
    (D : twist k p Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤) ⊗[k] twist k p Γ(G, ⊤))
    (E : twist k p Γ(G, ⊤) →ₐ[k] k)
    (S : twist k p Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤))
    (f : twist k p Γ(G, ⊤) →ₐ[k] Γ(G, ⊤))
    (v : Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤))
    [gt : GrpObj ((Spec (twist k p Γ(G, ⊤))).asOver (Spec (CommRingCat.of k)))] : Prop :=
  letI : MonObj ((Spec (twist k p Γ(G, ⊤))).asOver
    (Spec (CommRingCat.of k))) := gt.toMonObj
  gt.toMonObj.mul.left =
    (pullbackSpecIso (CommRingCat.of k) (twist k p Γ(G, ⊤))
      (twist k p Γ(G, ⊤))).hom ≫ Spec.map (CommRingCat.ofHom D.toRingHom) ∧
  gt.toMonObj.one.left =
    Spec.map (CommRingCat.ofHom E.toRingHom) ∧
  gt.inv.left =
    Spec.map (CommRingCat.ofHom S.toRingHom) ∧
  ∃ (F : G.asOver (Spec (CommRingCat.of k)) ⟶
      (Spec (twist k p Γ(G, ⊤))).asOver (Spec (CommRingCat.of k)))
    (V : (Spec (twist k p Γ(G, ⊤))).asOver (Spec (CommRingCat.of k)) ⟶
      G.asOver (Spec (CommRingCat.of k))),
    IsMonHom F ∧ IsMonHom V ∧
    F.left = G.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ∧
    V.left = Spec.map (CommRingCat.ofHom v.toRingHom) ≫ G.isoSpec.inv ∧
    F ≫ V = 𝟙 (G.asOver (Spec (CommRingCat.of k))) ^ p

/-- The specified base-changed Hopf operations, coordinate maps and induced group maps.
The three algebra maps are constrained on every first-factor generator; algebra linearity
fixes second-factor scalars. The spectrum group operations are explicitly identified with them.
Source: Milne, Definition 11.39 and Proposition 11.40(a), pp. 224–225
(blueprint: lem-sfb-affine-group-frobenius-verschiebung). -/
def Maps
    (G : Scheme.{u}) [G.Over (Spec (CommRingCat.of k))] [IsAffine G]
    [GrpObj (G.asOver (Spec (CommRingCat.of k)))] : Prop :=
  ∃ (D : twist k p Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤) ⊗[k] twist k p Γ(G, ⊤))
    (E : twist k p Γ(G, ⊤) →ₐ[k] k)
    (S : twist k p Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤)),
    (∀ a, D (first k p Γ(G, ⊤) a) = twistedComulGenerator k p Γ(G, ⊤) a) ∧
    (∀ a, E (first k p Γ(G, ⊤) a) = (Coalgebra.counit (R := k) a) ^ p) ∧
    (∀ a, S (first k p Γ(G, ⊤) a) =
      first k p Γ(G, ⊤) (HopfAlgebra.antipode k a)) ∧
    ∃ (f : twist k p Γ(G, ⊤) →ₐ[k] Γ(G, ⊤))
      (v : Γ(G, ⊤) →ₐ[k] twist k p Γ(G, ⊤)),
      (∀ a c, f (pure k p Γ(G, ⊤) a c) = c • a ^ p) ∧
      (∀ a, v a = projection k p Γ(G, ⊤) (iteratedComul k Γ(G, ⊤) p a)) ∧
      (Algebra.TensorProduct.map f f).comp D = (Bialgebra.comulAlgHom k Γ(G, ⊤)).comp f ∧
      (Bialgebra.counitAlgHom k Γ(G, ⊤)).comp f = E ∧
      (HopfAlgebra.antipodeAlgHom k Γ(G, ⊤)).comp f = f.comp S ∧
      D.comp v = (Algebra.TensorProduct.map v v).comp (Bialgebra.comulAlgHom k Γ(G, ⊤)) ∧
      E.comp v = Bialgebra.counitAlgHom k Γ(G, ⊤) ∧
      S.comp v = v.comp (HopfAlgebra.antipodeAlgHom k Γ(G, ⊤)) ∧
      ∃ gt : GrpObj ((Spec (twist k p Γ(G, ⊤))).asOver (Spec (CommRingCat.of k))),
        @GroupMaps k _ p _ _ G _ _ _ D E S f v gt

/-- Frobenius and the canonical Verschiebung, including its invariant-tensor construction.
Source: Milne, Definition 11.39 and Proposition 11.40(a), pp. 224–225
(blueprint: lem-sfb-affine-group-frobenius-verschiebung).

Proof plan: pull the group operations back to the coordinate Hopf algebra using
lem-sfb-affine-group-coordinate-hopf. Coassociativity and commutativity imply that iterated
comultiplication is invariant. The orbit sums of any tensor basis form a basis of invariants.
The lemma lem-sfb-symmetric-invariant-frobenius-projection identifies the restriction of the
explicit diagonal-coordinate projection with the basis-independent map lambda. Its naturality
and tensor compatibility, applied to multiplication, unit, coproduct, counit and antipode,
show that lambda composed with iterated comultiplication is a Hopf algebra homomorphism.
The formula `a ⊗ c ↦ c*a^p` gives the relative Frobenius Hopf homomorphism by the binomial
identity in characteristic p and compatibility of the coordinate Hopf maps with scalars.
Apply lem-sfb-hopf-spectrum-functor to these two coordinate homomorphisms. Multiplication of
the factors agrees with Frobenius after lambda on constant orbit tensors. Every nonconstant
orbit has size divisible by p, so its product sum is zero. The orbit basis therefore gives
`f ∘ v = multiplication ∘ iteratedComul`, which on algebra-valued points is multiplication
by p. Contravariance of Spec yields `F ≫ V = [p]`. This uses no perfection, connectedness,
reducedness, or smoothness assumption. -/
theorem frobenius_verschiebung
    (G : Scheme.{u}) [G.Over (Spec (CommRingCat.of k))] [IsAffine G]
    [GrpObj (G.asOver (Spec (CommRingCat.of k)))]
    [IsCommMonObj (G.asOver (Spec (CommRingCat.of k)))]
    [LocallyOfFiniteType (G ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (G ↘ Spec (CommRingCat.of k))] :
    (∀ (J : Type u) (B : Module.Basis J k Γ(G, ⊤)),
      ∃ OB : Module.Basis (Set.range (orbit (J := J) p)) k (invariants k p Γ(G, ⊤)),
        ∀ t, (OB ⟨orbit p t, Set.mem_range_self t⟩).val = orbitSum k p B t) ∧
    (∀ (J : Type u) (B : Module.Basis J k Γ(G, ⊤)) (t : Fin p → J),
      ((∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩) →
        projectionForBasis k p B (orbitSum k p B t) =
          first k p Γ(G, ⊤) (B (t ⟨0, (Fact.out : p.Prime).pos⟩))) ∧
      ((¬ ∀ i, t i = t ⟨0, (Fact.out : p.Prime).pos⟩) →
        projectionForBasis k p B (orbitSum k p B t) = 0)) ∧
    (∀ (J : Type u) (B : Module.Basis J k Γ(G, ⊤)),
      (projectionForBasis k p B).comp (invariants k p Γ(G, ⊤)).subtype =
        invariantProjection k p Γ(G, ⊤)) ∧
    (∀ a, iteratedComul k Γ(G, ⊤) p a ∈ invariants k p Γ(G, ⊤)) ∧
    Maps k p G := by
  sorry

end AlgebraicGeometry.AffineGroupFrobeniusVerschiebung
