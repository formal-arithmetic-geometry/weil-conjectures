module

public import Sheaf.AlgebraicGeometry.RelativeTangentWeightBaseChange
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.ContractedSmoothCurveLinearization
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Canonical relative root exponentials

Source: Conrad, Reductive group schemes, Theorem 4.1.4, printed pp.110, 116–118,
and Remark 4.2.4 (blueprint: lem-sfb-relative-canonical-root-exponential).

The source is the actual spectrum of the symmetric algebra of the dual root line.
The additive law, character action and tangent normalization are tested on all
algebra-valued points. No trivialization of the line is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RelativeRootExponential

variable {A : Type u} [CommRing A] {r : ℕ}
variable {G : Grp (Over (Spec (.of A)))}
variable {a : ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X G.X}

/-- The full coaction root module, not the differential of a character.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
abbrev Line (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ)) :=
  SplitTorus.weightSpace D.rho α

/-- The additive root line's underlying affine scheme, without a basis.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def vector (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ)) :
    Over (Spec (.of A)) :=
  (Spec (.of (SymmetricAlgebra A (Module.Dual A (Line D α))))).asOver (Spec (.of A))

/-- Evaluation of linear functions gives the canonical point of the vector scheme.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def vectorPoint (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ))
    {B : Type u} [CommRing B] [Algebra A B] (v : B ⊗[A] Line D α) :
    points (vector D α) B :=
  (Spec.map (CommRingCat.ofHom (SymmetricAlgebra.lift
    ({ toFun := fun φ ↦ (φ.baseChange B) v
       map_add' := by
         intro φ ψ
         change ((Module.Dual.baseChange B) (φ + ψ)) v = _
         rw [map_add]
         rfl
       map_smul' := by
         intro c φ
         change ((Module.Dual.baseChange B) (c • φ)) v = _
         rw [map_smul]
         rfl } : Module.Dual A (Line D α) →ₗ[A] B)).toRingHom)).asOver _

/-- The Laurent monomial character evaluated at a torus point.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def characterValue (α : ULift.{u} (Fin r → ℤ))
    {B : Type u} [CommRing B] [Algebra A B]
    (t : points (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X B) : B :=
  (Spec.preimage t.left).hom (AddMonoidAlgebra.single α 1)

/-- The point epsilon times v in the scalar-extended root line.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def infinitesimal (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ))
    {B : Type u} [CommRing B] [Algebra A B] (v : B ⊗[A] Line D α) :
    DualNumber B ⊗[A] Line D α :=
  TensorProduct.map ((TrivSqZeroExt.inrHom B B).restrictScalars A) LinearMap.id v

/-- Canonical vector points on the actual pullback over B, also for B=0.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def basePoint (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ))
    (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C] (v : C ⊗[A] Line D α) :
    points ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (vector D α)) C :=
  Over.homMk (pullback.lift (vectorPoint D α v).left
    (Spec.map (CommRingCat.ofHom (algebraMap B C))) (by
      rw [(vectorPoint D α v).w]
      change Spec.map (CommRingCat.ofHom (algebraMap A C)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq A B C])) (by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap B C))
      exact pullback.lift_snd _ _ _)

/-- The canonical projection of a point of a pullback to an A-point.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def forgetPoint (X : Over (Spec (.of A))) (B : Type u) [CommRing B] [Algebra A B]
    {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (x : points ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj X) C) : points X C :=
  Over.homMk (x.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (x.left ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj X).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) = _
    rw [Over.w]
    change Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C])

/-- Evaluation of a map between the actual B-pullbacks, using canonical vector points.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def evaluate (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ))
    (B : Type u) [CommRing B] [Algebra A B]
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (vector D α) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G.X)
    {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (v : C ⊗[A] Line D α) : points G.X C :=
  forgetPoint G.X B (basePoint D α B C v ≫ q)

/-- The required homomorphism, character equivariance and differential over any B.
These conditions quantify over all B-algebras, not just geometric points.
Source: Conrad, Theorem 4.1.4 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def IsExponentialOver (D : RelativeTangentWeights.Data r G a)
    (α : ULift.{u} (Fin r → ℤ))
    (i : ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ)) ⟶ G)
    (B : Type u) [CommRing B] [Algebra A B]
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (vector D α) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G.X) : Prop :=
  (∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C],
    evaluate D α B q (0 : C ⊗[A] Line D α) = 1 ∧
    (∀ v w : C ⊗[A] Line D α,
      evaluate D α B q (v + w) = evaluate D α B q v * evaluate D α B q w) ∧
    (∀ (t : points (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X C)
      (v : C ⊗[A] Line D α),
      evaluate D α B q (characterValue α t • v) =
        (t ≫ i.hom.hom) * evaluate D α B q v * (t ≫ i.hom.hom)⁻¹) ∧
    (∀ v : C ⊗[A] Line D α,
      evaluate D α B q (infinitesimal D α v) =
        (D.E C ((Line D α).subtype.baseChange C v)).val))

/-- The geometric closed image is the smooth connected normalized root subgroup.
The tangent-image equality uses the recorded canonical kernel comparison, so it
means precisely Lie(U)=g_alpha in the field root-subgroup characterization.
Source: Conrad, Theorem 4.1.4 and Milne, Algebraic Groups, Theorem 21.11(b),(c),
pp.428–430 (blueprint: lem-sfb-relative-canonical-root-exponential). -/
def IsGeometricRootImage (D : RelativeTangentWeights.Data r G a)
    (α : ULift.{u} (Fin r → ℤ))
    (i : ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ)) ⟶ G)
    (q : vector D α ⟶ G.X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] : Prop :=
  ∃ (U : Grp (Over (Spec (.of Ω))))
    (j : U ⟶ (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.obj G)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).obj
      (vector D α) ≅ U.X),
    e.hom ≫ j.hom.hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).map q ∧
    IsClosedImmersion j.hom.hom.left ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
    (∀ (W : Over (Spec (.of Ω)))
      (t : W ⟶ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.obj
          (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ)))).X)
      (x : W ⟶ U.X), ∃ y : W ⟶ U.X,
      (t ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.map
        i).hom.hom) * (x ≫ j.hom.hom) *
        (t ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.map
          i).hom.hom)⁻¹ = y ≫ j.hom.hom) ∧
    Set.range (fun v : GrpObj.Lie U.X ↦
      forgetPoint G.X Ω (GrpObj.tangentPoint v ≫ j.hom.hom)) =
      Set.range (fun v : Ω ⊗[A] Line D α ↦
        (D.E Ω ((Line D α).subtype.baseChange Ω v)).val)

/-- A root line has a unique equivariant exponential with its prescribed differential.
It is closed with smooth geometrically connected image, is the geometric root subgroup,
and remains the unique such map after every, including successive, base change.

Source: Conrad, Theorem 4.1.4, pp.110, 116–118, and Remark 4.2.4, p.119
(blueprint: lem-sfb-relative-canonical-root-exponential).

Proof:
1. Smoothness and affine finite type give finite presentation. The tangent and weight
   comparisons of lem-sfb-relative-tangent-weight-base-change identify the root line
   after arbitrary base change. By lem-sfb-relative-root-rank-one-centralizer, any
   equivariant map factors through the rank-one centralizer of ker(alpha_primitive).
2. Choose a cocharacter pairing positively with alpha. Apply
   lem-sfb-relative-dynamic-attracting-subgroup to the centralizer. Its attracting
   group U has tangent L and is smooth with connected fibres. The geometric
   root-subgroup theorem lem-sfb-reductive-root-subgroup-parametrizations identifies
   its fibres as the alpha root groups. Commutativity of T makes U T-stable.
3. Apply lem-sfb-contracted-smooth-curve-linearization on affine etale charts.
   Normalize each coordinate by its derivative to obtain V(L) -> U with derivative id.
4. An equivariant polynomial for a positive weight n has only its degree-one term:
   compare Laurent exponents nj and n over the arbitrary coefficient ring. Thus these
   normalized maps agree on overlaps. Applying the same calculation to universal
   torus points proves full T-equivariance, even over nonreduced rings.
5. The etale cover is fpqc (lem-weil-pbc-fpqc-finer-than-etale) and stays so on
   products (lem-galois-fpqc-covering-base-change). Glue the maps and their inverses
   by lem-weil-pbc-fpqc-representable-descent. Compose V(L) ≅ U with U -> G.
   This is closed, and its image has the asserted smoothness and geometric fibres.
6. Any competing equivariant homomorphism factors through the centralizer and then
   through U by dynamic functoriality. In the charts its derivative is the identity,
   so the degree-one calculation makes it the identity. Fpqc descent gives uniqueness
   among all competing homomorphisms, without requiring them to be immersions.
7. Pull back the charts, centralizer and dynamic group along any A -> B. The same
   calculation and descent prove uniqueness there, and hence the map is the actual
   pullback. For A -> B -> C, uniqueness gives the same map and closed image over C.
   The displayed naturality is its tensor-point formula. Over B=0 all schemes are
   empty and all asserted arrows and equalities are unique. No basis of L is chosen.
-/
theorem exists_unique [Nontrivial A] [IsNoetherianRing A]
    [IsAffine G.X.left] [Smooth G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (i : ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ)) ⟶ G)
    [IsClosedImmersion i.hom.hom.left]
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.obj G))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp.map i))
    (hconj : a.smul =
      (CartesianMonoidalCategory.fst _ _ ≫ i.hom.hom) *
        CartesianMonoidalCategory.snd _ _ *
          (CartesianMonoidalCategory.fst _ _ ≫ i.hom.hom)⁻¹)
    (D : RelativeTangentWeights.Data r G a) (α : ULift.{u} (Fin r → ℤ)) (hα : α ≠ 0)
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (Line D α) p = 1) :
    ∃ q : vector D α ⟶ G.X,
      IsExponentialOver D α i A
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A)))).map q) ∧
      (∀ q' : vector D α ⟶ G.X,
        IsExponentialOver D α i A
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A)))).map q') →
        q' = q) ∧
      IsClosedImmersion q.left ∧ Smooth (vector D α).hom ∧
      GeometricallyConnected (vector D α).hom ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
        IsGeometricRootImage D α i q Ω) ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B],
        IsExponentialOver D α i B
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map q) ∧
        ∀ qB : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
            (vector D α) ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G.X,
          IsExponentialOver D α i B qB →
            qB = (Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map q) ∧
      (∀ (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
        (f : B →ₐ[A] C) (v : B ⊗[A] Line D α),
        points.map G.X f (vectorPoint D α v ≫ q) =
          vectorPoint D α (TensorProduct.map f.toLinearMap LinearMap.id v) ≫ q) := by
  sorry

end AlgebraicGeometry.RelativeRootExponential
