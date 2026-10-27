module

public import Sheaf.AlgebraicGeometry.NeronLftModel
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Integral cosets of a split-torus extension

Source: BLR, Néron Models, 10.1 Proposition 7 proof, printed pp.292–293,
and 3.6 Definition 1, printed p.78
(blueprint: lem-sfb-torus-integral-coset-specialization).

Points of the generic fibre are represented by maps over the original base, via the
pullback universal property. Coset surjectivity is written as a representative factorization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- The canonical restriction of points along a morphism of algebras. Its underlying
scheme map is Spec of that algebra morphism.
Source: BLR 10.1 Proposition 7, integral coset restriction
(blueprint: lem-sfb-torus-integral-coset-specialization). -/
noncomputable def integralCosetRestriction (D C E : Type u)
    [CommRing D] [CommRing C] [CommRing E] [Algebra D C] [Algebra D E]
    (f : C →ₐ[D] E) :
    (algSpec (.of D)).obj (op (CommAlgCat.of D E)) ⟶
      (algSpec (.of D)).obj (op (CommAlgCat.of D C)) :=
  (algSpec (.of D)).map (CommAlgCat.ofHom f).op

/-- Representative formulation of surjectivity on integral cosets: every L-point is
an F-point times an A-point, using only the canonical restrictions. The points are
maps to B over Spec D, equivalently points of its relevant base changes.
Source: BLR 10.1 Proposition 7, printed pp.292–293
(blueprint: lem-sfb-torus-integral-coset-specialization). -/
def IntegralCosetSurjective (D F A L : Type u)
    [CommRing D] [Field F] [CommRing A] [Field L]
    [Algebra D F] [Algebra D A] [Algebra D L] [Algebra A L] [IsScalarTower D A L]
    (B : Grp (Over (Spec (.of D)))) (f : F →ₐ[D] L) : Prop :=
  ∀ a' : (algSpec (.of D)).obj (op (CommAlgCat.of D L)) ⟶ B.X,
    ∃ (a : (algSpec (.of D)).obj (op (CommAlgCat.of D F)) ⟶ B.X)
      (b : (algSpec (.of D)).obj (op (CommAlgCat.of D A)) ⟶ B.X),
      a' = (integralCosetRestriction D F L f ≫ a) *
        (integralCosetRestriction D A L (IsScalarTower.toAlgHom D A L) ≫ b)

/-- Valuative saturation and ramification-one surjectivity of the integral cosets.
Source: BLR 10.1 Proposition 7 proof, printed pp.292–293, and 3.6 Definition 1
(blueprint: lem-sfb-torus-integral-coset-specialization).

Proof plan:
1. The local split-torus extension points lemma lifts Q(C) to B(C) for each local C;
the kernel is T(C). Generic restriction is injective for separated schemes over domains
by lem-sfb-relative-separated-dominant-ext, so these are integral subgroups.
2. For (a), extend q(a) to M(D) by the Néron property. Its extension over V agrees with
the image of b_V by separatedness. Its closed point therefore lies in Q, and its generic
point does too. Factor through Q and lift to b_D by the local split-torus points lemma.
3. The difference a/b_D lies in T(F) and becomes a V-unit in every coordinate. Write
each coordinate u*pi^n by lem-weil-pbc-dvr-unit-times-uniformizer-power. Locality makes
pi a nonunit in V, so n=0. Thus a extends to B(D), including the empty tuple at rank zero.
4. For (b), lem-sfb-neron-strict-local-descent-base-change makes M_A Néron. Extend
q(a') to M(A), and use lem-sfb-strict-local-group-component-translates to write it
m_A*u_A with m in M(D), u_A in Q(A). Lift m_F to G(F) and u_A to B(A).
5. The remaining torus point has coordinates v_i*pi^n_i with v_i in A-units, since
pi is also an A-uniformizer. Absorb pi^n_i into the F-point and v_i into the A-point.
Commutativity yields the displayed representative factorization, hence coset surjectivity.
6. For a DVR local ring of a smooth D-scheme, lem-sfb-essentially-smooth-dvr-index-one
gives the common uniformizer and geometrically reduced residue extension. Apply (b).
No perfection, excellence or completeness is used. -/
theorem torus_integral_coset_specialization
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsStrictlyHenselianLocalRing D]
    (F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]
    (M Q B : Grp (Over (Spec (.of D))))
    [IsCommMonObj M.X] [IsCommMonObj Q.X] [IsCommMonObj B.X]
    [Smooth M.X.hom] [IsSeparated M.X.hom]
    (hM : IsNeronLftModel M
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).mapGrp.obj M)
      (Iso.refl _))
    (hH : GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).obj M.X).hom)
    (hHft : QuasiCompact
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).obj M.X).hom)
    (j : Q ⟶ M) [IsOpenImmersion j.hom.hom.left]
    [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    (hQ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of D)),
      Set.range (((Over.pullback s).map j.hom.hom).left) =
        connectedComponent ((η[((Over.pullback s).mapGrp.obj M).X]).left
          (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of Ω))))
    (hQF : IsIso ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D F)))).map j.hom.hom))
    [Smooth B.X.hom] [IsSeparated B.X.hom]
    [LocallyOfFiniteType B.X.hom] [QuasiCompact B.X.hom]
    [GeometricallyConnected B.X.hom]
    (r : ℕ) (i : RingGroupSchemes.splitTorus D r ⟶ B) (q : B ⟶ Q)
    (hker : IsPullback i.hom.hom (toUnit (RingGroupSchemes.splitTorus D r).X)
      q.hom.hom η[Q.X])
    (hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of D)))
      (yoneda.map q.hom.hom)) :
    (∀ (L : Type u) [Field L] [Algebra D L] (V : ValuationSubring L)
      [Algebra D V] [IsScalarTower D V L] [IsLocalHom (algebraMap D V)],
      Function.Injective (algebraMap D V) →
      ∀ (f : F →ₐ[D] L)
        (a : (algSpec (.of D)).obj (op (CommAlgCat.of D F)) ⟶ B.X),
        (∃ b : (algSpec (.of D)).obj (op (CommAlgCat.of D V)) ⟶ B.X,
          integralCosetRestriction D F L f ≫ a =
            integralCosetRestriction D V L (IsScalarTower.toAlgHom D V L) ≫ b) →
        ∃ b : 𝟙_ (Over (Spec (.of D))) ⟶ B.X,
          a = toUnit ((algSpec (.of D)).obj (op (CommAlgCat.of D F))) ≫ b) ∧
    (∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra D A] [IsLocalHom (algebraMap D A)],
      Function.Injective (algebraMap D A) →
      (∃ π : D, IsLocalRing.maximalIdeal D = Ideal.span {π} ∧
        IsLocalRing.maximalIdeal A = Ideal.span {algebraMap D A π}) →
      Algebra.IsGeometricallyReduced (IsLocalRing.ResidueField D) (IsLocalRing.ResidueField A) →
      ∀ (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
        [Algebra D L] [IsScalarTower D A L] (f : F →ₐ[D] L),
        IntegralCosetSurjective D F A L B f) ∧
    (∀ (X : Over (Spec (.of D))) [Smooth X.hom] (x : X.left)
      (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra D A] [IsLocalHom (algebraMap D A)]
      (e : A ≃+* X.left.presheaf.stalk x),
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.left.fromSpecStalk x ≫ X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap D A)) →
      Function.Injective (algebraMap D A) →
      ∀ (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
        [Algebra D L] [IsScalarTower D A L] (f : F →ₐ[D] L),
        IntegralCosetSurjective D F A L B f) := by
  sorry

end AlgebraicGeometry
