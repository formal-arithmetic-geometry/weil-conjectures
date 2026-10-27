module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Finite closed intersections and their étale stalk models

Source: Stacks Project, Morphisms, Tags 01QO, 01T6, 02GO; Schemes, Tags 01I4, 01JU;
Algebra, Tag 00CT (blueprint: lem-trf-finite-intersection-etale-stalk-model).

A limiting wide pullback cone represents the finite intersection, including the
empty intersection. Affine ideals are the ideals of the given closed immersions.
The quotient equivalences below are specified on germs, so they identify the
actual structural maps, rather than merely the isomorphism classes of rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite closed intersections have the stated affine and étale-local quotient models.
Source: Stacks Project, Tags 01QO, 01T6, 02GO, 01I4, 01JU and 00CT
(blueprint: lem-trf-finite-intersection-etale-stalk-model).

Proof:
1. On an affine open, enumerate J and induct on its cardinality. The empty
   product has ideal zero. Adding a factor replaces R/L by
   (R/L) ⊗[R] (R/I_j) = R/(L + I_j), by the affine fibre-product formula
   (lem-weil-pbc-fibre-product-affine-spectra) and the tensor-quotient formula
   (lem-weil-pbc-tensor-quotient-base-change). These identifications respect
   projections. The affine characterization of closed immersions proves closedness.
2. A Noetherian affine cover of X induces quotient charts of Z. Quotients and
   finite-type algebras over Noetherian rings are Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian). Étale maps are locally of finite
   type, so W has Noetherian charts too; localizing proves its stalks Noetherian
   (lem-weil-pbc-localization-noetherian).
3. At z, localize the affine quotient R/K. The quotient-localization formula
   (lem-weil-pbc-localization-at-prime-of-quotient) identifies the stalk with A/I.
   On fractions r/s the map is r/s ↦ r̄/s̄, so I is the kernel of the actual
   stalk map, independent of the affine chart. This also identifies I with
   the image of the ideal sheaf stalk, by lem-weil-pbc-spec-tilde-stalk-localization.
4. The local map A → B takes I into the maximal ideal of B. Therefore B/IB
   is nonzero and local (lem-weil-pbc-quotient-local-structure), and Noetherian.
   Apply the affine fibre-product and tensor-quotient formulas to Spec B;
   extending K directly or through A gives the same ideal IB.
5. On an affine neighbourhood Spec C of w, the pullback is Spec(C/KC).
   There is a unique prime above the prime q of w, namely q/KC. Localization
   identifies its stalk with B/IB and its quotient map with the actual stalk
   map from W (lem-weil-pbc-spec-map-stalk-localization).
6. The projection to Z is étale by base change (lem-weil-pbc-etale-scheme-base-change),
   hence flat on stalks and local. The fraction formulas identify this stalk map
   with the quotient of A → B, giving exactly the final commuting square.
   Empty J gives I = 0 and the original étale stalk map; empty Z has no z.
-/
theorem finiteIntersection_etale_stalk_model
    {X : Scheme.{u}} [IsLocallyNoetherian X] {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (hclosed : ∀ j : Fin n, IsClosedImmersion (i j)) (J : Finset (Fin n))
    (c : WidePullbackCone (fun j : J ↦ i j.val)) (hc : IsLimit c) :
    IsClosedImmersion c.base ∧ IsLocallyNoetherian c.pt ∧
    (∀ (U : X.Opens) (hU : IsAffineOpen U),
      ∃ e : pullback c.base hU.fromSpec ≅
          Spec (.of (Γ(X, U) ⧸ (⨆ j : J, (i j.val).ker.ideal ⟨U, hU⟩))),
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) =
          pullback.snd c.base hU.fromSpec) ∧
    (∀ (z : c.pt) (U : X.Opens) (hU : IsAffineOpen U) (hx : c.base z ∈ U)
        (K : Ideal Γ(X, U)) (hK : K = ⨆ j : J, (i j.val).ker.ideal ⟨U, hU⟩)
        (I : Ideal (X.presheaf.stalk (c.base z)))
        (hI : I = K.map (X.presheaf.germ U (c.base z) hx).hom),
      I = RingHom.ker (c.base.stalkMap z).hom ∧
      ∃ eA : (X.presheaf.stalk (c.base z) ⧸ I) ≃+* c.pt.presheaf.stalk z,
        (∀ a : X.presheaf.stalk (c.base z),
          eA (Ideal.Quotient.mk I a) = (c.base.stalkMap z).hom a) ∧
        ∀ (W : Scheme.{u}) (v : W ⟶ X), Etale v →
          ∀ (w : W) (hw : v w = c.base z)
            (φ : X.presheaf.stalk (c.base z) →+* W.presheaf.stalk w)
            (hφ : φ = (v.stalkMap w).hom.comp
              (X.presheaf.stalkCongr (.of_eq hw)).inv.hom)
            (IB : Ideal (W.presheaf.stalk w)) (hIB : IB = I.map φ),
          IsNoetherianRing (W.presheaf.stalk w) ∧ IsLocalRing (W.presheaf.stalk w) ∧
          Nontrivial (W.presheaf.stalk w ⧸ IB) ∧
          IsNoetherianRing (W.presheaf.stalk w ⧸ IB) ∧
          IsLocalRing (W.presheaf.stalk w ⧸ IB) ∧
          (∃ e : pullback c.base (W.fromSpecStalk w ≫ v) ≅
              Spec (.of (W.presheaf.stalk w ⧸ IB)),
            e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IB)) =
              pullback.snd c.base (W.fromSpecStalk w ≫ v)) ∧
          ∃ (p : (pullback c.base v : Scheme.{u})) (hp : pullback.snd c.base v p = w),
            (∀ p' : (pullback c.base v : Scheme.{u}), pullback.snd c.base v p' = w → p' = p) ∧
            ∃ (hz : pullback.fst c.base v p = z)
              (eB : (W.presheaf.stalk w ⧸ IB) ≃+*
                (pullback c.base v).presheaf.stalk p),
              (∀ b : W.presheaf.stalk w,
                eB (Ideal.Quotient.mk IB b) =
                  ((pullback.snd c.base v).stalkMap p).hom
                    ((W.presheaf.stalkCongr (.of_eq hp)).inv.hom b)) ∧
              ∃ q : (X.presheaf.stalk (c.base z) ⧸ I) →+*
                  (W.presheaf.stalk w ⧸ IB),
                q.Flat ∧ IsLocalHom q ∧
                (∀ a : X.presheaf.stalk (c.base z),
                  q (Ideal.Quotient.mk I a) = Ideal.Quotient.mk IB (φ a)) ∧
                (∀ a : X.presheaf.stalk (c.base z) ⧸ I,
                  eB (q a) = ((pullback.fst c.base v).stalkMap p).hom
                    ((c.pt.presheaf.stalkCongr (.of_eq hz)).inv.hom (eA a)))) := by
  sorry

end AlgebraicGeometry
