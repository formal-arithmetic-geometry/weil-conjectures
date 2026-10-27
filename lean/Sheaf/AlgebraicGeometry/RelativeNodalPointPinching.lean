/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Set.Card
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.AdicCompletion.Exactness
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Finite smooth-point pinching relative to a reference scheme

Source: Stacks Project, more-morphisms.tex, Tags 0E25--0E27; varieties.tex, Tag 09NN;
curves.tex, Tags 0E36 and 0C1J; morphisms.tex, Tag 03GN.
(blueprint: lem-trf-relative-nodal-point-pinching).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pinching finite sets of smooth rational points, with fibres of size one or two, on a
semistable unmarked curve proper over a reference scheme. Neither the curve nor the reference
scheme has to be separated over the ground field. Finite coproduct cofans specify the given
finite disjoint unions of copies of `Spec k`, including the empty coproduct.

The ring pullback in the double-fibre clause is `k[[u]] ×_k k[[v]]`, taken along the two
constant-coefficient maps. The branch equivalences and their residue-field equations express
that these maps are evaluation at zero. Compatibility on germs pins its two projections to
the original map of schemes; the equality proof `h` merely transports the target stalk.
The last clause expresses the reduced image by a closed immersion from the reduced source.

Source: Stacks Project, more-morphisms.tex, Tags 0E25--0E27; varieties.tex, Tag 09NN;
curves.tex, Tags 0E36 and 0C1J; morphisms.tex, Tag 03GN.
(blueprint: lem-trf-relative-nodal-point-pinching).

Proof plan, following the eleven steps of the DAG:
1. Over an affine open V of S, properness makes X_V separated over V, hence over k.
   Finite presentation of the curve makes X Noetherian. Its local rings at the finitely
   many smooth pinching points have dimension one. Apply
   lem-trf-codimension-one-points-affine-neighbourhood (Stacks 09NN) on X_V. No absolute
   separatedness of X or S is used.
2. The map E to F is finite, hence integral. Apply lem-sfb-ferrand-scheme-pushout to
   obtain the scheme pushout, its cartesian square, closed immersion of F and complement
   isomorphism. Surjectivity of E to F gives surjectivity of X to Y. The universal property
   supplies the compatible maps to S and Spec k.
3. On every affine open of Y its section ring is P = A ×_C B, with B and C finite products
   of k and B to C injective. The quotient A/P is C/B, finite dimensional over k. Lifts
   of a k-basis, together with 1, generate A over P. Thus X to Y is finite. The cartesian
   square identifies the scheme-theoretic inverse image of F with E.
4. The finite-type clause of lem-sfb-ferrand-scheme-pushout makes Y locally of finite
   type over k. Its quotient topology gives quasi-compactness. The nodes
   lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-finite-type-noetherian-finite-presentation give finite presentation of Y/k.
5. The affine-source separatedness node makes F to S separated. Relative separatedness
   in the Ferrand theorem makes Y to S separated. Finite-type cancellation gives local
   finite type, and lem-weil-pbc-image-universally-closed applied to X to Y to S gives
   universal closedness. Therefore Y to S is proper.
6. Remove the other points of F at a singleton fibre. The restricted pushout identifies
   Spec k with itself and is the corresponding open of X, giving the neighbourhood iso.
7. At f complete the exact finite-module sequence 0 to P to A plus k to k^r to 0.
   Use lem-weil-pbc-completion-exact-finite-modules and
   lem-weil-pbc-completion-finite-extension to identify the completion with the fibre
   product of the completed branch stalks along their residue maps, as in Stacks 0E36.
8. The smooth-over-field regularity node, completion-regular-local, completion-dimension
   and adic-completion-mod-power nodes make each branch completion a complete regular
   local k-algebra of dimension one with residue field k. Apply
   lem-trf-regular-complete-coefficient-coordinates with d = 1 to identify it with k[[t]],
   preserving k and identifying the residue map with constant coefficient.
9. Send a bivariate series h to (h(u,0), h(0,v)). Every pair with equal constants is
   the image of p(u) + q(v) - p(0). The kernel consists exactly of multiples of uv.
   This gives the displayed nodal ring equivalence in every characteristic.
10. The complement and singleton isomorphisms and the double-fibre calculation account
    for every point. The algebraic closure of an algebraically closed k is k up to
    k-isomorphism, so this verifies geometric semistability. The quotient topology
    preserves generic points of components and their dimension one. Flatness over k
    is automatic, finite presentation was proved in step 4, and the marking is empty.
11. On every affine open, write the reduced subcurve as Spec(A/I). If a fibre meets it,
    choose the scalar given by its unique point; otherwise choose zero. Interpolate
    the residues at the remaining points by elements of I using A onto C. Thus
    P to A/I is onto, proving the restricted map is a closed immersion. Its source is
    reduced, so its image has the reduced scheme structure. For E = F empty the
    pushout is X; for D empty the quotient ring A/I is the zero ring.
-/
theorem exists_relative_nodal_point_pinching
    (k : Type u) [Field k] [IsAlgClosed k]
    (S : Over (Spec (.of k))) (P : MultipointedCurve (Spec (.of k)))
    [IsEmpty P.D] (hP : P.IsSemistable)
    (s : Over.mk P.x ⟶ S) [IsProper s.left]
    (E F : Over (Spec (.of k))) (m n : ℕ)
    (ε : Fin m → (Over.mk (𝟙 (Spec (.of k))) ⟶ E))
    (φ : Fin n → (Over.mk (𝟙 (Spec (.of k))) ⟶ F))
    (hE : Nonempty (IsColimit (Cofan.mk E.left (fun l ↦ (ε l).left))))
    (hF : Nonempty (IsColimit (Cofan.mk F.left (fun l ↦ (φ l).left))))
    (i : E ⟶ Over.mk P.x) [IsClosedImmersion i.left]
    (hi : ∀ e : E.left, i.left e ∈ P.x.smoothLocus)
    (a : E ⟶ F) [Surjective a.left]
    (ha : ∀ f : F.left, (a.left ⁻¹' {f}).encard = 1 ∨ (a.left ⁻¹' {f}).encard = 2)
    (b : F ⟶ S) (hs : i ≫ s = a ≫ b) :
    ∃ (Q : MultipointedCurve (Spec (.of k))) (v : Over.mk P.x ⟶ Over.mk Q.x)
      (j : F ⟶ Over.mk Q.x) (t : Over.mk Q.x ⟶ S),
      IsEmpty Q.D ∧ Q.IsSemistable ∧ IsProper t.left ∧ v ≫ t = s ∧ j ≫ t = b ∧
      IsPushout i.left a.left v.left j.left ∧
      IsFinite v.left ∧ Surjective v.left ∧ IsClosedImmersion j.left ∧
      IsPullback i.left a.left v.left j.left ∧
      (∃ (U : P.X.Opens) (V : Q.X.Opens) (e : U.toScheme ≅ V.toScheme),
        (U : Set P.X) = (Set.range i.left)ᶜ ∧
        (V : Set Q.X) = (Set.range j.left)ᶜ ∧
        e.hom ≫ V.ι = U.ι ≫ v.left) ∧
      (∀ (f : F.left) (z : E.left), (∀ z' : E.left, a.left z' = f ↔ z' = z) →
        ∃ (U : P.X.Opens) (V : Q.X.Opens) (e : U.toScheme ≅ V.toScheme),
          i.left z ∈ U ∧ j.left f ∈ V ∧ e.hom ≫ V.ι = U.ι ≫ v.left) ∧
      (∀ (f : F.left) (z : Fin 2 → E.left), Function.Injective z →
        (∀ z' : E.left, a.left z' = f ↔ z' ∈ Set.range z) →
        ∃ (α : ∀ l : Fin 2,
          AdicCompletion (IsLocalRing.maximalIdeal (P.X.presheaf.stalk (i.left (z l))))
            (P.X.presheaf.stalk (i.left (z l))) ≃+* PowerSeries k)
          (ρ : ∀ l : Fin 2,
            (P.X.presheaf.stalk (i.left (z l)) ⧸
              IsLocalRing.maximalIdeal (P.X.presheaf.stalk (i.left (z l)))) ≃+* k)
          (γ : AdicCompletion (IsLocalRing.maximalIdeal (Q.X.presheaf.stalk (j.left f)))
            (Q.X.presheaf.stalk (j.left f)) ≃+*
            ↥(pullback (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
              (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))))
          (δ : ↥(pullback (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
            (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) ≃+*
              Orgogozo.nodeRing k),
          (∀ (l : Fin 2) (c : k),
            α l (algebraMap (P.X.presheaf.stalk (i.left (z l))) _
              (Orgogozo.localScalar P.x (i.left (z l)) c)) = PowerSeries.C c) ∧
          (∀ (l : Fin 2) (x : AdicCompletion
            (IsLocalRing.maximalIdeal (P.X.presheaf.stalk (i.left (z l))))
            (P.X.presheaf.stalk (i.left (z l)))),
            PowerSeries.constantCoeff (α l x) =
              ρ l (AdicCompletion.evalOneₐ
                (IsLocalRing.maximalIdeal (P.X.presheaf.stalk (i.left (z l)))) x)) ∧
          (∀ (l : Fin 2) (h : v.left (i.left (z l)) = j.left f)
            (r : Q.X.presheaf.stalk (j.left f)),
            (if l = 0 then pullback.fst
              (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
              (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
            else pullback.snd
              (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
              (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))))
              (γ (algebraMap (Q.X.presheaf.stalk (j.left f)) _ r)) =
                α l (algebraMap (P.X.presheaf.stalk (i.left (z l))) _
                  ((v.left.stalkMap (i.left (z l)))
                    ((Q.X.presheaf.stalkCongr (.of_eq h)).inv r)))) ∧
          (∀ (c : k),
            δ (γ (algebraMap (Q.X.presheaf.stalk (j.left f)) _
              (Orgogozo.localScalar Q.x (j.left f) c))) =
                Ideal.Quotient.mk _ (MvPowerSeries.C c))) ∧
      (∀ (D : Scheme.{u}) (d : D ⟶ P.X), IsReduced D → IsClosedImmersion d →
        (∃ C : Set (Set P.X), C ⊆ irreducibleComponents P.X ∧ Set.range d = ⋃₀ C) →
        (∀ f : F.left, ({z : E.left | a.left z = f ∧ i.left z ∈ Set.range d}).encard ≤ 1) →
        IsClosedImmersion (d ≫ v.left)) := by
  sorry

end AlgebraicGeometry
