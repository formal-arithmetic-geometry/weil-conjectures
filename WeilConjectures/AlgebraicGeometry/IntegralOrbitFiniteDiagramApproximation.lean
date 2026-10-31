/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated

/-! # Finite Noetherian diagram around an integral descent orbit

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1,
reductions 1--5 and the start of reduction 6, printed pp. 5-18--5-21.
(blueprint: lem-sfb-integral-orbit-finite-diagram-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite approximation around a point of an fpqc form with an integral model.

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1,
reductions 1--5 and the beginning of reduction 6, pp. 5-18--5-21.
(blueprint: lem-sfb-integral-orbit-finite-diagram-approximation).

The open restrictions are expressed by membership of the represented section in `F₀`.
The two Cartesian squares express the specified identifications with base changes.
Equality of the universal `F₀` sections makes the comparison canonical. The subsequent
transport equality expresses compatibility with the canonical datum on the `X` base change.
Invariance of `j` is equality of the two subfunctors on every scheme test, not just points.

Proof:
1. Lift x to P ×_S T using lem-weil-pbc-surjective-base-change and choose a quasi-affine
   neighbourhood of its orbit in Y. Descend local finite presentation by
   lem-weil-pbc-fpqc-descend-locally-finite-presentation. Apply
   lem-weil-pbc-integral-morphism-limit-of-finite and lem-sfb-fpqc-chart-limit-spreading
   to spread this chart to a finite finitely presented surjective Q over S.
2. On Spec κ(x) ×_S Q use common residue-field extensions and
   lem-weil-pbc-fibre-product-points to identify all transported points with the orbit.
   Apply lem-weil-pbc-limit-contained-in-constructible to enlarge the finite stage until
   the chart contains this whole fibre. Finite schemes over a field are Noetherian.
3. Remove from the chart the finite source image of the closed complement under target.
   Finite closedness (lem-weil-pbc-finite-closed-map-finite-fibres) makes the resulting Z
   open. Identity, inverse and cocycle make it invariant. It still contains the fibre.
   Noetherianity makes Z quasi-compact and finitely presented over Q.
4. Descend this invariant open to P₀ using the finite surjection P ×_S Q → P; its inverse
   image is precisely Z_A. Define F₀ by sections landing in P₀ after pullback to A.
   The fpqc equalizer condition gives its representations over A and Q, and
   lem-weil-pbc-open-subscheme-fpqc-descent gives the representing open Y₀ over T.
5. Use lem-weil-pbc-surjective-universally-closed-separated to descend separatedness
   from Z_A to P₀. Quasi-compactness descends by the surjective continuous map, and
   local finite presentation and separatedness make P₀ finitely presented over A.
6. Present A by affine finitely presented S-schemes and apply
   lem-sfb-fpqc-representation-limit-spreading to F₀. This gives B, a and X.
   The representations over B and Q identify Z_B with X ×_S Q by the same F₀-section
   and the B,Q coordinates. Thus the descent transports preserve X. The projection g
   is finite integral surjective by lem-weil-pbc-finite-morphism-permanence.
7. The finite orbit in Z is saturated by lem-pd-descent-orbit-saturated. Apply
   lem-sfb-finite-datum-semilocal-generalizations to obtain the invariant affine L and
   quasi-compact flat monomorphism j, with generalization-stable image. The chosen
   lift of x maps into this orbit. Lem-weil-pbc-base-change-image then gives the
   required incidence in the image of the base change j_B followed by g.
-/
theorem integralOrbitFiniteDiagramApproximation
    {S A T : Scheme.{u}} [IsAffine S] [IsAffine A] [IsNoetherian S]
    (p : A ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (_hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F)
    (P : Over A) [LocallyOfFinitePresentation P.hom]
    (rP : ((Over.map p).op ⋙ F).RepresentableBy P)
    (t : T ⟶ S) [IsIntegralHom t] [Surjective t]
    (Y : Over T) (rY : ((Over.map t).op ⋙ F).RepresentableBy Y)
    (_horbit : ∀ y : Y.left, ∃ U : Y.left.Opens,
      (∃ (H : Scheme.{u}) (_ : IsAffine H) (i : U.toScheme ⟶ H),
        IsOpenImmersion i ∧ QuasiCompact i) ∧
      rY.overDescentDatum.toHom ''
        (pullback.fst (Y.hom ≫ t) t ⁻¹' {y}) ⊆ (U : Set Y.left))
    (x : P.left) :
    ∃ (F₀ : Subfunctor F) (P₀ : P.left.Opens) (Y₀ : Y.left.Opens) (hx : x ∈ P₀),
      (∀ (H : Over A) (f : H ⟶ P),
        rP.homEquiv f ∈ F₀.obj (op ((Over.map p).obj H)) ↔
          Set.range f.left ⊆ (P₀ : Set P.left)) ∧
      (∀ (H : Over T) (f : H ⟶ Y),
        rY.homEquiv f ∈ F₀.obj (op ((Over.map t).obj H)) ↔
          Set.range f.left ⊆ (Y₀ : Set Y.left)) ∧
      ∃ (B Q : Over S) (_ : IsAffine B.left) (_ : IsAffine Q.left)
        (a : A ⟶ B.left) (ha : a ≫ B.hom = p) (tQ : T ⟶ Q.left),
        tQ ≫ Q.hom = t ∧ LocallyOfFinitePresentation B.hom ∧
        QuasiCompact B.hom ∧ QuasiSeparated B.hom ∧ IsFinite Q.hom ∧ Surjective Q.hom ∧
        ∃ (X : Over B.left) (Z : Over Q.left)
          (rX : ((Over.map B.hom).op ⋙ F₀.toFunctor).RepresentableBy X)
          (rZ : ((Over.map Q.hom).op ⋙ F₀.toFunctor).RepresentableBy Z)
          (k : P₀.toScheme ⟶ X.left)
          (hk : k ≫ X.hom = (P₀.ι ≫ P.hom) ≫ a),
          IsSeparated X.hom ∧ LocallyOfFinitePresentation X.hom ∧
          QuasiCompact X.hom ∧ QuasiSeparated X.hom ∧
          IsSeparated Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧
          QuasiCompact Z.hom ∧ QuasiSeparated Z.hom ∧
          IsPullback k (P₀.ι ≫ P.hom) X.hom a ∧
          F.map (Over.homMk k (by
            change k ≫ (X.hom ≫ B.hom) = (P₀.ι ≫ P.hom) ≫ p
            rw [← Category.assoc, hk, Category.assoc, ha]) :
            Over.mk ((P₀.ι ≫ P.hom) ≫ p) ⟶ (Over.map B.hom).obj X).op
              (rX.homEquiv (𝟙 X)).val =
            rP.homEquiv
              (Over.homMk P₀.ι rfl : Over.mk (P₀.ι ≫ P.hom) ⟶ P) ∧
          ∃ (g : pullback (Z.hom ≫ Q.hom) B.hom ⟶ X.left)
            (hg : g ≫ X.hom = pullback.snd (Z.hom ≫ Q.hom) B.hom),
            IsPullback g (pullback.fst (Z.hom ≫ Q.hom) B.hom ≫ Z.hom)
              (X.hom ≫ B.hom) Q.hom ∧
            IsFinite g ∧ IsIntegralHom g ∧ Surjective g ∧
            F₀.toFunctor.map (Over.homMk g (by
              change g ≫ (X.hom ≫ B.hom) =
                pullback.snd (Z.hom ≫ Q.hom) B.hom ≫ B.hom
              rw [← Category.assoc, hg]) :
              Over.mk (pullback.snd (Z.hom ≫ Q.hom) B.hom ≫ B.hom) ⟶
                (Over.map B.hom).obj X).op (rX.homEquiv (𝟙 X)) =
              F₀.toFunctor.map (Over.homMk (pullback.fst (Z.hom ≫ Q.hom) B.hom)
                (pullback.condition) :
                Over.mk (pullback.snd (Z.hom ≫ Q.hom) B.hom ≫ B.hom) ⟶
                  (Over.map Q.hom).obj Z).op (rZ.homEquiv (𝟙 Z)) ∧
            (∀ (H : Scheme.{u}) (w₁ w₂ : H ⟶ pullback (Z.hom ≫ Q.hom) B.hom)
              (he : w₁ ≫ g = w₂ ≫ g)
              (hq : (w₁ ≫ pullback.fst (Z.hom ≫ Q.hom) B.hom ≫ Z.hom) ≫ Q.hom =
                (w₂ ≫ pullback.fst (Z.hom ≫ Q.hom) B.hom ≫ Z.hom) ≫ Q.hom),
              (rZ.overDescentDatum.transport _ _ hq
                (Over.homMk (w₁ ≫ pullback.fst (Z.hom ≫ Q.hom) B.hom) rfl)).left =
                  w₂ ≫ pullback.fst (Z.hom ≫ Q.hom) B.hom) ∧
            ∃ (L : Scheme.{u}) (_ : IsAffine L) (j : L ⟶ Z.left),
              QuasiCompact j ∧ Flat j ∧ IsIso (pullback.diagonal j) ∧
              (∀ z z' : Z.left, z' ⤳ z → z ∈ Set.range j → z' ∈ Set.range j) ∧
              (∀ (H : Scheme.{u}) (q₁ q₂ : H ⟶ Q.left)
                (hq : q₁ ≫ Q.hom = q₂ ≫ Q.hom) (z : Over.mk q₁ ⟶ Z),
                (∃ l : H ⟶ L, l ≫ j = z.left) ↔
                  ∃ l : H ⟶ L, l ≫ j = (rZ.overDescentDatum.transport q₁ q₂ hq z).left) ∧
              k ⟨x, hx⟩ ∈ g '' Set.range
                (pullback.map (j ≫ Z.hom ≫ Q.hom) B.hom (Z.hom ≫ Q.hom) B.hom
                  j (𝟙 B.left) (𝟙 S) (by simp) (by simp)) := by
  sorry

end AlgebraicGeometry
