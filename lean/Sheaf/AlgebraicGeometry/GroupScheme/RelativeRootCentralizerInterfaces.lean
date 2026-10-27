module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Relative character weights and centralizer comparisons

Source: Conrad, Reductive group schemes, Section 4 introduction and Lemma 4.1.3,
printed pp.107--109 (blueprint: def-sfb-relative-root-centralizer-interfaces).

The tangent module is the existing `GrpObj.Lie`, over an arbitrary ring.
Weights use characters on all algebra points, including nonreduced test rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.RelativeRootCentralizer

variable {A : Type u} [CommRing A]

/-- Scalar extension with its actual pulled-back group law. Source: Conrad, p.107
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
abbrev extend {B : Type u} [CommRing B] (f : A →+* B) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp

/-- A Laurent coordinate evaluated as a unit. Source: Conrad, p.107
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def unitValue {B : Type u} [CommRing B] [Algebra A B]
    (t : points (RingGroupSchemes.multiplicative A).X B) : Bˣ :=
  Units.map (RingHom.toMonoidHom ((Scheme.ΓSpecIso (.of B)).hom.hom.comp
    (t.left.appTop.hom.comp (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv.hom)))
      (unitOfInvertible (LaurentPolynomial.T 1))

/-- Evaluation of the Laurent monomial with exponent m on the product torus.
Source: Conrad, p.107 (blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def characterValue {B : Type u} [CommRing B] [Algebra A B] :
    (r : ℕ) → (Fin r → ℤ) → points (RingGroupSchemes.splitTorus A r).X B → Bˣ
  | 0, _, _ => 1
  | n + 1, m, t =>
      unitValue (t ≫ (fst (RingGroupSchemes.multiplicative A)
        (RingGroupSchemes.splitTorus A n)).hom.hom) ^ m 0 *
      characterValue n (fun j ↦ m j.succ)
        (t ≫ (snd (RingGroupSchemes.multiplicative A)
          (RingGroupSchemes.splitTorus A n)).hom.hom)

/-- Dual-number extension of an algebra map, on both coefficients. Source: Conrad, p.109
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def dualMap {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) : DualNumber B →ₐ[A] DualNumber C where
  __ := DualNumber.mapRingHom f.toRingHom
  commutes' a := by
    ext <;> simp [DualNumber.mapRingHom, Algebra.algebraMap_eq_smul_one]

/-- Character eigencondition on an infinitesimal point, after every algebra extension.
It tests the full character, including in positive characteristic. Source: Conrad, p.107
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def IsWeightPoint {r : ℕ}
    {G : Grp (Over (Spec (.of A)))} (i : RingGroupSchemes.splitTorus A r ⟶ G)
    (m : Fin r → ℤ) {B : Type u} [CommRing B] [Algebra A B]
    (v : Spec (.of (DualNumber B)) ⟶ G.X.left) : Prop :=
  ∃ w : points G.X (DualNumber B), w.left = v ∧
  ∀ (C : Type u) [CommRing C] [Algebra A C] (f : B →ₐ[A] C)
    (t : points (RingGroupSchemes.splitTorus A r).X C),
    points.map G.X (TrivSqZeroExt.inlAlgHom A C C) (t ≫ i.hom.hom) *
        points.map G.X (dualMap f) w *
          (points.map G.X (TrivSqZeroExt.inlAlgHom A C C) (t ≫ i.hom.hom))⁻¹ =
      points.map G.X ((DualNumber.scale (characterValue r m t : C)).restrictScalars A)
        (points.map G.X (dualMap f) w)

/-- The character submodule. The displayed eigencondition is closed under tangent addition
and scalar multiplication, so its span has exactly those vectors. Equivalently this is
the kernel of rho minus v maps to v tensor z^m. Source: Conrad, pp.107--109
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def weight {r : ℕ} {G : Grp (Over (Spec (.of A)))}
    (i : RingGroupSchemes.splitTorus A r ⟶ G) (m : Fin r → ℤ) :
    Submodule A (GrpObj.Lie G.X) :=
  Submodule.span A {v | IsWeightPoint i m (GrpObj.tangentPoint v).left}

/-- The actual tangent image of a subgroup inclusion, without assuming a field base.
Source: Conrad, p.109 (blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def lieImage {H G : Grp (Over (Spec (.of A)))} (h : H ⟶ G) :
    Submodule A (GrpObj.Lie G.X) :=
  Submodule.span A {v | ∃ w : GrpObj.Lie H.X,
    GrpObj.tangentPoint v = GrpObj.tangentPoint w ≫ h.hom.hom}

/-- Zariski local freeness of rank one, allowing the zero ring and nontrivial line bundles.
Source: Conrad, pp.107--109 (blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def IsLine (V : Type u) [AddCommGroup V] [Module A V] : Prop :=
  ∀ p : PrimeSpectrum A, ∃ a : A, a ∉ p.asIdeal ∧
    Nonempty (LocalizedModule.Away a V ≃ₗ[Localization.Away a] Localization.Away a)

/-- The universal scheme-theoretic commuting condition on B-points.
Source: Conrad, Lemma 2.2.4 and p.109
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def centralizer {K G : Grp (Over (Spec (.of A)))} (k : K ⟶ G)
    (B : Type u) [CommRing B] [Algebra A B] : Set (points G.X B) :=
  {g | ∀ (C : Type u) [CommRing C] [Algebra A C] (f : B →ₐ[A] C)
    (t : points K.X C), Commute (points.map G.X f g) (t ≫ k.hom.hom)}

/-- The weight after scalar extension, transported to the original group on dual-number
points by the pullback projection. Source: Conrad, p.109
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def weightBase {r : ℕ} {G : Grp (Over (Spec (.of A)))}
    (i : RingGroupSchemes.splitTorus A r ⟶ G)
    (B : Type u) [CommRing B] [Algebra A B] (m : Fin r → ℤ) :
    Submodule B (GrpObj.Lie ((extend (algebraMap A B)).obj G).X) :=
  Submodule.span B {v | IsWeightPoint i m
    ((GrpObj.tangentPoint v).left ≫
      pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))))}

/-- The canonical tangent comparison, characterized on pure tensors by epsilon scaling
and the pullback projection. This formula determines the map uniquely.
Source: Conrad, p.109 (blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def IsLieComparison (G : Grp (Over (Spec (.of A))))
    (B : Type u) [CommRing B] [Algebra A B]
    (e : B ⊗[A] GrpObj.Lie G.X →ₗ[B]
      GrpObj.Lie ((extend (algebraMap A B)).obj G).X) : Prop :=
  ∀ (b : B) (v : GrpObj.Lie G.X),
    (GrpObj.tangentPoint (e (b ⊗ₜ[A] v))).left ≫
        pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      Spec.map (CommRingCat.ofHom (DualNumber.scale b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (algebraMap A B))) ≫
          (GrpObj.tangentPoint v).left

/-- Coherence of the characterized comparisons for successive ring maps. The equality
is tested after the two pullback projections, which jointly identify the canonical
iterated pullback with the direct one. Source: Conrad, p.109
(blueprint: def-sfb-relative-root-centralizer-interfaces). -/
def ComparisonsCompose (G : Grp (Over (Spec (.of A)))) : Prop :=
  ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C]
    (eB : B ⊗[A] GrpObj.Lie G.X →ₗ[B]
      GrpObj.Lie ((extend (algebraMap A B)).obj G).X)
    (eC : C ⊗[A] GrpObj.Lie G.X →ₗ[C]
      GrpObj.Lie ((extend (algebraMap A C)).obj G).X)
    (eBC : C ⊗[B] GrpObj.Lie ((extend (algebraMap A B)).obj G).X →ₗ[C]
      GrpObj.Lie ((extend (algebraMap B C)).obj
        ((extend (algebraMap A B)).obj G)).X),
    IsLieComparison G B eB → IsLieComparison G C eC →
      IsLieComparison ((extend (algebraMap A B)).obj G) C eBC →
    ∀ (c : C) (b : B) (v : GrpObj.Lie G.X),
      (GrpObj.tangentPoint (eBC (c ⊗ₜ[B] eB (b ⊗ₜ[A] v)))).left ≫
          pullback.fst ((extend (algebraMap A B)).obj G).X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap B C))) ≫
          pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
        (GrpObj.tangentPoint (eC ((c * algebraMap B C b) ⊗ₜ[A] v))).left ≫
          pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A C)))

end AlgebraicGeometry.RelativeRootCentralizer
