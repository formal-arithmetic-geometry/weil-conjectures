module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The tame root germ has nonzero class modulo the normalized maximal-ideal square.

Source: Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7 and 0307.
(blueprint: lem-sbc-dvr-galois-components-root-not-square)

Proof: Tag 09EV makes A a DVR with root t as uniformizer and ramification
index n over B; for n = 1 use A = B. For each E_i, Tag 09EB gives the
Galois degree formula, so each local ramification index e and residue
degree f divide n. In positive residue characteristic p, invertibility
of n makes e prime to p and excludes a nontrivial inseparable residue
degree, which is a p-power dividing f. In characteristic zero the residue
extension is separable automatically. The local extensions are thus tame.
Apply Tag 0BRM with the index-n root extension, and then Tag 09E7:
every normalized generic tensor-product field factor has ramification
index one over A. Consequently t has valuation one in its integral
closure localized above the closed point, whereas every element of the
maximal-ideal square has valuation at least two. The actual normalization
stalk at x is this local ring: use the affine integral-closure description
of relative normalization, its compatibility with finite disjoint unions,
and Tag 0307 for localization. These are identifications over A, so the
structural germ tau corresponds to t and is outside the square. If the
coproduct is empty there is no x. Degree-one factors are unramified. This
asserts only nonmembership in the square, not cotangent spanning. -/
theorem dvr_galois_components_root_not_mem_square
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i) ∧ Module.finrank (FractionRing B) (E i) ∣ n)
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      let tau := (a.fromNormalization.stalkMap x).hom
        (StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
      let m := IsLocalRing.maximalIdeal C
      tau ∉ m * m := by sorry

end AlgebraicGeometry.Scheme
