module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.Pi

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Transport a specified root splitting through an affine chart over the base.

Source: Stacks Project, Tag 0EYG, off-divisor branch, and affine localization.
(blueprint: lem-sbc-root-split-away-transport-chart)

Proof: The isomorphism e and its compatibility he identify the two base maps.
Functoriality of pullbacks identifies Y times Spec S with Y times V. Compose
with delta and transport every coproduct summand through the inverse of e.
Naturality and hdelta show that the resulting isomorphism to d copies of Spec S
commutes with the second projection. Evaluation T at phi(g) gives an S-algebra
isomorphism S[T]/(T-phi(g)) to S, inverse to the algebra map. Take its finite
product and apply Spec, which carries finite products of rings to coproducts
of affine schemes. Since phi(g) is a unit, its image in the product is a unit,
so the displayed basic open is the whole spectrum. Compose the preceding
isomorphisms to obtain gamma. Each constituent commutes with the structure
map, yielding the asserted projection equation. For d=0 the product is the
zero ring and both the coproduct and its spectrum are empty. For d=1 this is
just the evaluation isomorphism. No descent along a root cover is asserted:
the affine chart is required to be isomorphic to that cover over the base.
-/
theorem root_split_away_transport_chart
    (R : CommRingCat.{u}) (g : R) (n : ℕ) {Y : Scheme.{u}}
    (p : Y ⟶ Spec R) (d : ℕ) (S : CommRingCat.{u}) (φ : R →+* S)
    (hunit : IsUnit (φ g)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) →
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    let N := Spec (CommRingCat.of (∀ _k : Fin d,
      AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
    let q := Spec.map (CommRingCat.ofHom
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
    let V : N.Opens := PrimeSpectrum.basicOpen
      (algebraMap S (∀ _k : Fin d,
        AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
    ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
      γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by sorry

end AlgebraicGeometry.Scheme
