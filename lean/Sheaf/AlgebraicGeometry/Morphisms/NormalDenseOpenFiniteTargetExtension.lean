module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDenseOpen

/-! # Extension from a normal dense open into a finite target

Source: Stacks Project, Morphisms of Schemes, Tags 035I
(`lemma-characterize-normalization`) and 01RH (`lemma-equality-of-morphisms`).
(blueprint: lem-trf-normal-dense-open-finite-target-extension)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An S-morphism from a dense open of a locally Noetherian normal scheme to a finite
S-scheme extends uniquely.

Source: Stacks Project, Morphisms of Schemes, Tags 035I
(`lemma-characterize-normalization`) and 01RH (`lemma-equality-of-morphisms`).
(blueprint: lem-trf-normal-dense-open-finite-target-extension)

Proof:
1. Identify U with its open image. The open immersion j is quasi-compact because each
   affine open of the locally Noetherian X is Noetherian and its open subschemes are
   quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian). This is the affine
   test for quasi-compactness in def-weil-finite-type-morphism.
2. An open immersion is a monomorphism; its self-pullback is U, so its diagonal is an
   isomorphism. Thus j is quasi-separated (def-weil-quasi-separated-morphism), without
   requiring X itself to be quasi-compact.
3. Form T = E ×_S X (def-pc-fibre-product). Its projection q to X is integral: p is
   finite, hence integral (pqf-lem-finite-integral-lft), and integral morphisms are
   stable under base change (lem-sbc-integral-morphism-base-change). The given equation
   defines a lift alpha : U → T whose projection to X is j.
4. Take the relative normalization U → N → X of j
   (lem-weil-pbc-relative-normalization). Its map nu : N → X is an isomorphism by
   lem-sbc-normalization-dense-open, since X has integrally closed domain stalks and U
   is dense. The integral factorization through T gives d : N → T, commuting with
   both maps, by lem-sbc-relative-normalization-universal-property.
5. Compose d with the inverse of nu to obtain a section s : X → T of q. Composing s
   with T → E gives b. The pullback equation and the two normalization equations give
   b ≫ p = n and j ≫ b = a.
6. Two extensions give sections s₁, s₂ of q. Their composites with nu agree after
   U → N and over X; the uniqueness clause of the same relative-normalization
   universal property makes them equal. Compose with the inverse of nu and T → E
   to get equality of the extensions. This unique existence is precisely bijectivity
   of restriction on S-morphisms. All constructions allow empty or disconnected X.
-/
theorem existsUnique_extension_of_normal_dense_open_finite_target
    {S X E U : Scheme.{u}} (n : X ⟶ S) (p : E ⟶ S) [IsFinite p]
    [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (j : U ⟶ X) [IsOpenImmersion j] (hdense : DenseRange j)
    (a : U ⟶ E) (ha : a ≫ p = j ≫ n) :
    ∃! b : X ⟶ E, b ≫ p = n ∧ j ≫ b = a := by
  sorry

end AlgebraicGeometry.Scheme
