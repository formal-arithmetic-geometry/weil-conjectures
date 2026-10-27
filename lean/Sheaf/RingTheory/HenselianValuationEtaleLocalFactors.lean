module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Prod
import Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition
import Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation
import Sheaf.RingTheory.ValuationRingNormal
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Local etale factors over a henselian valuation domain

Source: Stacks Project, algebra.tex, Tags 04GH and 04GK, with the valuation specialization
and residue-power-basis calculation used in Temkin, Proposition 2.2.1, pp. 11--12
(blueprint: lem-trf-henselian-valuation-etale-local-factors).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/--
Source: Stacks Project, algebra.tex, Tags 04GH and 04GK, with Tags 00U3, 00IC and 00DV;
more-algebra.tex, Tags 0ASJ and 053E(2); the residue-generator calculation used in Temkin,
Proposition 2.2.1, pp. 11--12
(blueprint: lem-trf-henselian-valuation-etale-local-factors).

`S` is any model of `D_n`. The existential fraction-field algebra structure is constrained
by the scalar tower, so its map is the unique extension of the given map from `R`.
The residue-field algebra structure is the canonical one induced by the local map.

Proof:
1. Etaleness gives finite presentation and hence finite type
   (lem-weil-pbc-etale-algebra-finite-presentation-localization). Apply
   lem-weil-pbc-henselian-finite-type-product-decomposition to split `D` into finite local
   factors and a residual factor having no quasi-finite prime above the maximal ideal.
   The factors are idempotent localizations, hence etale. By
   lem-weil-pbc-etale-quotient-base-change and lem-weil-pbc-etale-algebra-over-field-product,
   their closed fibres are products of finite separable fields. Every prime of such a
   product is isolated, so def-weil-pbc-ring-map-quasi-finite-at-prime excludes any prime
   of the residual factor above the maximal ideal. Thus `n` belongs to a finite local factor.
2. The closed fibre of that factor is local and nonzero, hence a single field. Its maximal
   ideal is the extended maximal ideal of `R`; localizing there changes nothing and kills
   the other factors. This identifies the canonical localization map with the projection,
   and proves that `S` is finite etale and its residue extension is finite separable.
3. Apply lem-trf-etale-localization-valuation-domain: the contraction hypothesis gives an
   injective local map `R → S` and makes `S` a valuation domain. Extend the embedding to
   the fraction fields using their universal property.
4. Etaleness gives flatness (lem-weil-pbc-etale-algebra-flat). Apply
   lem-trf-valuation-finite-type-module-presentation with `A = B = R` and `M = S`, then
   lem-sc-valuation-fp-torsionfree-free to obtain finite freeness. Reducing a basis shows
   its rank is the residue-field degree.
5. Localize this basis to `K`. The resulting finite-dimensional domain is a field:
   multiplication by a nonzero element is injective and therefore surjective. It is thus
   `Frac(S)`. Base change preserves etaleness (lem-weil-pbc-etale-ring-base-change), so
   lem-weil-pbc-etale-algebra-over-field-product makes this a finite separable extension,
   of degree equal to the rank and the residue-field degree.
6. Cayley--Hamilton (lem-weil-cayley-hamilton-free-module) applied to multiplication by
   each element of `S` gives integrality over `R`. Normality of the valuation domain `S`
   (lem-weil-pbc-valuation-ring-normal) gives the reverse integral-closure inclusion.
   Applying normality to `R` also proves that the intersection with `K` is exactly `R`.
7. Any valuation ring `W` in `L` with intersection `R` with `K` contains `S` by integrality
   and normality. Its maximal ideal contracts to the maximal ideal of `R`: otherwise a
   nonzero nonunit of `R` would have its inverse in `W ∩ K = R`. It then contracts on `S`
   to its maximal ideal. If `z ∈ W` is outside `S`, the inverse alternative puts its
   inverse in the maximal ideal of `S`, a contradiction. Hence `W = S`.
8. For a lift `y` of a residue generator, the residue powers form a basis by
   lem-weil-pbc-simple-algebraic-extension-power-basis. Nakayama
   (lem-weil-pbc-nakayama-local-generators) makes their lifts span `S`. Their square matrix
   in a free basis has unit determinant since its reduction is invertible, so these lifts
   are a basis. Therefore `S = R[y]`, and localization gives `L = K(y)`.
9. Express `y^r` in this basis to construct a monic polynomial over `R` of degree `r`.
   The localized power basis identifies its image with the minimal polynomial over `K`;
   the residue power basis identifies its reduction with the residue minimal polynomial.
   The latter is separable (def-weil-pbc-separable-algebraic-extension), so Bezout for it
   and its derivative (def-pc-separable-polynomial) makes the derivative nonzero at the
   residue generator. Differentiation and evaluation commute with reduction, so the
   derivative at `y` is outside the maximal ideal of `S`, hence a unit.
-/
theorem henselian_valuation_etale_local_factors
    (R D : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [HenselianLocalRing R] [CommRing D] [Algebra R D]
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap R D)))]
    (n : Ideal D) [n.IsPrime]
    (hn : n.comap (algebraMap R D) = IsLocalRing.maximalIdeal R)
    (S : Type v) [CommRing S] [Algebra D S] [Algebra R S]
    [IsScalarTower R D S] [IsLocalization.AtPrime S n] :
    ∃ (_ : IsDomain S) (_ : ValuationRing S) (_ : IsLocalHom (algebraMap R S))
      (_ : Algebra (FractionRing R) (FractionRing S))
      (_ : IsScalarTower R (FractionRing R) (FractionRing S)),
      (∃ (T : CommAlgCat.{u} R) (e : D ≃ₐ[R] S × T),
        ∀ d : D, (e d).1 = algebraMap D S d) ∧
      Module.Finite R S ∧ Algebra.Etale R S ∧
      Module.Finite (FractionRing R) (FractionRing S) ∧
      Algebra.IsSeparable (FractionRing R) (FractionRing S) ∧
      (integralClosure R (FractionRing S)).toSubring =
        (algebraMap S (FractionRing S)).range ∧
      ((algebraMap S (FractionRing S)).range).comap
          (algebraMap (FractionRing R) (FractionRing S)) =
        (algebraMap R (FractionRing R)).range ∧
      (∀ W : ValuationSubring (FractionRing S),
        W.toSubring.comap (algebraMap (FractionRing R) (FractionRing S)) =
          (algebraMap R (FractionRing R)).range →
        W.toSubring = (algebraMap S (FractionRing S)).range) ∧
      IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) ∧
      Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
      Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
      Module.Free R S ∧
      Module.finrank R S = Module.finrank (FractionRing R) (FractionRing S) ∧
      Module.finrank (FractionRing R) (FractionRing S) =
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
      ∀ y : S,
        IntermediateField.adjoin (IsLocalRing.ResidueField R)
          {IsLocalRing.residue S y} = ⊤ →
        Algebra.adjoin R {y} = ⊤ ∧
        IntermediateField.adjoin (FractionRing R)
          {algebraMap S (FractionRing S) y} = ⊤ ∧
        ∃ g : Polynomial R,
          g.Monic ∧
          g.map (algebraMap R (FractionRing R)) =
            minpoly (FractionRing R) (algebraMap S (FractionRing S) y) ∧
          g.natDegree =
            Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
          g.map (IsLocalRing.residue R) =
            minpoly (IsLocalRing.ResidueField R) (IsLocalRing.residue S y) ∧
          IsUnit (Polynomial.aeval y g.derivative) := by
  sorry

end AlgebraicGeometry
