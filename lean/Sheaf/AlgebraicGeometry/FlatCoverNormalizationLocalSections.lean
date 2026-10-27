module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Localization.Integral
import Sheaf.FieldTheory.CommonNormalCompatibleGroups
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Local sections of flat covers after normalization of a semi-trait

Source: Stacks Project, Tags 05GU, 02LR, 09DT and 09EU; the quasi-section and
conjugate-chart construction of Anantharaman, Lemma 4.2.1, second paragraph, p. 56.
(blueprint: lem-sfb-flat-cover-normalization-local-sections)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A flat surjective affine morphism of finite presentation over a semilocal normal
Noetherian domain of dimension one has local sections after normalization in a finite
extension of its fraction field. The normalization need not be module-finite, and the
extension need not be separable. An open's map to `T` over `Spec R` is equivalently a
section over that open of the base change, by the fibre-product universal property.

Source: Stacks Project, Tags 05GU, 02LR, 09DT and 09EU; Anantharaman, Lemma 4.2.1,
second paragraph, printed p. 56.
(blueprint: lem-sfb-flat-cover-normalization-local-sections)

Proof:
1. Write T = Spec B. Finite presentation on the affine pair gives B finite type over
   R, and the affine flatness criterion gives flatness. For each maximal ideal m of R,
   choose a closed point x_m of the nonempty fibre. The generic point of Spec R is
   open: the product of a chosen nonzero element in each maximal ideal vanishes at
   every nongeneric prime and is nonzero in the domain.
2. Flat going down gives a generic-fibre point specializing to x_m. Tag 05GU
   (lem-sfb-quasi-section-nearby-open) gives an integral closed quasi-section through
   x_m, dominating the base and quasi-finite at x_m.
3. Openness of the quasi-finite locus (lem-sc-quasi-finite-points-open) gives a
   principal affine neighbourhood W_m = Spec D_m inside that locus. Its generic
   fibre is a nonzero finite-dimensional domain over K = Frac R, hence a field E_m
   finite over K, and is also Frac D_m.
4. Apply Zariski's main theorem, Tag 02LR (pqf-lem-normalization-open), to W_m over
   Spec R. It is open in the spectrum of the integral closure C_m of R in D_m.
   Let A_m be the integral closure of R in E_m. Lying over for C_m into A_m gives a
   point above x_m; the inverse image V_m of W_m contains that point and maps to T.
5. The simultaneous normal envelope (lem-sfb-common-normal-compatible-groups),
   with trivial auxiliary groups, embeds all E_m in a finite normal extension L/K.
   Put A = integralClosure R L. Lying over lifts the selected point of each A_m to
   A, and pulling back V_m gives an open O_m of Spec A mapping to T over Spec R.
6. Each R_m is a DVR (lem-sc-dedekind-localization-dvr). Its integral closure in L
   is the localization of A away from m: one direction follows by localizing monic
   equations; conversely, clear their coefficient denominators with s outside m,
   so that sz is integral over R. Primes of A over m correspond to maximal ideals
   of this localized integral closure, by integral prime/maximal correspondence.
7. Apply lem-sfb-normal-coefficient-branch-conjugacy to the identity DVR map R_m
   to itself and the normal extension L/K. It makes Aut_K(L) transitive on these
   primes, including inseparable extensions. Each automorphism preserves A because
   it fixes coefficients of monic equations over R. Thus its inverse translates of
   O_m cover the fibre above m and carry the translated maps to T.
8. There are finitely many m and finitely many K-automorphisms of L. The resulting
   finite family covers every maximal ideal of A. Every prime lies in a maximal
   ideal, and an open containing that maximal ideal contains its generalizations.
   Hence the family covers Spec A. Enumerate it by Fin n and retain its maps to T.
   Pairing each map with its open inclusion gives the equivalent local section of
   T times over Spec R with Spec A; the converse is projection to T. -/
theorem exists_flat_cover_normalization_local_sections
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 1) (hmax : Set.Finite {m : Ideal R | m.IsMaximal})
    (T : Scheme.{u}) [IsAffine T] (f : T ⟶ Spec (CommRingCat.of R))
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing R) L)
      (_ : Algebra R L) (_ : IsScalarTower R (FractionRing R) L)
      (_ : Module.Finite (FractionRing R) L)
      (n : ℕ) (U : Fin n → (Spec (CommRingCat.of (integralClosure R L))).Opens),
      (⨆ j, U j) = ⊤ ∧
      ∃ u : ∀ j, (U j).toScheme ⟶ T,
        ∀ j, u j ≫ f = (U j).ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) := by
  sorry

end AlgebraicGeometry
