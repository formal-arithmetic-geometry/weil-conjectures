/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent
import Sheaf.CategoryTheory.SiteConstantModuleUnit

/-! # The periodic resolution for an exact square-zero divisor

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples", periodic resolution;
Stacks Project, Tags 064K, 06YQ, 093J and 03CY.
(blueprint: lem-sfb-square-zero-periodic-tensor).

## Main statements

* `ModuleCat.square_zero_periodic_resolution_tensor`: the rank-one free resolution and self-Tor.
* `AlgebraicGeometry.Scheme.square_zero_periodic_tensor`: the constant-sheaf calculation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe r u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat

/-- The multiplication-by-`t` resolution and its self-tensor calculation.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks Tag 064K.
(blueprint: lem-sfb-square-zero-periodic-tensor).

Proof:
1. Put R in every nonnegative chain degree, with differential multiplication by t,
   and augment by R → R/(t). The square-zero equation makes a complex. The annihilator
   hypothesis says each kernel equals the incoming image tR. The quotient augmentation
   is surjective with kernel tR, so this is a free resolution of rank one in every degree.
2. Reindex by i = -q. This is bounded above and termwise flat, hence K-flat by
   lem-pc-module-bounded-flat-kflat, using def-pc-kflat-complex on the one-point site.
   The computation and independence in lem-pc-derived-tensor-second-factor-functor
   identify its total tensor with F[0] with the derived self-tensor.
3. Each nonpositive term after tensoring is F and multiplication by t is zero.
   There is only one summand in each total degree. Thus cohomology in degree -q is F,
   including q = 0. The chain-indexed calculation is exactly Tor_q(F,F). -/
theorem square_zero_periodic_resolution_tensor (R : Type r) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{r} R)]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)) :
    (∃ P : ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))),
      ∃ e : ∀ n : ℕ, P.complex.X n ≅ ModuleCat.of R R,
        (∀ (n : ℕ) (x : P.complex.X (n + 1)),
          (e n).hom (P.complex.d (n + 1) n x) = t * (e (n + 1)).hom x) ∧
        (∀ x : P.complex.X 0,
          P.π.f 0 x = Ideal.Quotient.mk (Ideal.span ({t} : Set R)) ((e 0).hom x))) ∧
    (∀ q : ℕ,
      Nonempty ((((Tor (ModuleCat.{r} R) q).obj
        (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ≅
            ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ∧
    (∀ q : ℕ,
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{r} R) (-(q : ℤ))).obj
        (((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) ⊗
         ((DerivedCategory.singleFunctor (ModuleCat.{r} R) 0).obj
          (ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R))))) ≅
            ModuleCat.of R (R ⧸ Ideal.span ({t} : Set R)))) := by
  sorry

end ModuleCat

namespace AlgebraicGeometry.Scheme

/-- The constant quotient F_V, as a module over the constant commutative ring sheaf R_V.
It is the unit module of the constant quotient ring sheaf restricted along the constant
quotient map. The lift only places coefficients in a universe containing the site.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 03CY and 06YU (blueprint: lem-sfb-square-zero-periodic-tensor). -/
def squareZeroQuotientModule (R : Type r) [CommRing R] (t : R) (V : Scheme.{u}) :
    SheafOfModules.{max r (u + 1)}
      ((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} R)))) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology V)
      (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).map
        ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).map
          (CommRingCat.ofHom (RingHom.ulift
            (Ideal.Quotient.mk (Ideal.span ({t} : Set R)))))))).obj
    (SheafOfModules.unit
      ((sheafCompose (ProEt.topology V)
        (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} (R ⧸ Ideal.span ({t} : Set R)))))))

/-- The constant-sheaf self-tensor has F_V in every nonpositive cohomological degree.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples";
Stacks Project, Tags 093J, 06YQ, 06YU and 03CY.
(blueprint: lem-sfb-square-zero-periodic-tensor).

Proof:
1. Apply constant module sheafification to the periodic free resolution of
   ModuleCat.square_zero_periodic_resolution_tensor. Exactness follows from
   lem-weil-pbc-finite-type-constant-exact: kernels, cokernels and therefore images
   are preserved, so the augmentation to F_V[0] is a quasi-isomorphism.
2. The unit tensor maps R_V ⊗ M ≅ M identify tensoring with R_V with the identity;
   thus R_V and zero are flat (def-pur-sheaf-tensor-product, def-pc-flat-sheaf-modules).
   The resolution is bounded above, so lem-pc-bounded-above-flat-kflat-site makes it K-flat.
3. By lem-weil-derived-tensor-resolution-independent this resolution computes
   def-weil-derived-tensor. Each nonpositive total tensor term is F_V, and its
   differential is zero since t acts by zero on R/(t). The cohomology is therefore F_V
   in every degree -q, including q = 0 (def-weil-abstract-derived-category).
4. If F is nonzero and V nonempty, choose a nonzero a in F. If its constant section
   vanished, lem-sf-constant-module-unit-locally-bijective would give a cover on which
   a equals zero. Joint surjectivity of a pro-etale cover gives a nonempty member, where
   restriction of the constant presheaf is the identity, a contradiction. Hence F_V and
   all the isomorphic displayed cohomology sheaves are nonzero. -/
theorem square_zero_periodic_tensor (R : Type r) [CommRing R]
    (t : R) (ht : t ^ 2 = 0)
    (hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R))
    (V : Scheme.{u})
    [hD : @HasDerivedCategory.{w, max r (u + 1), (max r (u + 1)) + 1}
      (SheafOfModules.{max r (u + 1)}
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R)))))
      inferInstance
      (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V))] :
    (∀ q : ℕ,
      Nonempty ((@DerivedCategory.homologyFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD (-(q : ℤ))).obj
        (@SheafOfModules.ringedSiteDerivedTensorOfUniverses.{u + 1, u, max r (u + 1), w}
          V.ProEt _ _ (ProEt.topology V)
          ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
            (CommRingCat.of (ULift.{u + 1} R)))
          (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V) hD
          ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))
          ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))) ≅
            squareZeroQuotientModule R t V)) ∧
    (Nontrivial (R ⧸ Ideal.span ({t} : Set R)) → Nonempty V →
      ¬ IsZero (squareZeroQuotientModule R t V) ∧
        ∀ q : ℕ, ¬ IsZero ((@DerivedCategory.homologyFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD (-(q : ℤ))).obj
          (@SheafOfModules.ringedSiteDerivedTensorOfUniverses.{u + 1, u, max r (u + 1), w}
          V.ProEt _ _ (ProEt.topology V)
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R)))
          (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V) hD
            ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))
            ((@DerivedCategory.singleFunctor (SheafOfModules.{max r (u + 1)}
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
                ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
                  (CommRingCat.of (ULift.{u + 1} R)))))
          inferInstance
          (@SheafOfModules.instAbelian.{max r (u + 1), u, max r (u + 1), u + 1}
        V.ProEt inferInstance (ProEt.topology V)
        ((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{max r (u + 1)} RingCat.{max r (u + 1)})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{max r (u + 1)}).obj
              (CommRingCat.of (ULift.{u + 1} R))))
        (WeilConjectures.integralCoefficientAbSheafify.{u, r} V)
        (WeilConjectures.integralCoefficientAbLocallyBijective.{u, r} V)) hD 0).obj
            (squareZeroQuotientModule R t V))))) := by
  sorry

end AlgebraicGeometry.Scheme
