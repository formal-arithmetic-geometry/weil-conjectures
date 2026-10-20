/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.IntegralConstructibleTriangulated
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules

public import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Paper.CompletedIntegralCoefficients
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.DerivedCompleteIntegralDetailed

/-!
# Integral constructible categories are linear over the valuation ring

Source: Weil conjectures blueprint, `def-weil-rationalization-karoubi`, its integral
linearity hypothesis (blueprint: lem-weil-integral-constructible-linear).

The section maps are specified by every finite quotient projection; their naturality
includes restriction from the terminal object, hence the map from constant global
sections. Sheaf-level scalar multiplication and linearity of the localization specify
the resulting action on derived morphisms, including morphisms created by localization.
The constructible subcategory carries precisely the inherited linear structure.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

/-- The triangulated structure proved by the recorded dependency, used by the inherited
integer shifts below. This is the second component of that named theorem.
Source: Bhatt--Scholze, Section 6.5 following Definition 6.5.1
(blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleTriangulatedStructure
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    (boundedConstructibleDerivedCompleteIntegral.{d, u} D l hl E Y).IsTriangulated :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).2

/-- The canonical constant-section action makes the ambient and integral constructible
derived categories linear, with linear integer shifts. Composition bilinearity is part
of `CategoryTheory.Linear`; the full-subcategory structure is the ambient one.
Source: blueprint `def-weil-rationalization-karoubi`, the integral-linearity hypothesis;
Stacks Tags 09MJ, 03CW, 03DA, 05RU
(blueprint: lem-weil-integral-constructible-linear).

Proof (the DAG's five steps):
1. Apply clause (2) of lem-pod-adic-limit-finite-modules to the free rank-one module M=\mathcal
O_E. Its finite-generation hypothesis holds because 1 generates M. It identifies the canonical
reduction map \mathcal O_E\to\varprojlim_n A_{E,n} with an isomorphism. This is a ring
isomorphism, since each coordinate is the quotient ring homomorphism and addition and
multiplication of compatible sequences are coordinatewise.

2. For each object U of Y_{\mathrm{proet}}, map a\in\mathcal O_E to the sequence of constant
sections (a\bmod\varpi_E^n)_U in (A_{E,n})_Y(U). These sections come from the constant-presheaf-
to-sheaf map in the definition of (A_{E,n})_Y. The reduction maps take the (n+1)st coordinate to
the nth. The sectionwise inverse-limit description therefore gives an element c_U(a) of
\widehat{\mathcal O}_{E,Y}(U). Coordinatewise ring operations make c_U a unital ring homomorphism,
and restriction along V\to U takes c_U(a) to c_V(a). At the terminal object Y this is precisely
the stated map to global sections, using the identification of Step 1. No equality between the
constant sheaf (\mathcal O_E)_Y and the completed sheaf is asserted.

3. Put \mathcal O=\widehat{\mathcal O}_{E,Y}. On morphisms f:M\to N of \mathcal O-module sheaves
set (a f)_U(x)=c_U(a)f_U(x). Each A_{E,n} is commutative; local representatives in its constant
sheaf therefore commute, and multiplication in their inverse limit is coordinatewise. Hence
\mathcal O is commutative, so (a f)_U is \mathcal O(U)-linear. Semilinearity of restriction and
c_U(a)|_V=c_V(a) show that these components commute with restriction. All module identities hold
sectionwise: (a+b)f=af+bf, a(f+g)=af+ag, (ab)f=a(bf) and 1f=f. For composable f,g, linearity of
g_U gives g_U(c_U(a)f_U(x))=c_U(a)g_U(f_U(x)), hence g\circ(af)=a(g\circ f)=(ag)\circ f. Addition
is sectionwise as well. Thus the sheaf category is \mathcal O_E-linear; its abelian structure is
supplied by the cited module-category statement in a universe large enough for the site.

4. Apply lem-weil-linear-abelian-derived-category with R=\mathcal O_E and \mathcal
A=\Mod(\widehat{\mathcal O}_{E,Y}), using the abelian category and scalar action of Step 3. The
derived category here is exactly D(Y_{\mathrm{proet}},\mathcal O_E) by the completed-coefficients
definition. Take the localization universe from the abstract-derived-category convention. The
lemma makes this category linear, its localization functor linear, and every integer shift linear.
To identify the action, multiplication by c_U(a) on each term defines a cochain endomorphism
\mu_{a,K}, since the differentials are module maps; already on complexes
\mu_{a,K}=a\,\mathrm{id}_K. Consequently Q(\mu_{a,K})=a\,\mathrm{id}_{QK}. For any derived
morphism f:QK\to QL, bilinearity now gives af=Q(\mu_{a,L})\circ f=f\circ Q(\mu_{a,K}). Thus it is
exactly the action through the constant global sections constructed above, including on morphisms
introduced by localization.

5. By def-weil-derived-complete-integral-detailed, D^b_c(Y,\mathcal O_E) is a full subcategory of
the ambient derived category. Give each of its Hom groups exactly the ambient module structure:
sums, scalar multiples and compositions still have the same source and target, so all module and
bilinearity identities are the ambient identities. By lem-weil-integral-constructible-triangulated
it is closed under every integer shift and has the induced triangulated structure. Its shift maps
on Hom groups are therefore the ambient shift maps, and [m](af)=a[m](f) is the identity proved in
Step 4. This proves the final assertion without imposing a new boundedness, finite-Tor-dimension,
or coefficient hypothesis.
-/
theorem integralConstructible_linear
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃ c : ∀ U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ,
        Padic.coefficientExtensionIntegers l E →+*
          (completedIntegralCoefficientSheaf l E Y D hl).obj.obj U,
      (∀ (U V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (f : U ⟶ V)
        (a : Padic.coefficientExtensionIntegers l E),
        (completedIntegralCoefficientSheaf l E Y D hl).obj.map f (c U a) = c V a) ∧
      (∀ (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (n : ℕ)
        (a : Padic.coefficientExtensionIntegers l E),
        ((completedIntegralCoefficientProjection l E Y D hl n).hom.app U) (c U a) =
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
            ((Functor.const (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ).obj
              (CommRingCat.of
                (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U)
            (ULift.up
              ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a))) ∧
      ∃ (_ : Linear (Padic.coefficientExtensionIntegers l E)
          (completedIntegralModuleSheaves l E Y D hl)),
        (∀ (M N : completedIntegralModuleSheaves l E Y D hl) (f : M ⟶ N)
          (a : Padic.coefficientExtensionIntegers l E)
          (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : M.val.obj U),
          (a • f).val.app U x = c U a • f.val.app U x) ∧
        ∃ (_ : Linear (Padic.coefficientExtensionIntegers l E)
            (completedIntegralDerivedCategory l E Y D hl)),
          Functor.Linear (Padic.coefficientExtensionIntegers l E)
            (DerivedCategory.Q (C := completedIntegralModuleSheaves l E Y D hl)) ∧
          (∀ m : ℤ, Functor.Linear (Padic.coefficientExtensionIntegers l E)
            (shiftFunctor (completedIntegralDerivedCategory l E Y D hl) m)) ∧
          Functor.Linear (Padic.coefficientExtensionIntegers l E)
            (boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ∧
          (∀ m : ℤ, Functor.Linear (Padic.coefficientExtensionIntegers l E)
            (shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) m)) := by
  sorry

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The coefficient action is the unique linear structure whose scalar maps are
multiplication by the actual constant sections of the completed coefficient sheaf.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: constant sections give a ring homomorphism to central endomorphisms of the
identity functor, characterized by their finite residues. Its ring laws can be
checked after all finite projections. Composition with these endomorphisms defines
scalar multiplication on every Hom group; centrality makes composition bilinear.
The same sectionwise action commutes with shifts on complexes. Localization at
quasi-isomorphisms preserves it by lem-weil-linear-abelian-derived-category.
The specified scalar maps determine the module structures and hence uniqueness. 
Complete DAG proof plan:
1. Apply clause (2) of lem-pod-adic-limit-finite-modules to the free rank-one module $M=\mathcal
O_E$. Its finite-generation hypothesis holds because $1$ generates $M$. It identifies the
canonical reduction map $\mathcal O_E\to\varprojlim_n A_{E,n}$ with an isomorphism. This is a
ring isomorphism, since each coordinate is the quotient ring homomorphism and addition and
multiplication of compatible sequences are coordinatewise.
2. For each object $U$ of $Y_{\mathrm{proet}}$, map $a\in\mathcal O_E$ to the sequence of
constant sections $(a\bmod\varpi_E^n)_U$ in $(A_{E,n})_Y(U)$. These sections come from the
constant-presheaf-to-sheaf map in the definition of $(A_{E,n})_Y$. The reduction maps take the
$(n+1)$st coordinate to the $n$th. The sectionwise inverse-limit description therefore gives an
element $c_U(a)$ of $\widehat{\mathcal O}_{E,Y}(U)$. Coordinatewise ring operations make $c_U$ a
unital ring homomorphism, and restriction along $V\to U$ takes $c_U(a)$ to $c_V(a)$. At the
terminal object $Y$ this is precisely the stated map to global sections, using the identification
of Step 1. No equality between the constant sheaf $(\mathcal O_E)_Y$ and the completed sheaf is
asserted.
3. Put $\mathcal O=\widehat{\mathcal O}_{E,Y}$. On morphisms $f:M\to N$ of $\mathcal O$-module
sheaves set $(a f)_U(x)=c_U(a)f_U(x)$. Each $A_{E,n}$ is commutative; local representatives in
its constant sheaf therefore commute, and multiplication in their inverse limit is
coordinatewise. Hence $\mathcal O$ is commutative, so $(a f)_U$ is $\mathcal O(U)$-linear.
Semilinearity of restriction and $c_U(a)|_V=c_V(a)$ show that these components commute with
restriction. All module identities hold sectionwise: $(a+b)f=af+bf$, $a(f+g)=af+ag$,
$(ab)f=a(bf)$ and $1f=f$. For composable $f,g$, linearity of $g_U$ gives
$g_U(c_U(a)f_U(x))=c_U(a)g_U(f_U(x))$, hence $g\circ(af)=a(g\circ f)=(ag)\circ f$. Addition is
sectionwise as well. Thus the sheaf category is $\mathcal O_E$-linear; its abelian structure is
supplied by the cited module-category statement in a universe large enough for the site.
4. Apply lem-weil-linear-abelian-derived-category with $R=\mathcal O_E$ and $\mathcal
A=\Mod(\widehat{\mathcal O}_{E,Y})$, using the abelian category and scalar action of Step 3. The
derived category here is exactly $D(Y_{\mathrm{proet}},\mathcal O_E)$ by the
completed-coefficients definition. Take the localization universe from the
abstract-derived-category convention. The lemma makes this category linear, its localization
functor linear, and every integer shift linear. To identify the action, multiplication by
$c_U(a)$ on each term defines a cochain endomorphism $\mu_{a,K}$, since the differentials are
module maps; already on complexes $\mu_{a,K}=a\,\mathrm{id}_K$. Consequently
$Q(\mu_{a,K})=a\,\mathrm{id}_{QK}$. For any derived morphism $f:QK\to QL$, bilinearity now gives
$af=Q(\mu_{a,L})\circ f=f\circ Q(\mu_{a,K})$. Thus it is exactly the action through the constant
global sections constructed above, including on morphisms introduced by localization.
5. By def-weil-derived-complete-integral-detailed, $D^b_c(Y,\mathcal O_E)$ is a full subcategory
of the ambient derived category. Give each of its Hom groups exactly the ambient module
structure: sums, scalar multiples and compositions still have the same source and target, so all
module and bilinearity identities are the ambient identities. By
lem-weil-integral-constructible-triangulated it is closed under every integer shift and has the
induced triangulated structure. Its shift maps on Hom groups are therefore the ambient shift
maps, and $[m](af)=a[m](f)$ is the identity proved in Step 4. This proves the final assertion
without imposing a new boundedness, finite-Tor-dimension, or coefficient hypothesis.
-/
theorem integralCoefficientLinear_existsUnique :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory (integralTowerModules l E Y)),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory (integralTowerModules l E Y))] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E)
          (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
          a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) (linearInst := s) := by
  sorry

/-- The canonical constant-section linear structure, fixed by its scalar formula.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralCoefficientLinear :
    Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E Y)) :=
  (integralCoefficientLinear_existsUnique l E Y).exists.choose

/-- Shift is linear for the canonical constant-section action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: on complexes multiplication by a constant section commutes with translation
and its signed differential. Localization extends this equality to roofs, by
lem-weil-linear-abelian-derived-category. -/
theorem integralCoefficientShift_linear (n : ℤ) :
    (shiftFunctor (DerivedCategory (integralTowerModules l E Y)) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- Linearity of the integral constructible full subcategory is inherited by fullness.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleLinear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    Linear (Padic.coefficientExtensionIntegers l E)
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  letI : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  Linear.fullSubcategory (boundedConstructibleDerivedCompleteIntegral D l hl E Y)

/-- Isomorphism closure supplies the inherited integral triangulation.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleClosedIso (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsClosedUnderIsomorphisms :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).1

/-- Triangulated closure, specialized from the recorded integral triangulation theorem.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear). -/
noncomputable instance integralConstructibleTriangulated (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsTriangulated :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).2

/-- The inherited shift of the integral full subcategory is linear.
Source: blueprint order 1460 (blueprint: lem-weil-integral-constructible-linear).
Proof: the inherited shift acts on each underlying Hom by the ambient shift.
Use integralCoefficientShift_linear and fullness; the inherited module action is
exactly the ambient constant-section action. -/
theorem integralConstructibleShift_linear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℤ) :
    (shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  sorry

end WeilConjectures
