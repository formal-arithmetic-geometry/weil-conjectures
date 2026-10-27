module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.TraceFormula.LocalDimensionFormula

/-!
# A finite normal cover is the normalization in its function field

Source: Stacks Project, Morphisms, Tag 035I; Properties, Tag 0358;
Algebra, Tags 00GK, 030B and 0307.
(blueprint: lem-sfb-finite-normal-cover-normalization)

The field algebra is constrained by its generic-point morphism, so it is the induced
extension. The affine equality is an equality of subsets of the actual source function
field. The same global isomorphism realizes each affine equality on sections, which
expresses compatibility on principal opens and arbitrary overlaps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A finite surjective normal integral cover is the normalization in its function field,
with its affine integral-closure description and uniqueness even among all morphisms.
The equation `hL` specifies the induced field extension, rather than an arbitrary embedding.
The last equality says that the affine isomorphisms are the identity inside `k(Z)`:
pullback of a normalization section has its original generic value. These are the section
maps of one global isomorphism, so they agree under restriction, including on overlaps.

Source: Stacks Project, Morphisms, Tag 035I (lemma-characterize-normalization),
Properties, Tag 0358 (lemma-normal-integral-sections), and Algebra, Tag 00GK.
(blueprint: lem-sfb-finite-normal-cover-normalization)

Proof:
1. On a nonempty affine V = Spec A, finiteness makes its inverse image Spec B, finite
as an A-module, and surjectivity makes this inverse image nonempty. The fraction-field
lemma lem-sc-integral-function-field-affine-fraction identifies the germs of A and B in
k(X) and k(Z). Dominance gives the generic stalk map of
 def-sfb-dominant-function-field-map. Its injectivity implies injectivity of A to B.
2. By lem-weil-pbc-affine-open-stalk-localization the localizations of B at maximal
ideals are local rings of Z. Transfer normal-domain structure using
lem-weil-pbc-normal-domain-ring-equivalence; then
lem-weil-pbc-normal-domain-of-local-normal makes B integrally closed in k(Z) = Frac B.
3. By lem-weil-pbc-finite-algebra-is-integral, every element of B is integral over A,
so its germ belongs to the integral closure C of A in k(Z).
4. Conversely the same monic equation over A is one over B, so every element of C
lies in B by step 2. Thus B = C inside k(Z). The affine description in
 def-fin-normalization-extension and contravariance of Spec give the affine isomorphism,
whose generic map is the identity since k(Z) = Frac B.
5. For a nonzero a in A, the preimage of D(a) is D(f sharp a). By
lem-weil-pbc-spec-module-tilde-sections, restriction is localization; by
lem-weil-pbc-integral-closure-commutes-localization, C localizes to the integral closure
of A localized at a. Thus B = C localizes to the same identity. For a = 0 the opens
are empty and the compatibility is automatic.
6. Cover arbitrary overlaps by affine opens W. Restriction of either identification
has the same germ in k(Z), hence is the identity B_W = C_W by injectivity of germs.
Use lem-weil-pbc-scheme-morphism-gluing to glue the affine maps and their inverses.
Their composites are identities on each affine chart, hence globally. This gives e,
over X and with the asserted generic identity; its section maps realize B = C.
7. Any other morphism u over X with this generic identity has on each affine chart
the same map C to B: both send c to the unique section with germ c. Injectivity of
germs and uniqueness in morphism gluing give u = e.hom. No normality of X or etaleness
of f enters the argument. -/
theorem finite_normal_cover_normalization
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : Z ⟶ X) [IsFinite f] [Surjective f]
    [Algebra X.functionField Z.functionField]
    (hL : X.fromSpecOfAlgebraFunctionField Z.functionField = Z.fromSpecFunctionField ≫ f)
    [FiniteDimensional X.functionField Z.functionField] :
    ∃ e : Z ≅ X.normalizationIn Z.functionField,
      e.hom ≫ X.fromNormalizationIn Z.functionField = f ∧
      Z.fromSpecFunctionField ≫ e.hom =
        (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization ∧
      (∀ v : Z ⟶ X.normalizationIn Z.functionField,
        v ≫ X.fromNormalizationIn Z.functionField = f →
        Z.fromSpecFunctionField ≫ v =
          (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization → v = e.hom) ∧
      ∀ (V : X.Opens), IsAffineOpen V → ∀ (_ : Nonempty V),
        ∃ (_ : Nonempty (f ⁻¹ᵁ V))
          (hpre : f ⁻¹ᵁ V ≤ e.hom ⁻¹ᵁ (X.fromNormalizationIn Z.functionField ⁻¹ᵁ V))
          (hgen : ⊤ ≤ (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization ⁻¹ᵁ
            (X.fromNormalizationIn Z.functionField ⁻¹ᵁ V)),
          IsAffineOpen (f ⁻¹ᵁ V) ∧ Function.Injective (f.app V) ∧
          Function.Injective (Z.germToFunctionField (f ⁻¹ᵁ V)) ∧
          IsFractionRing Γ(Z, f ⁻¹ᵁ V) Z.functionField ∧
          Set.range (Z.germToFunctionField (f ⁻¹ᵁ V)) =
            (@integralClosure Γ(X, V) Z.functionField _ _
              ((Z.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (f.app V).hom).toAlgebra :
                Set Z.functionField) ∧
          e.hom.appLE (X.fromNormalizationIn Z.functionField ⁻¹ᵁ V) (f ⁻¹ᵁ V) hpre ≫
              Z.germToFunctionField (f ⁻¹ᵁ V) =
            (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization.appLE
                (X.fromNormalizationIn Z.functionField ⁻¹ᵁ V) ⊤ hgen ≫
              (Scheme.ΓSpecIso (.of Z.functionField)).hom := by
  sorry

end AlgebraicGeometry
