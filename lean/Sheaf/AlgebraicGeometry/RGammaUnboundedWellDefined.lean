module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Independence of unbounded derived global sections from a K-injective resolution

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-rgamma-unbounded-well-defined.md, node lem-kun-rgamma-unbounded-well-defined
(blueprint: lem-kun-rgamma-unbounded-well-defined).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Any comparison of two K-injective resolutions induces the canonical isomorphism on
unbounded derived global sections, and the result is independent of the comparison and,
up to these canonical isomorphisms, of the chosen representative and resolution.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/
lem-kun-rgamma-unbounded-well-defined.md, node lem-kun-rgamma-unbounded-well-defined;
Stacks Project, Tag 070I.

Clauses: (1) every `f : I ⟶ J` with `s ≫ f` homotopic to `t` gives an isomorphism
`Q(Γ f)` in `D(Λ)`; (2) any two such comparisons give the same morphism `Q(Γ f) = Q(Γ g)`;
(3) (the "consequently" clause: canonical independence of the representative, the
resolution and the comparison) for a second representative `e' : Q(C') ≅ K` with a
K-injective resolution `s' : C' ⟶ I'`, there is a comparison `f : I ⟶ I'` over `K`, i.e.
`e⁻¹ ≫ Q(s) ≫ Q(f) = e'⁻¹ ≫ Q(s')`, and any such `f` gives an isomorphism `Q(Γ f)`, the
same one for every such `f`. Identity and cocycle equations of these isomorphisms follow
from (3): `𝟙` is a comparison from a resolution to itself, and a composite of comparisons
over `K` is a comparison over `K`.

Proof:
1. Write `Q` for the localization to `D(Mod(T_ét, Λ))`. `Q(s)` and `Q(t)` are invertible
   since `s, t` are quasi-isomorphisms, so a comparison `f` over `C` (up to homotopy)
   satisfies `Q(f) = Q(s)⁻¹ Q(t)`.
2. By the K-injective Hom bijection (lem-weil-pbc-kinjective-hom-derived), lift
   `Q(t)⁻¹ Q(s)` to `g : J ⟶ I`; injectivity of the bijection for the K-injective targets
   `I` and `J` gives homotopies `g f ≃ 𝟙` and `f g ≃ 𝟙`, so `f` is a homotopy equivalence.
3. Global sections (evaluation at the terminal object `T`) are additive and act termwise, so
   they carry these homotopies to homotopies of complexes of `Λ`-modules; hence `Γ f` is a
   homotopy equivalence and `Q(Γ f)` is an isomorphism in `D(Λ)`, since the localization
   factors through the homotopy category. No exactness of sections is used.
4. Any two comparisons over `C` have the same image `Q(s)⁻¹ Q(t)`, hence are homotopic by
   injectivity of the Hom bijection with source `I` and target `J`; the evaluated homotopy
   gives `Q(Γ f) = Q(Γ g)`. For a second representative put `u = Q(s)⁻¹ e`,
   `u' = Q(s')⁻¹ e'` and `β = u u'⁻¹ : Q(I) ⟶ Q(I')`; surjectivity of the Hom bijection for
   the K-injective target `I'` gives `f` with `Q(f) = β`, which is the displayed equation.
   Two such `f` have the same image, hence are homotopic; the inverse class is obtained
   in the same way from `β⁻¹`, and injectivity gives the homotopies exhibiting `f` as a
   homotopy equivalence. Evaluating them as in step 3 gives the isomorphism `Q(Γ f)` and its
   independence of `f`.
(blueprint: lem-kun-rgamma-unbounded-well-defined).
-/
theorem rgamma_unbounded_well_defined (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u})
    (K : DerivedCategoryModule Λ T)
    (C I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (s : C ⟶ I) (t : C ⟶ J)
    (hs : CochainComplex.IsKInjectiveResolution T Λ s)
    (ht : CochainComplex.IsKInjectiveResolution T Λ t) :
    (∀ (f : I ⟶ J), Nonempty (Homotopy (s ≫ f) t) →
      IsIso (DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map f))) ∧
    (∀ (f g : I ⟶ J), Nonempty (Homotopy (s ≫ f) t) →
      Nonempty (Homotopy (s ≫ g) t) →
      DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) ∧
    (∀ (C' I' : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
      (e' : DerivedCategory.Q.obj C' ≅ K) (s' : C' ⟶ I'),
      CochainComplex.IsKInjectiveResolution T Λ s' →
      (∃ f : I ⟶ I', e.inv ≫ DerivedCategory.Q.map s ≫ DerivedCategory.Q.map f =
        e'.inv ≫ DerivedCategory.Q.map s') ∧
      ∀ (f g : I ⟶ I'),
        e.inv ≫ DerivedCategory.Q.map s ≫ DerivedCategory.Q.map f =
          e'.inv ≫ DerivedCategory.Q.map s' →
        e.inv ≫ DerivedCategory.Q.map s ≫ DerivedCategory.Q.map g =
          e'.inv ≫ DerivedCategory.Q.map s' →
        IsIso (DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ∧
        DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
        DerivedCategory.Q.map (((Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
  sorry

end AlgebraicGeometry.Etale
