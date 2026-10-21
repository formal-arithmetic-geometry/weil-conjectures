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

private lemma homotopy_of_derived_eq
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {I J : CochainComplex A ℤ} [J.IsKInjective] (f g : I ⟶ J)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj I) J).injective
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app J)]
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

private lemma exists_comparison
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (I J : CochainComplex A ℤ) [J.IsKInjective]
    (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ g : I ⟶ J, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj I) J).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app I ≫ f ≫
        (DerivedCategory.quotientCompQhIso A).inv.app J)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app I),
    ← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

private lemma map_comparison_isIso
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {I J : CochainComplex A ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J)
    [IsIso (DerivedCategory.Q.map f)] :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  have hf : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso A f).mp inferInstance
  obtain ⟨h, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp hf
  have := (F.mapHomotopyEquiv h).quasiIso_hom
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).mpr this

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
  let := hs.1
  let := hs.2
  let := ht.1
  let := ht.2
  let F := Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have comparison_eq (f : I ⟶ J) (hf : Nonempty (Homotopy (s ≫ f) t)) :
      DerivedCategory.Q.map s ≫ DerivedCategory.Q.map f = DerivedCategory.Q.map t := by
    rw [← Functor.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy _ hf.some
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have : IsIso (DerivedCategory.Q.map s ≫ DerivedCategory.Q.map f) := by
      rw [comparison_eq f hf]
      infer_instance
    have : IsIso (DerivedCategory.Q.map f) :=
      IsIso.of_isIso_comp_left (DerivedCategory.Q.map s) (DerivedCategory.Q.map f)
    exact map_comparison_isIso F f
  · intro f g hf hg
    have hfg : DerivedCategory.Q.map f = DerivedCategory.Q.map g := by
      rw [← cancel_epi (DerivedCategory.Q.map s), comparison_eq f hf, comparison_eq g hg]
    exact DerivedCategory.Q_map_eq_of_homotopy _
      (F.mapHomotopy (homotopy_of_derived_eq f g hfg).some)
  · intro C' I' e' s' hs'
    let := hs'.1
    let := hs'.2
    let a := e.inv ≫ DerivedCategory.Q.map s
    let b := e'.inv ≫ DerivedCategory.Q.map s'
    have : IsIso a := by dsimp [a]; infer_instance
    have : IsIso b := by dsimp [b]; infer_instance
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hf⟩ := exists_comparison I I' (inv a ≫ b)
      refine ⟨f, ?_⟩
      rw [← Category.assoc]
      change a ≫ DerivedCategory.Q.map f = b
      rw [hf, IsIso.hom_inv_id_assoc]
    · intro f g hf hg
      rw [← Category.assoc] at hf hg
      change a ≫ DerivedCategory.Q.map f = b at hf
      change a ≫ DerivedCategory.Q.map g = b at hg
      have : IsIso (a ≫ DerivedCategory.Q.map f) := by rw [hf]; infer_instance
      have : IsIso (DerivedCategory.Q.map f) :=
        IsIso.of_isIso_comp_left a (DerivedCategory.Q.map f)
      refine ⟨map_comparison_isIso F f, ?_⟩
      have hfg : DerivedCategory.Q.map f = DerivedCategory.Q.map g := by
        rw [← cancel_epi a, hf, hg]
      exact DerivedCategory.Q_map_eq_of_homotopy _
        (F.mapHomotopy (homotopy_of_derived_eq f g hfg).some)

end AlgebraicGeometry.Etale
