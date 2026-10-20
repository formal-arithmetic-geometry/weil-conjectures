module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
public import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit
public import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare

/-! Declarations of ours that lived in the upstream file `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Smooth base change on the pro-étale site, finite coefficients

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated, and a coefficient ring `Λ` killed by
a nonzero integer invertible on `S`. For a bounded constructible complex `K` of pro-étale
sheaves of `Λ`-modules on `T` (one of étale origin), the pro-étale exchange map
`p^* Rg_* K ⟶ Rh_* e^* K` is an isomorphism (blueprint
`sbc-thm-finite-proetale-smooth-base-change`). It is obtained by conjugating the étale exchange
isomorphism (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth`)
by the site comparison, as recorded by the transport lemma
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` of the proper base change
chapter.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

section
variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  (e : l ⊣ r) (e' : l' ⊣ r') (d : p ⊣ s) (d' : p' ⊣ s')
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}
  (a : l ⋙ A₁ ≅ A₀ ⋙ p) (a' : l' ⋙ A₃ ≅ A₂ ⋙ p')
  (c : g ⋙ A₂ ≅ A₀ ⋙ q) (c' : h ⋙ A₃ ≅ A₁ ⋙ t)
  (b : r ⋙ A₀ ⟶ A₁ ⋙ s) (b' : r' ⋙ A₂ ⟶ A₃ ⋙ s')
  (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
  (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b.app K) ≫ d.counit.app (A₁.obj K) =
    A₁.map (e.counit.app K))
  (hb' : ∀ K, a'.hom.app (r'.obj K) ≫ p'.map (b'.app K) ≫ d'.counit.app (A₃.obj K) =
    A₃.map (e'.counit.app K))
  (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.hom.app (l.obj M) ≫ t.map (a.hom.app M) =
    a'.hom.app (g.obj M) ≫ p'.map (c.hom.app M) ≫ ϑ.app (A₀.obj M))

include a a' hb hb' hsq in
private theorem comparison_mate_transport (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) ≫ b'.app (h.obj K) ≫
      s'.map (c'.hom.app K) =
    c.hom.app (r.obj K) ≫ q.map (b.app K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).natTrans.app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.hom.app (g.obj (r.obj K)))).1
  have hn := a'.hom.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.hom.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b.app K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

end ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

variable (p) in
end AlgebraicGeometry
