/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Canonical derived tensor/internal-Hom bijections
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom).
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
The representative equation uses the actual Hom-complex projections, sheaf tensor-Hom
currying, the localization factorization, and the functorial K-injective resolution.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The functorial resolution already used by derived internal Hom, with the scheme's
Grothendieck instance supplied explicitly.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomKInjectiveResolution (X : Scheme.{uCD}) :
    CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ :=
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  CochainComplex.kInjectiveResolutionFunctor.{uCD} _

/-- Inverse of the localized quasi-isomorphism into the fixed resolution.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomResolutionInverse (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj ((schemeHomKInjectiveResolution X).obj M) ⟶
      DerivedCategory.Q.obj M := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _
    ((CochainComplex.toKInjectiveResolution.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))).app M)).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) M).2
  exact inv (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{uCD} _).app M))

/-- The localization factorization for the fixed functorial K-injective model.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeDerivedInternalHomResolutionIso (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M)) := by
  haveI : IsGrothendieckAbelian.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact (Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{uCD} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{uCD} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, M)

/-- Naturality and the actual representative evaluation equation characterize the family.
The chain map ψ is fixed on every total-tensor summand by currying the degree-p
component of φ, projected to Hom(L^q,I(M)^(q+p)). The symmetry restores the order
P^p tensor L^q. The localization factorization and resolution map fix both targets.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def IsCanonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          (β_ (P.X p) (L.X q)).hom ≫
            (SheafOfModules.tensorHomEquiv (L.X q) (P.X p)
              (((schemeHomKInjectiveResolution X).obj M).X n)).symm
              (φ.f p ≫ (Classical.choose (Classical.choose_spec
                (homComplex_exists (R := X.sheaf)))) L
                  ((schemeHomKInjectiveResolution X).obj M)
                  p q n h')) ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)

/-- Existence of the canonical tensor-Hom family.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
Proof: resolve both tensor inputs by K-flat complexes and the target by the fixed
K-injective functor. Curry the Hom-complex components using the sheaf tensor-Hom
bijection. The Hom differential and total-tensor signs make the displayed ψ a chain
map. Maps into a K-injective compute derived Hom; localization and the resolution
map give the displayed equation. Common resolutions show independence of choices,
and componentwise composition gives naturality in all three variables. -/
theorem exists_canonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∃ e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M),
      IsCanonicalDerivedTensorHom X e := by sorry

/-- Uniqueness of the family specified on representatives.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
Proof: on K-flat inputs, Hom(L,I(M)) is K-injective. Every derived morphism into
it is represented by a chain map up to homotopy. Its uncurrying is determined on
every tensor summand, so the representative equation determines the bijection.
Every derived object has such a representative; naturality transports the equality. -/
theorem IsCanonicalDerivedTensorHom.unique (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    {e e' : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)}
    (h : IsCanonicalDerivedTensorHom X e)
    (h' : IsCanonicalDerivedTensorHom X e') : e = e' := by sorry

/-- Canonical family fixed by the representative equation.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeDerivedTensorHomEquiv (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M) :=
  Classical.choose (exists_canonicalDerivedTensorHom X)

end AlgebraicGeometry
