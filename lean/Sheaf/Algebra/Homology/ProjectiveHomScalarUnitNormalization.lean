/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.Algebra.Homology.NormalizedRingHomExtension
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Algebra.Homology.ScalarInternalHomData

/-! # Projective Hom scalar comparison and the canonical unit transpose

Source: Stacks Project, more-algebra.tex, Tag 0E1W
(lemma-upgrade-adjoint-tensor-RHom) and Equation 0E1X (equation-base-change-RHom).
(blueprint: lem-trf-projective-hom-scalar-unit-normalization).

All Hom complexes are the shared product Hom complexes. Each projective-source
model comparison is pinned by its evaluation normalization: the chain evaluation
is fixed on generators with sign (-1)^(pq), and its localization is the
tensor-Hom transpose of the comparison. Scalar comparisons below retain the universal
counit and ordinary unit normalizations on every complex, including unbounded ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

namespace CochainComplex

/-- Termwise ordinary scalar extension.
Source: Stacks 0E1X (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomScalarComplex {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) := (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary restriction.
Source: Stacks 0E1W (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomRestrictionComplex {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) := (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)

/-- The canonical localization comparison for exact restriction.
Source: Stacks 0E1W (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomRestrictionComparison {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) := (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors

/-- Source bifunctor for the derived scalar internal-Hom adjunction.
Source: Stacks 0E1W (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomScalarAdjunctionSource {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :=
  ((ModuleCat.ordinaryDerivedExtendScalars φ).op.prod (𝟭 _)) ⋙
    ordinaryModuleDerivedInternalHom S ⋙ ModuleCat.derivedRestrictScalars φ

/-- Target bifunctor for the derived scalar internal-Hom adjunction.
Source: Stacks 0E1W (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomScalarAdjunctionTarget {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :=
  ((𝟭 _).prod (ModuleCat.derivedRestrictScalars φ)) ⋙ ordinaryModuleDerivedInternalHom R

/-- The canonical lax tensor on restriction: the mate of the normalized strong
scalar tensor comparison, with both scalar counits.
Source: Stacks 0E1W and 0GMT
(blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
def projectiveHomRestrictionTensor {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S)
    (adj : ModuleCat.ordinaryDerivedExtendScalars φ ⊣ ModuleCat.derivedRestrictScalars φ)
    (A B : DerivedCategory (ModuleCat.{u} S)) :
    (ModuleCat.derivedRestrictScalars φ).obj A ⊗
        (ModuleCat.derivedRestrictScalars φ).obj B ⟶
      (ModuleCat.derivedRestrictScalars φ).obj (A ⊗ B) :=
  adj.unit.app _ ≫ (ModuleCat.derivedRestrictScalars φ).map
    (Functor.OplaxMonoidal.δ (ModuleCat.ordinaryDerivedExtendScalars φ) _ _ ≫
      (adj.counit.app A ⊗ₘ adj.counit.app B))

/-- Source bifunctor of the unit-transpose scalar comparison.
Source: Stacks 0E1X (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomScalarSource {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :=
  ordinaryModuleDerivedInternalHom R ⋙ ModuleCat.ordinaryDerivedExtendScalars φ

/-- Target bifunctor of the unit-transpose scalar comparison.
Source: Stacks 0E1X (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
abbrev projectiveHomScalarTarget {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) :=
  ((ModuleCat.ordinaryDerivedExtendScalars φ).op.prod
    (ModuleCat.ordinaryDerivedExtendScalars φ)) ⋙ ordinaryModuleDerivedInternalHom S

/-- The precise scalar-adjunction transpose of Hom applied to the scalar unit,
followed by the inverse of the evaluation-normalized internal-Hom comparison.
Source: Stacks 0E1X (blueprint: lem-trf-projective-hom-scalar-unit-normalization). -/
def projectiveHomScalarBeta {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S)
    (adj : ModuleCat.ordinaryDerivedExtendScalars φ ⊣ ModuleCat.derivedRestrictScalars φ)
    (α : projectiveHomScalarAdjunctionSource φ ≅ projectiveHomScalarAdjunctionTarget φ)
    (E L : DerivedCategory (ModuleCat.{u} R)) :
    (projectiveHomScalarSource φ).obj (op E, L) ⟶
      (projectiveHomScalarTarget φ).obj (op E, L) :=
  (adj.homEquiv _ _).symm
    ((ordinaryModuleDerivedInternalHom R).map (Prod.mkHom (𝟙 (op E)) (adj.unit.app L)) ≫
      α.inv.app (op E, (ModuleCat.ordinaryDerivedExtendScalars φ).obj L))

/-- The normalized product-Hom scalar chain map represents the canonical derived
unit transpose, with its actual internal-Hom scalar adjunction and unit formulas.
Source: Stacks 0E1W, lemma-upgrade-adjoint-tensor-RHom, proof, and 0E1X,
equation-base-change-RHom
(blueprint: lem-trf-projective-hom-scalar-unit-normalization).

Proof:
1. Use singleton-site module comparison to work in ordinary modules. Flat scalar
extension preserves quasi-isomorphisms even for unbounded complexes by tensoring
cycles and boundaries. Its universal derived counit is consequently invertible
on every complex. The flat projective-Hom models identify unit and counit with
1 tensor x and scalar multiplication, and identify Hom from a bounded-above
projective complex with derived Hom (lem-trf-flat-projective-hom-models).
2. On each product coordinate define a(g)(x) = g(1 tensor x), with inverse
v(h)(t tensor x) = t h(x). Balancedness and S-linearity give both inverse
identities. Evaluating the signed Hom differential proves they are chain maps.
No tensor/infinite-product interchange is used (def-sc-module-total-hom-complex).
3. The projective Hom evaluation model has sign (-1)^(pn) on both sides.
The restriction tensor is the counit mate of the normalized strong tensor map.
Transport its pure-generator formula along a K-flat resolution of the Hom
complex; P and U(FP) are K-flat, so these tensor maps are quasi-isomorphisms.
The scalar unit followed by this lax tensor sends x tensor g to
(1 tensor x) tensor g. Thus the localized a has exactly the evaluation
normalization of lem-sfb-dc-hom-scalar-adjunction, and uniqueness identifies it.
Use lem-pod-projective-hom-evaluation-model and def-sfb-scalar-hom-comparison-data.
4. Hom applied to the unit is the chain map k(f)(x) = 1 tensor f(x).
Its composite with v sends f to the map t tensor x to t tensor f(x).
5. The scalar adjoint is the ordinary counit after extension of v k; it sends
s tensor f, evaluated at t tensor x, to st tensor f(x). The normalization of
lem-pc-normalized-ring-hom-extension identifies it with chi. Localize and use
the universal flat and projective model comparisons to obtain the displayed square.
6. Bifunctoriality, naturality of the scalar unit, the natural scalar-Hom
isomorphism and the scalar counit prove naturality for all derived morphisms.
This includes inverses of quasi-isomorphisms. The natural projective model
comparisons therefore give representative independence and target invariance.
No finiteness or target boundedness is used, and chi need not be invertible. -/
theorem projective_hom_scalar_unit_normalization {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat) :
    ∃ (c : DerivedCategory.Q ⋙ ModuleCat.ordinaryDerivedExtendScalars φ ≅
          projectiveHomScalarComplex φ ⋙ DerivedCategory.Q)
      (adj : ModuleCat.ordinaryDerivedExtendScalars φ ⊣ ModuleCat.derivedRestrictScalars φ),
      (∀ C : CochainComplex (ModuleCat.{u} R) ℤ,
        c.hom.app C = (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app C) ∧
      (∀ C : CochainComplex (ModuleCat.{u} R) ℤ,
        adj.unit.app (DerivedCategory.Q.obj C) ≫
            (ModuleCat.derivedRestrictScalars φ).map (c.hom.app C) ≫
            (projectiveHomRestrictionComparison φ).hom.app
              ((projectiveHomScalarComplex φ).obj C) =
          DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.app C)) ∧
      (∀ D : CochainComplex (ModuleCat.{u} S) ℤ,
        (ModuleCat.ordinaryDerivedExtendScalars φ).map
            ((projectiveHomRestrictionComparison φ).hom.app D) ≫
            c.hom.app ((projectiveHomRestrictionComplex φ).obj D) ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).counit.app
                D) = adj.counit.app (DerivedCategory.Q.obj D)) ∧
      ∃ α : projectiveHomScalarAdjunctionSource φ ≅ projectiveHomScalarAdjunctionTarget φ,
        (∀ (E : DerivedCategory (ModuleCat.{u} R))
          (D : DerivedCategory (ModuleCat.{u} S)),
          E ◁ α.hom.app (op E, D) ≫
              (ihom.ev E).app ((ModuleCat.derivedRestrictScalars φ).obj D) =
            adj.unit.app E ▷ _ ≫
              projectiveHomRestrictionTensor φ adj _ _ ≫
              (ModuleCat.derivedRestrictScalars φ).map
                ((ihom.ev ((ModuleCat.ordinaryDerivedExtendScalars φ).obj E)).app D)) ∧
        ∃ β : projectiveHomScalarSource φ ⟶ projectiveHomScalarTarget φ,
          (∀ E L : DerivedCategory (ModuleCat.{u} R),
            β.app (op E, L) = projectiveHomScalarBeta φ adj α E L) ∧
          ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
            (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
            (hp : ∀ i : ℤ, Module.Projective R (P.X i))
            (N : CochainComplex (ModuleCat.{u} R) ℤ),
            ∃ (hbS : ∃ n : ℤ, ∀ i : ℤ, n < i →
                  IsZero (((projectiveHomScalarComplex φ).obj P).X i))
              (hpS : ∀ i : ℤ,
                Module.Projective S (((projectiveHomScalarComplex φ).obj P).X i))
              (evH : P ⊗ moduleHomComplex P N ⟶ N)
              (evT : P ⊗ moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj ((projectiveHomScalarComplex φ).obj N)) ⟶
                (projectiveHomRestrictionComplex φ).obj ((projectiveHomScalarComplex φ).obj N))
              (evS : (projectiveHomScalarComplex φ).obj P ⊗
                  moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                    ((projectiveHomScalarComplex φ).obj N) ⟶
                (projectiveHomScalarComplex φ).obj N)
              (eH : DerivedCategory.Q.obj (moduleHomComplex P N) ≅
                (ordinaryModuleDerivedInternalHom R).obj
                  (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj N))
              (eT : DerivedCategory.Q.obj (moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj
                    ((projectiveHomScalarComplex φ).obj N))) ≅
                (ordinaryModuleDerivedInternalHom R).obj (op (DerivedCategory.Q.obj P),
                  DerivedCategory.Q.obj ((projectiveHomRestrictionComplex φ).obj
                    ((projectiveHomScalarComplex φ).obj N))))
              (eS : DerivedCategory.Q.obj (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                  ((projectiveHomScalarComplex φ).obj N)) ≅
                (ordinaryModuleDerivedInternalHom S).obj
                  (op (DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj P)),
                    DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj N)))
              (χ : (projectiveHomScalarComplex φ).obj (moduleHomComplex P N) ⟶
                moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                  ((projectiveHomScalarComplex φ).obj N))
              (a : (projectiveHomRestrictionComplex φ).obj
                  (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                    ((projectiveHomScalarComplex φ).obj N)) ≅
                moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj ((projectiveHomScalarComplex φ).obj N)))
              (k : moduleHomComplex P N ⟶ moduleHomComplex P
                ((projectiveHomRestrictionComplex φ).obj ((projectiveHomScalarComplex φ).obj N))),
              (∀ (p q : ℤ) (x : P.X p) (f : (moduleHomComplex P N).X q),
                (evH.f (p + q)) ((HomologicalComplex.ιTensorObj P (moduleHomComplex P N)
                  p q (p + q) rfl) (x ⊗ₜ[R] f)) = (p * q).negOnePow • (f.v p (p + q) rfl) x) ∧
              (∀ (p q : ℤ) (x : P.X p) (f : (moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj
                    ((projectiveHomScalarComplex φ).obj N))).X q),
                (evT.f (p + q)) ((HomologicalComplex.ιTensorObj P (moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj
                    ((projectiveHomScalarComplex φ).obj N))) p q (p + q) rfl) (x ⊗ₜ[R] f)) =
                  (p * q).negOnePow • (f.v p (p + q) rfl) x) ∧
              (∀ (p q : ℤ) (x : ((projectiveHomScalarComplex φ).obj P).X p)
                (f : (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                  ((projectiveHomScalarComplex φ).obj N)).X q),
                (evS.f (p + q)) ((HomologicalComplex.ιTensorObj
                  ((projectiveHomScalarComplex φ).obj P)
                  (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                    ((projectiveHomScalarComplex φ).obj N)) p q (p + q) rfl) (x ⊗ₜ[S] f)) =
                  (p * q).negOnePow • (f.v p (p + q) rfl) x) ∧
              (IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N)) ∧
                Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P N) ≫
                    DerivedCategory.Q.map evH =
                  DerivedCategory.Q.obj P ◁ eH.hom ≫
                    (ihom.ev (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)) ∧
              (IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P
                  ((projectiveHomRestrictionComplex φ).obj
                    ((projectiveHomScalarComplex φ).obj N)))) ∧
                Functor.LaxMonoidal.μ DerivedCategory.Q P (moduleHomComplex P
                    ((projectiveHomRestrictionComplex φ).obj
                      ((projectiveHomScalarComplex φ).obj N))) ≫ DerivedCategory.Q.map evT =
                  DerivedCategory.Q.obj P ◁ eT.hom ≫
                    (ihom.ev (DerivedCategory.Q.obj P)).app
                      (DerivedCategory.Q.obj ((projectiveHomRestrictionComplex φ).obj
                        ((projectiveHomScalarComplex φ).obj N)))) ∧
              (IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q ((projectiveHomScalarComplex φ).obj P)
                  (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                    ((projectiveHomScalarComplex φ).obj N))) ∧
                Functor.LaxMonoidal.μ DerivedCategory.Q ((projectiveHomScalarComplex φ).obj P)
                    (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                      ((projectiveHomScalarComplex φ).obj N)) ≫ DerivedCategory.Q.map evS =
                  DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj P) ◁ eS.hom ≫
                    (ihom.ev (DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj P))).app
                      (DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj N))) ∧
              (∀ (n p : ℤ) (s t : S) (f : (moduleHomComplex P N).X n) (x : P.X p),
                (((χ.f n) (s ⊗ₜ[R,φ] f)).v p (p + n) rfl) (t ⊗ₜ[R,φ] x) =
                  (s * t) ⊗ₜ[R,φ] ((f.v p (p + n) rfl) x)) ∧
              (∀ (n p : ℤ)
                (g : (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                  ((projectiveHomScalarComplex φ).obj N)).X n) (x : P.X p),
                (((a.hom.f n) g).v p (p + n) rfl) x =
                  (g.v p (p + n) rfl) ((1 : S) ⊗ₜ[R,φ] x)) ∧
              (∀ (n p : ℤ) (t : S)
                (h : (moduleHomComplex P ((projectiveHomRestrictionComplex φ).obj
                  ((projectiveHomScalarComplex φ).obj N))).X n) (x : P.X p),
                (((a.inv.f n) h).v p (p + n) rfl) (t ⊗ₜ[R,φ] x) =
                  t • (@id (((projectiveHomScalarComplex φ).obj N).X (p + n))
                    ((h.v p (p + n) rfl) x))) ∧
              (∀ (n p : ℤ) (f : (moduleHomComplex P N).X n) (x : P.X p),
                (((k.f n) f).v p (p + n) rfl) x =
                  (1 : S) ⊗ₜ[R,φ] ((f.v p (p + n) rfl) x)) ∧
              χ = ((((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).homEquiv
                _ _).symm (k ≫ a.inv)) ∧
              (projectiveHomRestrictionComparison φ).hom.app
                  (moduleHomComplex ((projectiveHomScalarComplex φ).obj P)
                    ((projectiveHomScalarComplex φ).obj N)) ≫
                  DerivedCategory.Q.map a.hom ≫ eT.hom =
                (ModuleCat.derivedRestrictScalars φ).map
                    (eS.hom ≫ (ordinaryModuleDerivedInternalHom S).map
                      (Prod.mkHom (c.hom.app P).op (𝟙 _))) ≫
                  α.hom.app (op (DerivedCategory.Q.obj P),
                    DerivedCategory.Q.obj ((projectiveHomScalarComplex φ).obj N)) ≫
                  (ordinaryModuleDerivedInternalHom R).map
                    (Prod.mkHom (𝟙 _) ((projectiveHomRestrictionComparison φ).hom.app
                      ((projectiveHomScalarComplex φ).obj N))) ∧
              DerivedCategory.Q.map k ≫ eT.hom =
                eH.hom ≫
                  (ordinaryModuleDerivedInternalHom R).map (Prod.mkHom (𝟙 _)
                    (adj.unit.app (DerivedCategory.Q.obj N) ≫
                      (ModuleCat.derivedRestrictScalars φ).map (c.hom.app N) ≫
                      (projectiveHomRestrictionComparison φ).hom.app
                        ((projectiveHomScalarComplex φ).obj N))) ∧
              β.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj N) =
                (ModuleCat.ordinaryDerivedExtendScalars φ).map eH.inv ≫
                  c.hom.app (moduleHomComplex P N) ≫ DerivedCategory.Q.map χ ≫
                  eS.hom ≫
                  (ordinaryModuleDerivedInternalHom S).map
                    (Prod.mkHom (c.hom.app P).op (c.inv.app N)) := by
  sorry

end CochainComplex
