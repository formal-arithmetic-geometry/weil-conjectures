/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplexToSingle
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar finite-projective dual realization

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ, scalar
finite-free-retract calculation (blueprint: lem-sfb-scalar-perfect-dual-realization).
The realization uses the existing constant-module sheaf and ordinary change of rings.
The scalar dual is the existing module-valued Hom complex into R[0].
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ScalarPerfectDual

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Type u) [CommRing R] (B : Sheaf J CommRingCat.{u})
  (α : (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of R) ⟶ B)

/-- The existing category of B-module sheaves.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev Modules := ringedSiteModules.{u} ((sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj B)

/-- Ordinary scalar realization, by constant sheafification and sheaf change of rings.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realize (V : ModuleCat.{u} R) : Modules J B :=
  SheafOfModules.changeOfRings.{u, u, u} α ((SheafOfModules.constantCoefficientModule J R).obj V)

/-- Realization of a linear map is the sheafified map id_B tensor f.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realizeMap {V W : ModuleCat.{u} R} (f : V ⟶ W) :
    realize J R B α V ⟶ realize J R B α W :=
  SheafOfModules.changeOfRingsHom.{u, u, u} α _
    ((SheafOfModules.constantCoefficientModule J R).map f)

/-- The maps of scalar realization satisfy the additive functor laws.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: constant sheafification is additive. Before the second sheafification,
id_B tensor f preserves identities, composites and sums, by evaluation on pure tensors.
The additive module sheafification functor preserves these three equalities. -/
theorem realizeMap_laws :
    (∀ V : ModuleCat.{u} R, realizeMap J R B α (𝟙 V) = 𝟙 _) ∧
    (∀ {V W T : ModuleCat.{u} R} (f : V ⟶ W) (g : W ⟶ T),
      realizeMap J R B α (f ≫ g) = realizeMap J R B α f ≫ realizeMap J R B α g) ∧
    (∀ {V W : ModuleCat.{u} R} (f g : V ⟶ W),
      realizeMap J R B α (f + g) = realizeMap J R B α f + realizeMap J R B α g) := by
  sorry

/-- The canonical additive scalar-realization functor.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realization : ModuleCat.{u} R ⥤ Modules J B where
  obj := realize J R B α
  map := realizeMap J R B α
  map_id := (realizeMap_laws J R B α).1
  map_comp := (realizeMap_laws J R B α).2.1

/-- Scalar realization is additive, so it acts termwise on complexes.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: this is the sum clause of realizeMap_laws. -/
instance realization_additive : (realization J R B α).Additive where
  map_add {_V _W} {f g} := (realizeMap_laws J R B α).2.2 f g

/-- Termwise scalar realization, including the differential.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev complexRealization :=
  (realization J R B α).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The image of a scalar in the sheaf B.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def scalar (U : Cᵒᵖ) (r : R) : B.obj.obj U :=
  α.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r)

/-- A constant local section of the existing constant-module sheaf.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def constantElement (V : ModuleCat.{u} R) (U : Cᵒᵖ) (v : V) :
    ((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (SheafOfModules.constantCoefficientUnit J R)).unit.app
      ((SheafOfModules.strictPerfectConstantPresheaf (C := C) R).obj V)).app U) v

/-- The actual local pure tensor b tensor v in scalar realization.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def tensorElement (V : ModuleCat.{u} R) (U : Cᵒᵖ) (b : B.obj.obj U) (v : V) :
    (realize J R B α V).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} α
        ((SheafOfModules.constantCoefficientModule J R).obj V))).app U)
    (@TensorProduct.tmul _ _ (B.obj.obj U)
      (((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom)
      (((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U).isModule
      b (constantElement J R V U v))


/-- The scalar dual uses the existing total Hom complex, with its signed differential.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev dual (F : CochainComplex (ModuleCat.{u} R) ℤ) :=
  CochainComplex.moduleHomComplex F
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- Projection of the total scalar Hom complex onto its unique nonzero target factor.
This specifies both its terms and its precise differential sign.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: evaluate a degree-q cochain at (-q,0), then use the canonical single-complex
identification in degree zero. All other factors have zero target. The inverse extends
by zero, so this is a linear isomorphism. The Hom differential has zero target term;
its surviving term is -(-1)^q times precomposition by d_F. -/
theorem dual_coordinates (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ τ : ∀ q : ℤ, (dual R F).X q ≅ ModuleCat.of R (Module.Dual R (F.X (-q))),
      (∀ (q : ℤ) (z : (dual R F).X q),
        (τ q).hom z =
          (z.v (-q) 0 (neg_add_cancel q) ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (ModuleCat.of R R)).hom).hom) ∧
      ∀ q : ℤ, (dual R F).d q (q + 1) ≫ (τ (q + 1)).hom =
        (τ q).hom ≫ ModuleCat.ofHom
          (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap) := by
  sorry

/-- The canonical evaluation formula determines a unique scalar-dual comparison.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: the formula is balanced, B-linear, additive and commutes with restriction.
Extend first over the constant-module sheafification, then over the scalar tensor
sheafification. Uniqueness follows from local tensor generators. -/
theorem evaluation_existsUnique (V : ModuleCat.{u} R) :
    ∃! β : realize J R B α (ModuleCat.of R (Module.Dual R V)) ⟶
        SheafOfModules.homObj (R := B) (realize J R B α V)
          (SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
      ∀ (U : Cᵒᵖ) (b b' : B.obj.obj U) (φ : Module.Dual R V) (v : V),
        (β.val.app U (tensorElement J R B α _ U b φ)).app
          (op (Over.mk (𝟙 U.unop))) (tensorElement J R B α V U b' v) =
            b * b' * scalar J R B α U (φ v) := by
  sorry

/-- The evaluation comparison, uniquely characterized by its formula on local generators.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def evaluation (V : ModuleCat.{u} R) :=
  (evaluation_existsUnique J R B α V).exists.choose

/-- Evaluation is natural under scalar module maps and invertible on finite projectives.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: both naturality composites send b tensor ψ, evaluated at b' tensor v, to
bb'ψ(f(v)). Uniqueness of sheafification gives equality. For a finite projective V,
choose a finite free splitting, with dual generators v_j, λ_j. The inverse sends h
to the finite sum of h(1 tensor v_j) tensor λ_j. The identities v=Σλ_j(v)v_j and
φ=Σφ(v_j)λ_j prove both inverse relations. Rank zero and V=0 are included. -/
theorem evaluation_natural_isIso :
    (∀ {V W : ModuleCat.{u} R} (f : V ⟶ W),
      (realization J R B α).map (ModuleCat.ofHom f.hom.dualMap) ≫
          evaluation J R B α V =
        evaluation J R B α W ≫ SheafOfModules.homObjMap (R := B)
          ((realization J R B α).map f) (𝟙 _)) ∧
    ∀ (V : ModuleCat.{u} R), Module.Finite R V → Module.Projective R V →
      IsIso (evaluation J R B α V) := by
  sorry

/-- The canonical scalar degree coordinates, specified by evaluation at (-q,0).
Source: Stacks 0A8X (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def coordinates (F : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (dual_coordinates R F).choose

/-- B in degree zero, in the existing cochain-complex category.
Source: Stacks 08JH (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev unitComplex := (CochainComplex.singleFunctor (Modules J B) 0).obj
  (SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- A bounded scalar finite-projective complex realizes to finite-free retract terms;
internal sheaf Hom out of each term is exact, and every K-injective resolution of B[0]
gives a quasi-isomorphism of Hom complexes. No flatness hypothesis is used.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof:
1. Use the supplied scalar splittings i_r,p_r, as in the coefficient-package node.
Constant sheafification and ordinary scalar extension preserve their splitting relation.
The coordinate maps identify C_B(R^N) with B^N, including N=0. This constructs the package.
2. Apply lem-sfb-ringed-site-finite-retract-dual-exact to each resulting term. It gives
exactness on short exact sequences of sheaves, not exactness of global sections.
3. Additivity gives C_B(0)=0, so the realized complex has the same finite bounds.
Apply lem-pc-bounded-exact-term-hom-quasi-iso to B[0]→I for any K-injective resolution.
Its target can be unbounded. This is the canonical comparison used in derived Hom. -/
theorem scalarPerfectDualRealization
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F)
    (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)) :
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackage
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      ((complexRealization J R B α).obj F)) ∧
    (∀ (q : ℤ) (S : ShortComplex (Modules J B)), S.ShortExact →
      ∃ hz : SheafOfModules.homObjMap (R := B)
          (𝟙 (((complexRealization J R B α).obj F).X q)) S.f ≫
        SheafOfModules.homObjMap (R := B)
          (𝟙 (((complexRealization J R B α).obj F).X q)) S.g = 0,
        (ShortComplex.mk
          (SheafOfModules.homObjMap (R := B)
            (𝟙 (((complexRealization J R B α).obj F).X q)) S.f)
          (SheafOfModules.homObjMap (R := B)
            (𝟙 (((complexRealization J R B α).obj F).X q)) S.g) hz).ShortExact) ∧
    ∀ (I : CochainComplex (Modules J B) ℤ) (ι : unitComplex J B ⟶ I),
      QuasiIso ι → I.IsKInjective →
        QuasiIso (((homComplexFunctor (R := B)).obj
          (op ((complexRealization J R B α).obj F))).map ι) := by
  sorry

/-- The degreewise scalar evaluation maps form the uniquely normalized complex isomorphism.
Source: Stacks 08JJ and 0A8X (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: in degree q the only surviving Hom factor is Hom_B(E^(-q),B).
Use evaluation at F^(-q), preceded by the scalar Hom coordinate isomorphism.
Finite-projective evaluation is invertible by evaluation_natural_isIso. Naturality
for d_F identifies the two differentials, both -(-1)^q times precomposition.
The product projections therefore assemble these components into a chain isomorphism.
The surviving projection is invertible, so the component equation determines it uniquely. -/
theorem comparison_existsUnique
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    ∃! κ : (complexRealization J R B α).obj (dual R F) ≅
        signedSheafDualComplex (R := B) ((complexRealization J R B α).obj F)
          (SheafOfModules.unit.{u, u, u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
      ∀ q : ℤ, HEq (κ.hom.f q)
        ((realization J R B α).map ((coordinates R F q).hom) ≫
          evaluation J R B α (F.X (-q))) := by
  sorry

/-- The cochain comparison is determined by the displayed signed degreewise evaluations.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def comparison (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :=
  (comparison_existsUnique J R B α F P).exists.choose

/-- Scalar duality and the cochain comparison are contravariantly natural.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: precompose scalar cochains by f to construct g. The scalar coordinates identify
its components with the linear dual of f^(-q). The chain-map law follows from that of f.
For the comparison square, project to the unique nonzero Hom factor; both sides are
scalar evaluation precomposed with f^(-q), equal by evaluation_natural_isIso.
The invertible surviving projections give the equality of chain maps. -/
theorem comparison_natural
    (F G : CochainComplex (ModuleCat.{u} R) ℤ)
    (PF : ModuleCat.StrictPerfectCoefficientPackage F)
    (PG : ModuleCat.StrictPerfectCoefficientPackage G) (f : F ⟶ G) :
    ∃ g : dual R G ⟶ dual R F,
      (∀ q : ℤ, g.f q ≫ (coordinates R F q).hom =
        (coordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap) ∧
      ∀ q : ℤ,
        ((complexRealization J R B α).map g).f q ≫ (comparison J R B α F PF).hom.f q =
          (comparison J R B α G PG).hom.f q ≫
            SheafOfModules.homObjMap (R := B)
              (((complexRealization J R B α).map f).f (-q)) (𝟙 _) := by
  sorry

/-- The signed, degreewise normalized comparison is an isomorphism to the recorded Hom complex.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: compose comparison with the inverse of homComplex_to_single_iso. That existing
isomorphism projects the Hom product to its only nonzero target factor (-q,0), and
identifies its differential with exactly the signedSheafDualComplex differential.
Thus this is the same degreewise evaluation isomorphism in the product-Hom presentation. -/
theorem ordinary_comparison
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    Nonempty ((complexRealization J R B α).obj (dual R F) ≅
      homComplex (R := B) ((complexRealization J R B α).obj F) (unitComplex J B)) := by
  sorry

/-- Both ordinary dual complexes have the reversed degree bounds, including empty intervals.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: outside [-b,-a], the term F^(-q) is zero. Its scalar linear dual is zero;
the unique-factor description of both Hom complexes and C_B(0)=0 imply both vanish. -/
theorem dual_bounds (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)) :
    ∀ q : ℤ, q < -b ∨ -a < q →
      IsZero (((complexRealization J R B α).obj (dual R F)).X q) ∧
      IsZero ((homComplex (R := B) ((complexRealization J R B α).obj F)
        (unitComplex J B)).X q) := by
  sorry

variable [HasDerivedCategory.{w} (Modules J B)]

/-- The realized scalar dual naturally represents derived internal Hom into B.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof:
1. Use scalarPerfectDualRealization: for every K-injective resolution B[0]→I the ordinary
Hom comparison is a quasi-isomorphism. Its image under Q is an isomorphism.
2. The target computes the recorded derivedInternalHomOfUniverses, independently of
resolution. Use its comparison with the fixed functorial K-injective replacement.
3. Use ordinary_comparison to pass from the signed model to the product Hom model,
then compose its image under Q with the preceding isomorphism. Naturality of
the fixed resolution and comparison_natural give the displayed naturality square.
The scalar cochain-coordinate condition fixes g as precomposition by f.
There is no flatness condition on the scalar morphism to B. -/
theorem derived_comparison_natural :
    ∃ e : ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ)
        (P : ModuleCat.StrictPerfectCoefficientPackage F)
        (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)),
      DerivedCategory.Q.obj ((complexRealization J R B α).obj (dual R F)) ≅
        (derivedInternalHomOfUniverses.{u, u, u, w} J B).obj
          (op (DerivedCategory.Q.obj ((complexRealization J R B α).obj F)),
            DerivedCategory.Q.obj (unitComplex J B)),
      ∀ (F G : CochainComplex (ModuleCat.{u} R) ℤ)
        (PF : ModuleCat.StrictPerfectCoefficientPackage F)
        (PG : ModuleCat.StrictPerfectCoefficientPackage G)
        (a b c d : ℤ)
        (hF : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
        (hG : ∀ q : ℤ, q < c ∨ d < q → IsZero (G.X q))
        (f : F ⟶ G) (g : dual R G ⟶ dual R F),
        (∀ q : ℤ, g.f q ≫ (coordinates R F q).hom =
          (coordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap) →
        DerivedCategory.Q.map ((complexRealization J R B α).map g) ≫
            (e F PF a b hF).hom =
          (e G PG c d hG).hom ≫
            (derivedInternalHomOfUniverses.{u, u, u, w} J B).map
              ((DerivedCategory.Q.map ((complexRealization J R B α).map f)).op,
                𝟙 (DerivedCategory.Q.obj (unitComplex J B))) := by
  sorry

end CategoryTheory.ScalarPerfectDual
