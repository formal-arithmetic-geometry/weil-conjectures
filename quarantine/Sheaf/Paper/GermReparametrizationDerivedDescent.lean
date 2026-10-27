/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.TraceBoundedQuotientStalkRealization
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SfIntegralConstructible
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import all Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.StrictQuotientStalkReindexing
import Sheaf.Paper.QuotientStalkNaturalDescent

/-!
# Germ reparametrization and integral derived descent

Source: Stacks Project, sites.tex, Tag 05V1 (lemma-point-morphism-sites);
blueprint main-20261015, thm-trf-l-function-euler-product.proof.md, Step 1,
Local powers (b) (blueprint: lem-trf-germ-reparametrization-derived-descent).

All quotient transitions, good truncations, cone maps and realization arrows are
those of the recorded dependencies. Exponents n >= 1 are indexed by n + 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] trfCompletedPointFibre
  trfQuotientSectionTower trfQuotientStalkRealizationArrow
  integralOperationsRoosMap HasDerivedCategory.standard

/-- Cancellation against the prescribed realization tests a descended map on any
one good representative of each object. Equality of endpoints is kept explicit
so this also applies to the heterogeneous action laws. -/
private theorem trfNormalizedMapHEq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (T : Scheme.{u})
    (e : ∀ v : Spec (.of D.k) ⟶ T,
      trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v)
    (he : ∀ (v : Spec (.of D.k) ⟶ T) (M : sfIntegralConstructibleCategory l E T)
      (P : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
      IsIso (trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q))
    (v w w' : Spec (.of D.k) ⟶ T) (h : w = w')
    (a : trfQuotientStalkTower l E v ⟶ trfQuotientStalkTower l E w)
    (b : trfQuotientStalkTower l E v ⟶ trfQuotientStalkTower l E w')
    (hab : HEq a b)
    (f : (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D v ⟶
      (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D w)
    (g : (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D v ⟶
      (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D w')
    (hf : ∀ (M : sfIntegralConstructibleCategory l E T)
      (P : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
      f.app M ≫ trfQuotientStalkRealizationArrow l E D w (e w) M.obj P q =
        trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q ≫
          (trfIntegralModuleQ l E).map (integralOperationsRoosMap (a.app P.obj)))
    (hg : ∀ (M : sfIntegralConstructibleCategory l E T)
      (P : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
      g.app M ≫ trfQuotientStalkRealizationArrow l E D w' (e w') M.obj P q =
        trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q ≫
          (trfIntegralModuleQ l E).map (integralOperationsRoosMap (b.app P.obj))) :
    HEq f g := by
  classical
  subst w'
  have hab' : a = b := eq_of_heq hab
  subst b
  apply heq_of_eq
  apply NatTrans.ext
  funext M
  let L := integralOperationsGoodLocalization l E T
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E T) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E T).ι
  have : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E T
  have : L.EssSurj := Localization.essSurj L W
  let P := L.objPreimage M.obj
  let q : DerivedCategory.Q.obj P.obj ≅ M.obj := L.objObjPreimageIso M.obj
  have := he w M P q
  apply (cancel_mono (trfQuotientStalkRealizationArrow l E D w (e w) M.obj P q)).mp
  exact (hf M P q).trans (hg M P q).symm

/-- Germ reindexing gives strict quotient-stalk tower isomorphisms and their
resolution-independent natural descent on the full integral constructible category.
The two cocone equations specify both coordinates of the whole cone map.
The last equations express the opposite action law and the identity, hence all
finite successions, including the empty succession.

Source: Stacks Tag 05V1 and blueprint Euler-product proof, Local powers (b)
(blueprint: lem-trf-germ-reparametrization-derived-descent).

Proof:
1. Reindex pointed neighbourhoods by Spec(alpha), leaving their objects, arrows
   and sections unchanged (def-weil-proetale-geometric-stalk). This preserves every
   germ relation. Reindexing by alpha inverse is inverse. Common refinements prove
   addition and scalar compatibility, and sheaf maps give naturality.
2. Apply this in each degree and each quotient of P. The differential and quotient
   transition change only the section of a germ, so both squares commute strictly.
   This gives a natural A_n-linear level isomorphism and an R-linear tower isomorphism.
3. If Q is the product of these level maps and D=1-s, then Qd=dQ and QD=D'Q.
   Consequently (b,a) maps to (Qb,Qa), and its differential is
   (-dQb-D'Qa,dQa)=(Q(-db-Da),Qda). The inverse is diagonal too.
4. Functorial kernels and cokernels commute with this rule. Thus the upper and
   lower good-truncation arrows commute with it, also when the interval is a point.
   lem-trf-bounded-quotient-stalk-realization identifies J_v(M) with the localized
   whole cone by the prescribed e_v,P, natural for every representative chain map.
5. A representative homotopy h induces the cone homotopy (-product(h),product(h));
   its mixed terms cancel since h commutes with transitions. Hence these maps
   factor through homotopy classes. lem-pur-integral-operations-well-defined gives
   the canonical resolution comparisons, and exact point sections give J_v.
6. By lem-pur-quasi-isos-saturated-triangulated, every derived arrow is a roof.
   Resolve its apex by lem-pc-kflat-resolution; it remains a representative of a
   constructible object because that full subcategory is isomorphism invariant.
   Define r objectwise by e_target inverse, then the diagonal cone map, then e_source.
7. Invert the naturality square for the roof denominator and compose with the
   numerator square. Conjugation by e proves naturality for the derived arrow
   itself, independent of its roof. Taking the identity between two representatives
   proves independence of P and compatibility with canonical resolution comparisons.
8. Successive rules send [U,u,x] to [U,u Spec(alpha) Spec(beta),x]. Spec reverses
   composition, so this is beta after alpha, without a commutation assumption.
   The identity fixes germs. Products and the diagonal cone construction preserve
   these equalities. Cancel the intermediate e's to get the same laws for r;
   induction proves every finite succession, with empty succession the identity.
-/
theorem trfGermReparametrizationDerivedDescent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)] :
    ∃ (R : ∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k),
        trfQuotientStalkTower l E v ≅ trfQuotientStalkTower l E
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v))
      (e : ∀ v : Spec (.of D.k) ⟶ T,
        trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v)
      (r : ∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k),
        (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D v ≅
          (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D
            (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)),
      (∀ v : Spec (.of D.k) ⟶ T,
        ∃ (γ : ∀ n : ℕ,
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
                (Padic.coefficientExtensionRing l E (n + 1)))
          (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
            pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
              finiteCoefficientModuleStalkFunctor v
                (Padic.coefficientExtensionRing l E (n + 1))),
          TrfQuotientGermNormalized l E D v γ δ (e v)) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k)
        (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) (i : ℤ),
        HEq ((((R v α).hom.app P).app (op n)).f i).hom.toFun
          ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1)) v α).hom.app
            (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i)).hom.toFun) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k)
        (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) (i : ℤ)
        (N : ProEtaleGeometricNeighbourhood v)
        (x : ((((trfQuotientTower l E T).obj P).obj (op n)).X i).val.obj (op N.right)),
        (((R v α).hom.app P).app (op n)).f i
            ((colimit.ι ((proEtaleGeometricNeighbourhoodForget v).op ⋙
              ((((trfQuotientTower l E T).obj P).obj (op n)).X i).val.presheaf) (op N)) x) =
          (colimit.ι ((proEtaleGeometricNeighbourhoodForget
              (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).op ⋙
                ((((trfQuotientTower l E T).obj P).obj (op n)).X i).val.presheaf)
            (op ((proEtaleStalkNeighbourhoodReparam v α).obj N))) x) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k)
        (P : CochainComplex (integralTowerModules l E T) ℤ),
        (∀ n : ℕ,
          integralOperationsRoosMap ((R v α).hom.app P) ≫
              CochainComplex.mappingCocone.fst
                (scalarRoosBoundary ((trfQuotientStalkTower l E _).obj P)) ≫
              Pi.π (fun m ↦ ((trfQuotientStalkTower l E _).obj P).obj (op m)) n =
            CochainComplex.mappingCocone.fst
                (scalarRoosBoundary ((trfQuotientStalkTower l E v).obj P)) ≫
              Pi.π (fun m ↦ ((trfQuotientStalkTower l E v).obj P).obj (op m)) n ≫
              ((R v α).hom.app P).app (op n)) ∧
        (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ),
          (integralOperationsRoosMap ((R v α).hom.app P)).f i ≫
              (CochainComplex.mappingCocone.snd
                (scalarRoosBoundary ((trfQuotientStalkTower l E _).obj P))).v i j h ≫
              (Pi.π (fun m ↦ ((trfQuotientStalkTower l E _).obj P).obj (op m)) n).f j =
            (CochainComplex.mappingCocone.snd
                (scalarRoosBoundary ((trfQuotientStalkTower l E v).obj P))).v i j h ≫
              (Pi.π (fun m ↦ ((trfQuotientStalkTower l E v).obj P).obj (op m)) n).f j ≫
              (((R v α).hom.app P).app (op n)).f j)) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k)
        (P : CochainComplex (integralTowerModules l E T) ℤ) (p q : ℤ),
        ∃ (U : trfUpperTower ((trfQuotientTower l E T).obj P) q ⋙
              (integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ) ≅
            trfUpperTower ((trfQuotientTower l E T).obj P) q ⋙
              (integralCoefficientModuleStalkFunctor l E
                (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).mapHomologicalComplex (.up ℤ))
          (B : trfBoundedTower ((trfQuotientTower l E T).obj P) p q ⋙
              (integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ) ≅
            trfBoundedTower ((trfQuotientTower l E T).obj P) p q ⋙
              (integralCoefficientModuleStalkFunctor l E
                (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).mapHomologicalComplex (.up ℤ)),
          U.hom ≫ Functor.whiskerRight
              (trfUpperArrow ((trfQuotientTower l E T).obj P) q)
              ((integralCoefficientModuleStalkFunctor l E
                (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).mapHomologicalComplex (.up ℤ)) =
            Functor.whiskerRight (trfUpperArrow ((trfQuotientTower l E T).obj P) q)
              ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)) ≫
                (R v α).hom.app P ∧
          U.hom ≫ Functor.whiskerRight
              (trfLowerArrow ((trfQuotientTower l E T).obj P) p q)
              ((integralCoefficientModuleStalkFunctor l E
                (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).mapHomologicalComplex (.up ℤ)) =
            Functor.whiskerRight (trfLowerArrow ((trfQuotientTower l E T).obj P) p q)
              ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)) ≫
                B.hom) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (M : sfIntegralConstructibleCategory l E T)
        (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
        IsIso (trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q)) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k)
        (M : sfIntegralConstructibleCategory l E T)
        (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
        (r v α).hom.app M ≫
            trfQuotientStalkRealizationArrow l E D _ (e _) M.obj P q =
          trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q ≫
            (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((R v α).hom.app P.obj))) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α β : D.k ≃+* D.k),
        HEq ((R v α).hom ≫
            (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom)
          (R v (α.trans β)).hom) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k),
        HEq (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) α.symm).hom
          (R v α).inv) ∧
      (∀ v : Spec (.of D.k) ⟶ T,
        HEq (R v (RingEquiv.refl D.k)).hom (𝟙 (trfQuotientStalkTower l E v))) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α β : D.k ≃+* D.k),
        HEq ((r v α).hom ≫
            (r (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom)
          (r v (α.trans β)).hom) ∧
      (∀ v : Spec (.of D.k) ⟶ T,
        HEq (r v (RingEquiv.refl D.k)).hom
          (𝟙 ((sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D v))) := by
  classical
  have hreal (v : Spec (.of D.k) ⟶ T) :=
    trfBoundedQuotientStalkRealization l E D hl T v
  choose γ δ e hnorm htrunc hreal hnat using hreal
  have he : ∀ (v : Spec (.of D.k) ⟶ T) (M : sfIntegralConstructibleCategory l E T)
      (P : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
      IsIso (trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q) := by
    intro v M P q
    obtain ⟨ε, hε⟩ := (hreal v M.obj M.property P q).2.2.2
    rw [← hε]
    infer_instance
  obtain ⟨R, hfinite, hgerm, hcone, hbounded, hcomp, hinv, hid⟩ :=
    trfStrictQuotientStalkReindexing l E D hl T
  have hr (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k) :=
    trfQuotientStalkNaturalDescent l E D hl T e he hnat v
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) (R v α)
  choose r hr using hr
  refine ⟨R, e, r, ?_, hfinite, hgerm, hcone, hbounded, he, hr, hcomp, hinv, hid, ?_, ?_⟩
  · intro v
    exact ⟨γ v, δ v, hnorm v⟩
  · intro v α β
    have hpoint : Spec.map (CommRingCat.ofHom β.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) =
        Spec.map (CommRingCat.ofHom (α.trans β).toRingHom) ≫ v := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    refine trfNormalizedMapHEq l E D T e he v _ _ hpoint
      ((R v α).hom ≫ (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom)
      (R v (α.trans β)).hom (hcomp v α β)
      ((r v α).hom ≫ (r (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom)
      (r v (α.trans β)).hom ?_ (hr v (α.trans β))
    intro M P q
    let A (u : Spec (.of D.k) ⟶ T) :=
      trfQuotientStalkRealizationArrow l E D u (e u) M.obj P q
    let Q := trfIntegralModuleQ l E
    let a := (R v α).hom.app P.obj
    let b := (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom.app P.obj
    change ((r v α).hom.app M ≫
      (r (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom.app M) ≫ A _ =
        A v ≫ Q.map (integralOperationsRoosMap (a ≫ b))
    calc
      _ = (r v α).hom.app M ≫
          ((r (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom.app M ≫ A _) :=
        Category.assoc _ _ _
      _ = (r v α).hom.app M ≫
          (A (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) ≫
            Q.map (integralOperationsRoosMap b)) :=
        congrArg (fun f ↦ (r v α).hom.app M ≫ f)
          (hr (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β M P q)
      _ = ((r v α).hom.app M ≫
          A (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)) ≫
            Q.map (integralOperationsRoosMap b) := (Category.assoc _ _ _).symm
      _ = (A v ≫ Q.map (integralOperationsRoosMap a)) ≫
          Q.map (integralOperationsRoosMap b) :=
        congrArg (fun f ↦ f ≫ Q.map (integralOperationsRoosMap b)) (hr v α M P q)
      _ = A v ≫ (Q.map (integralOperationsRoosMap a) ≫
          Q.map (integralOperationsRoosMap b)) := Category.assoc _ _ _
      _ = A v ≫ Q.map (integralOperationsRoosMap (a ≫ b)) :=
        congrArg (fun f ↦ A v ≫ f)
          ((congrArg Q.map (integralOperationsRoosMap_comp a b)).trans
            (Q.map_comp (integralOperationsRoosMap a) (integralOperationsRoosMap b))).symm
  · intro v
    have hpoint : Spec.map (CommRingCat.ofHom (RingEquiv.refl D.k).toRingHom) ≫ v = v := by
      change Spec.map (𝟙 (CommRingCat.of D.k)) ≫ v = v
      rw [Spec.map_id, Category.id_comp]
    refine trfNormalizedMapHEq l E D T e he v _ v hpoint
      (R v (RingEquiv.refl D.k)).hom (𝟙 _) (hid v)
      (r v (RingEquiv.refl D.k)).hom (𝟙 _) (hr v (RingEquiv.refl D.k)) ?_
    intro M P q
    simp only [NatTrans.id_app, Category.id_comp, integralOperationsRoosMap_id]
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q ≫ f)
        ((trfIntegralModuleQ l E).map_id _).symm)

end WeilConjectures
