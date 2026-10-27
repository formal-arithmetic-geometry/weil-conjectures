/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Paper.TraceBoundedQuotientStalkRealization

/-!
# Strict integral quotient-stalk reindexing

Source: Stacks Tag 05V1 and blueprint Euler-product proof, Local powers (b).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Reindexing germs gives a strict quotient-stalk tower isomorphism, with the
specified finite coefficient maps, both cone coordinates, truncation squares,
and the opposite action, inverse, and unit laws.

Source: Stacks Project, sites.tex, Tag 05V1; blueprint Euler-product proof,
Local powers (b), parent steps 1--4 and 8
(blueprint: lem-trf-strict-quotient-stalk-reindexing).

Proof: precompose every pointed lift by Spec(alpha), keeping sections and
neighbourhood arrows fixed. This is an equivalence of pointed neighbourhood
categories. The colimit universal property gives additive maps, and common
refinements show that the constant integral scalar germ is respected. Its inverse
uses alpha inverse. In each finite quotient this is the published finite
coefficient reparametrization, since both maps agree on every coprojection.
Naturality for differentials, reduction maps, and maps of complexes gives a
natural isomorphism of strict towers. The product maps commute with 1-s by
projection to every level. Applying the diagonal map on the two cocone summands
gives both displayed projection equations, including the shifted coordinate.
Whisker the integral stalk reparametrization with the functorial upper and lower
truncations; naturality for their boundary arrows gives the two squares for all
p and q, including p=q and p>q. Finally successive reindexings send a pointed
lift u to Spec(beta) followed by Spec(alpha) followed by u. Contravariance of
Spec identifies this with alpha.trans beta. Equality on coprojections gives the
composition, inverse, and identity laws, first in each degree and then for the
whole natural tower map. No commutativity of alpha and beta is used. -/
theorem trfStrictQuotientStalkReindexing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)] :
    ∃ (R : ∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k),
        trfQuotientStalkTower l E v ≅ trfQuotientStalkTower l E
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)),
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
      (∀ (v : Spec (.of D.k) ⟶ T) (α β : D.k ≃+* D.k),
        HEq ((R v α).hom ≫
            (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) β).hom)
          (R v (α.trans β)).hom) ∧
      (∀ (v : Spec (.of D.k) ⟶ T) (α : D.k ≃+* D.k),
        HEq (R (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v) α.symm).hom
          (R v α).inv) ∧
      (∀ v : Spec (.of D.k) ⟶ T,
        HEq (R v (RingEquiv.refl D.k)).hom (𝟙 (trfQuotientStalkTower l E v))) := by sorry

end WeilConjectures
