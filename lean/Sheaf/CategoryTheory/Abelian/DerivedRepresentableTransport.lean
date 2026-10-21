/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# Derived transport of represented functors

Source: Stacks Project, derived.tex, Tags 05TH, 05TI, 070I and 015F;
representability and coherence calculation in the DAG
(blueprint: lem-pur-derived-representable-transport).

The comparisons below use the left Kan extension unit, the exact termwise derived
functor, and the roof-normalized comparison of `exists_rhom_hom_derived_roof`.
-/

@[expose] public section

universe u₁ u₂ u₃ v w₁ w₂ w₃ wAb

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{wAb} AddCommGrpCat.{v}]

/-- The termwise transformation followed by the target derived unit and exact
localization comparison. Source: Stacks Tags 05TI and 015F
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportUnit
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus) :=
  whiskerRight (NatTrans.mapHomotopyCategoryPlus tau) DerivedCategory.Plus.Qh ≫
    whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ S'))).inv
      DerivedCategory.Plus.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft L.mapHomotopyCategoryPlus S'.rightDerivedFunctorPlusUnit ≫
    (associator _ _ _).inv ≫
    whiskerRight L.mapDerivedCategoryPlusFactorsh.inv S'.rightDerivedFunctorPlus ≫
    (associator _ _ _).hom

/-- The canonical comparison is the Kan factorization of `representableTransportUnit`.
Source: Stacks Tag 05TI (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportComparison
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
  S.rightDerivedFunctorPlus.rightDerivedDesc S.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A) _ (representableTransportUnit L S S' tau)

/-- The roof-normalized RHom equivalence supplied by the recorded roof theorem.
Its normalization determines it on every injective representative.
Source: Stacks Tag 070I (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportRoof (P : A) (X : DerivedCategory.Plus A) (a : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
        ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.obj X) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :=
  Classical.choose (exists_rhom_hom_derived_roof P) X a

/-- Derive the inverse representing isomorphism, then apply the roof equivalence.
Source: Stacks Tags 05TI and 070I
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representedTransportHomEquiv
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S) (X : DerivedCategory.Plus A) (a : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
        (S.rightDerivedFunctorPlus.obj X) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :=
  ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).mapIso
    ((rightDerivedFunctorPlusNatIso θ.symm).app X)).addCommGroupIsoToAddEquiv.trans
      (representableTransportRoof P X a)

/-- Apply the exact derived functor to a shifted morphism and precompose with `d⁻¹`.
The displayed single and shift isomorphisms are the termwise ones.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportHom
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P : A} {P' : B} (d : L.obj P ≅ P') (X : DerivedCategory.Plus A) (a : ℤ)
    (f : (DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :
    (DerivedCategory.singleFunctor B 0).obj P' ⟶
      (L.mapDerivedCategoryPlus.obj X).obj⟦a⟧ :=
  (DerivedCategory.singleFunctor B 0).map d.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫ L.mapDerivedCategory.map f ≫
    (L.mapDerivedCategory.commShiftIso a).hom.app X.obj

/-- The inverse of a localized resolution, transported through the fully faithful
bounded below inclusion and the canonical quotient comparisons.
Source: Stacks Tag 05RU (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportResolutionInverse
    {F I : CochainComplex.Plus A} (e : F ⟶ I) [QuasiIso e.hom] :
    (DerivedCategory.Plus.Q (C := A)).obj I ⟶ (DerivedCategory.Plus.Q (C := A)).obj F :=
  (DerivedCategory.Plus.ι (C := A)).preimage
    ((DerivedCategory.quotientCompQhIso A).inv.app I.obj ≫
      CategoryTheory.inv (DerivedCategory.Q.map e.hom) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app F.obj)

/-- The canonical map from the termwise injective model to the derived value at the
original complex. Its inverse-resolution arrow is taken after localization.
Source: Stacks Tags 05TH and 05TI
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportModel
    (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    {F I : CochainComplex.Plus A} (e : F ⟶ I) [QuasiIso e.hom] :
    (DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})).obj
        (S.mapCochainComplexPlus.obj I) ⟶
      S.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.Q (C := A)).obj F) :=
  S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
    S.rightDerivedFunctorPlus.map (representableTransportResolutionInverse e)

/-- The exact termwise identification on a bounded below complex.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportExactIso
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : CochainComplex.Plus A) :
    L.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.Q (C := A)).obj F) ≅
      (DerivedCategory.Plus.Q (C := B)).obj (L.mapCochainComplexPlus.obj F) :=
  L.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient A).obj F)

/-- The chain map in the injective model: first the termwise transformation, then
apply the target functor to the comparison of resolutions.
Source: Stacks Tags 05TH and 05TI
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportChainMap
    (L : A ⥤ B) [L.Additive]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S')
    (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj) :
    S.mapCochainComplexPlus.obj I ⟶ S'.mapCochainComplexPlus.obj J :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex tau (ComplexShape.up ℤ)).app I.obj ≫
      (mapHomologicalComplexCompIso (Iso.refl (L ⋙ S')) (ComplexShape.up ℤ)).inv.app
        I.obj ≫
      (S'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)

/-- The canonical comparison, its injective model and its represented Hom formula.
Source: Stacks Tags 05TH, 05TI, 070I and 015F, with the representability calculation
(blueprint: lem-pur-derived-representable-transport).

Proof: The left Kan extension property factors the termwise transformation followed
by the target unit, and makes that factorization unique. Exactness of L preserves
quasi-isomorphisms. A bounded below complex of injectives J is K-injective, so the
localized arrow Q(e') Q(Le)⁻¹ lifts to a chain map t, unique up to homotopy, and
t Le is homotopic to e'. Naturality of the derived comparison at e, its factorization
at I and naturality of the target unit at t give the displayed model formula; only
units at I and J are inverted, and LI need not be injective. The representing square
and naturality of the target representing isomorphism give the cocycle formula.
Derive the inverse representing isomorphisms and apply the roof-normalized RHom
comparison. The roof is Q(e')⁻¹ Q(t) Q(Lf) d⁻¹. Cancel Q(t) Q(Le) = Q(e') and use
the termwise shift comparison to obtain the asserted exact-functor action on Hom.
Every class has a cocycle representative. A boundary has zero localized single
map, and applying additive functors to homotopies gives equal derived maps.
The canonical comparison and the roof normalization therefore remove all choices. -/
theorem derived_representable_transport
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (P : A) (P' : B) (d : L.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] [PreservesFiniteLimits S] [PreservesFiniteLimits S']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S') (tau : S ⟶ L ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f)) :
    (S.rightDerivedFunctorPlusUnit ≫
        whiskerLeft DerivedCategory.Plus.Qh (representableTransportComparison L S S' tau) =
      representableTransportUnit L S S' tau) ∧
    (∀ b : S.rightDerivedFunctorPlus ⟶
        L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus,
      S.rightDerivedFunctorPlusUnit ≫ whiskerLeft DerivedCategory.Plus.Qh b =
        representableTransportUnit L S S' tau →
      b = representableTransportComparison L S S' tau) ∧
    (∀ (F I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
        (e : F ⟶ I) [QuasiIso e.hom]
        (e' : L.mapCochainComplexPlus.obj F ⟶ J) [QuasiIso e'.hom]
        (_hi : ∀ k : ℤ, Injective (I.obj.X k))
        (_hj : ∀ k : ℤ, Injective (J.obj.X k)),
      ∃ t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
        Nonempty (Homotopy
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t) e'.hom) ∧
        (∀ t' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
          Nonempty (Homotopy
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t') e'.hom) →
          Nonempty (Homotopy t t')) ∧
        (representableTransportModel S e ≫
            (representableTransportComparison L S S' tau).app
              ((DerivedCategory.Plus.Q (C := A)).obj F) =
          DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) ≫
            representableTransportModel S' e' ≫
            S'.rightDerivedFunctorPlus.map (representableTransportExactIso L F).inv) ∧
        (∀ (a : ℤ) (f : P ⟶ I.obj.X a) (_hf : f ≫ I.obj.d a (a + 1) = 0),
          (d.inv ≫ L.map f ≫ t.f a) ≫ J.obj.d a (a + 1) = 0 ∧
          S'.map (t.f a) (tau.app (I.obj.X a) (θ.hom.app (I.obj.X a) f)) =
            θ'.hom.app (J.obj.X a) (d.inv ≫ L.map f ≫ t.f a))) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P' S' θ' (L.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison L S S' tau).app X) α) =
        representableTransportHom L d X a (representedTransportHomEquiv P S θ X a α)) := by
  sorry

/-- Boundaries vanish and homotopic comparisons give the same derived model map.
Together with the resolution-uniform formula in `derived_representable_transport`,
this expresses independence of resolutions, comparison maps and cocycle representatives.
Source: Stacks Tags 05RU and 070I
(blueprint: lem-pur-derived-representable-transport).

Proof: A boundary f = g d has null-homotopic single-complex map: the only nonzero
homotopy component is (-1)^a g, which compensates for the shifted differential.
Localization through the homotopy category kills this map. Applying S' to a
homotopy and precomposing with the termwise transformation gives a homotopy of
the model chain maps, so their localized maps coincide. The model formula is
equal to the single canonical comparison for every resolution, proving the
remaining independence assertions. -/
theorem derived_representable_transport_independence
    (L : A ⥤ B) [L.Additive]
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    (∀ (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
        (hf : f ≫ I.obj.d a (a + 1) = 0),
      (∃ g : P ⟶ I.obj.X (a - 1), g ≫ I.obj.d (a - 1) a = f) →
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q = 0) ∧
    (∀ (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
        (t t' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj),
      Nonempty (Homotopy t t') →
      DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) =
        DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t')) := by
  sorry

variable {C : Type u₃} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₃} C]

/-- Composition of canonical derived comparisons and of the represented Hom formula.
The total representing isomorphism is `L₂(d)` followed by `d₂`; the total underived
transformation is `tau` followed by `L(tau₂)`.
Source: Stacks Tags 05TI and 015F; Kan uniqueness and inverse-composition calculation
(blueprint: lem-pur-derived-representable-transport).

Proof: Compose the defining factorization equations. The composite factors exactly
the termwise total transformation followed by the final derived unit. Uniqueness
of the source Kan factorization identifies it with the total comparison under
the canonical exact-functor composition isomorphism. Apply the two representing
squares successively; the inverse of L₂(d) d₂ is d₂⁻¹ L₂(d⁻¹).
Apply the Hom formula twice. Functoriality, the single-complex identifications and
the termwise shift comparisons identify this with the Hom formula for the total
datum. No functor is required to preserve injective objects. -/
theorem derived_representable_transport_comp
    (L : A ⥤ B) (L₂ : B ⥤ C) [L.Additive] [L₂.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (P : A) (P' : B) (P'' : C) (d : L.obj P ≅ P') (d₂ : L₂.obj P' ≅ P'')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    (S'' : C ⥤ AddCommGrpCat.{v}) [S.Additive] [S'.Additive] [S''.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteLimits S'] [PreservesFiniteLimits S'']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S')
    (θ'' : preadditiveCoyoneda.obj (op P'') ≅ S'')
    (tau : S ⟶ L ⋙ S') (tau₂ : S' ⟶ L₂ ⋙ S'')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (h₂ : ∀ (M : B) (f : P' ⟶ M),
      θ''.hom.app (L₂.obj M) (d₂.inv ≫ L₂.map f) = tau₂.app M (θ'.hom.app M f)) :
    (∀ (M : A) (f : P ⟶ M),
      θ''.hom.app ((L ⋙ L₂).obj M)
          ((L₂.mapIso d ≪≫ d₂).inv ≫ (L ⋙ L₂).map f) =
        (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv).app M
          (θ.hom.app M f)) ∧
    (representableTransportComparison (L ⋙ L₂) S S''
          (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv) ≫
        whiskerRight (mapDerivedCategoryPlusCompIso L L₂).hom S''.rightDerivedFunctorPlus =
      representableTransportComparison L S S' tau ≫
        whiskerLeft L.mapDerivedCategoryPlus (representableTransportComparison L₂ S' S'' tau₂) ≫
        (associator L.mapDerivedCategoryPlus L₂.mapDerivedCategoryPlus
          S''.rightDerivedFunctorPlus).inv) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P'' S'' θ'' ((L ⋙ L₂).mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison (L ⋙ L₂) S S''
              (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv)).app X) α) ≫
        ((mapDerivedCategoryCompIso L L₂).hom.app X.obj)⟦a⟧' =
      representableTransportHom L₂ d₂ (L.mapDerivedCategoryPlus.obj X) a
        (representableTransportHom L d X a (representedTransportHomEquiv P S θ X a α))) := by
  sorry

/-- Coherent identifications of exact functors preserve the canonical comparison and
its represented Hom formula. This applies in particular to identified composites.
Source: Stacks Tags 05RU, 05TI and 015F; naturality and Kan uniqueness
(blueprint: lem-pur-derived-representable-transport).

Proof: Localize the termwise natural isomorphism zeta. Naturality of the target
unit shows that postcomposing the first comparison by RS'(D zeta) factors the
second underived transformation. Kan uniqueness identifies it with the second
comparison. Naturality of D zeta at the morphism from P[0] to X[a], compatibility
with the termwise shifts, and dT zeta_P = d identify the two Hom formulas.
This also covers arbitrary coherently identified composites, by the composition
clause and the canonical localized composition identifications. -/
theorem derived_representable_transport_coherence
    (L T : A ⥤ B) [L.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (zeta : L ≅ T) (P : A) (P' : B) (d : L.obj P ≅ P') (dT : T.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] [PreservesFiniteLimits S] [PreservesFiniteLimits S']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S')
    (tau : S ⟶ L ⋙ S') (tauT : S ⟶ T ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (hT : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (T.obj M) (dT.inv ≫ T.map f) = tauT.app M (θ.hom.app M f))
    (hd : zeta.hom.app P ≫ dT.hom = d.hom)
    (htau : tau ≫ whiskerRight zeta.hom S' = tauT) :
    (representableTransportComparison L S S' tau ≫
        whiskerRight (mapDerivedCategoryPlusNatIso zeta).hom S'.rightDerivedFunctorPlus =
      representableTransportComparison T S S' tauT) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P' S' θ' (L.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison L S S' tau).app X) α) ≫
        ((mapDerivedCategoryNatIso zeta).hom.app X.obj)⟦a⟧' =
      representedTransportHomEquiv P' S' θ' (T.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison T S S' tauT).app X) α)) := by
  sorry

end CategoryTheory.Functor
