module

public import Sheaf.SixFunctors.FiniteScalarMateData
public import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus

/-! # Finite scalar mates as coherent systems and integral natural maps

Source: current blueprint coefficient-extension exceptional-image proof,
sec-six-functors-basics/sk-prop-scalar-six; Stacks 0941, 079P and 07A6
(blueprint: lem-coef-finite-scalar-mate-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

variable {l E L i D hl f c}

/-- Normalized comparison data and equations, all supplied in the theorem's conclusion.
The finite comparison is the published proper/open arrow. The coherent arrow is
already defined as a mate, before any of the equations below are asserted.
Source: every comparison clause of the node
(blueprint: lem-coef-finite-scalar-mate-realization). -/
structure Realization (a : Context l E L i D hl f c) (h : IsIso a.alpha)
    (e : ℕ) (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) where
  finiteX : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    FiniteExceptional.domain l L X (retainedIndex e n)
      ((finiteTensor l E L i e he hp X n).obj K.obj)
  finiteY : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E Y n).FullSubcategory),
    FiniteExceptional.domain l L Y (retainedIndex e n)
      ((finiteTensor l E L i e he hp Y n).obj K.obj)
  evalX : ∀ n : ℕ,
    a.TX ⋙ FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E X n ⋙
        finiteTensorRestricted l E L i e he hp X n (finiteX n)
  evalY : ∀ n : ℕ,
    a.TY ⋙ FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E Y n ⋙
        finiteTensorRestricted l E L i e he hp Y n (finiteY n)
  transitionX : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    (FiniteExceptional.reduction l L X (retainedIndex_mono e hnm)).map
        (((evalX m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp X hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E X m).obj N).obj ≫
      (finiteTensor l E L i e he hp X n).map
        (FiniteAdjunctionDiagram.transition l E X a.r.quotientRestrictionX hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L X a.s.quotientRestrictionX
      (retainedIndex_mono e hnm) (a.TX.obj N)).hom ≫ ((evalX n).hom.app N).hom
  transitionY : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    (FiniteExceptional.reduction l L Y (retainedIndex_mono e hnm)).map
        (((evalY m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp Y hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E Y m).obj N).obj ≫
      (finiteTensor l E L i e he hp Y n).map
        (FiniteAdjunctionDiagram.transition l E Y a.r.quotientRestrictionY hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L Y a.s.quotientRestrictionY
      (retainedIndex_mono e hnm) (a.TY.obj N)).hom ≫ ((evalY n).hom.app N).hom
  alphaFinite : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    IsIso (finiteAlpha l E L i D hl f c e he hp n K)
  finiteSupport : ∀ (n : ℕ) (K : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    ((FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n)).map
        (a.alpha.app K) ≫ (a.s.supportEvaluation (retainedIndex e n)).hom.app (a.TX.obj K) ≫
      (FiniteExceptional.F l L D hl f c (retainedIndex e n)).map ((evalX n).hom.app K)).hom =
    ((evalY n).hom.app (a.r.F.obj K) ≫
      (finiteTensorRestricted l E L i e he hp Y n (finiteY n)).map
        ((a.r.supportEvaluation n).hom.app K)).hom ≫
      finiteAlpha l E L i D hl f c e he hp n
        ((FiniteAdjunctionDiagram.evaluation l E X n).obj K)
  integralAlpha :
    sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⋙
      a.TIY ≅ a.TIX ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c L
  integralAlpha_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (integralAlpha.hom.app K).hom = a.integralAlphaComponent K
  source : a.RY ⋙ a.r.G ⋙ a.TX ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.GR ⋙ a.TIX ⋙ (sfIntegralConstructible l L X).ι
  target : a.RY ⋙ a.TY ⋙ a.s.G ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.TIY ⋙ a.GS ⋙ (sfIntegralConstructible l L X).ι
  integralAdjunctionR : SemilinearSections.AdjunctionEvaluation
    a.RX a.RY a.adjR a.r.adjunction
  integralAdjunctionS : SemilinearSections.AdjunctionEvaluation
    a.SXred a.SYred a.adjS a.s.adjunction
  reconstructionR : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (a.SX.adjunction.unit.app K.obj)
  reconstructionS : ∀ K : sfIntegralConstructibleCategory l L X,
    IsIso (a.UX.adjunction.unit.app K.obj)
  reconstructionY : ∀ K : sfIntegralConstructibleCategory l E Y,
    IsIso (a.SY.adjunction.unit.app K.obj)
  support_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (coefficientSequenceLimit l E Y).map
        ((integralAdjunctionR.left.hom.app K).hom) ≫ a.supportR.iso.hom.app K =
      (@asIso _ _ _ _ (a.SY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj K).obj)
        (reconstructionY _)).inv
  reconstructionSY : ∀ K : sfIntegralConstructibleCategory l L Y,
    IsIso (a.UY.adjunction.unit.app K.obj)
  supportS_normalization : ∀ K : sfIntegralConstructibleCategory l L X,
    (coefficientSequenceLimit l L Y).map
        ((integralAdjunctionS.left.hom.app K).hom) ≫ a.supportS.iso.hom.app K =
      (@asIso _ _ _ _ (a.UY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c L).obj K).obj)
        (reconstructionSY _)).inv
  scalarReduction : a.TIY ⋙ a.SYred ≅ a.RY ⋙ a.TY
  scalarReduction_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    (scalarReduction.hom.app M).hom =
      (integralComparisonScalarCounit l E L i Y a.SY a.UY
        ((FrobeniusExchange.models l L).roos Y) a.scalarModelY).app M.obj
  cofinalX : retainedLimit l L X e ≅ coefficientSequenceLimit l L X
  cofinalX_normalization : ∀ C : CochainComplex (coefficientSequenceModules l L X) ℤ,
    ∃ ρ : integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⟶
      integralOperationsRoos (PurCompactSupport.retainedTower e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor),
      PurCompactSupport.IsCofinalRoosMap e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ρ ∧
      cofinalX.inv.app (DerivedCategory.Q.obj C) ≫ retainedRoosComparison l L X e C =
        fullRoosComparison l L X C ≫ DerivedCategory.Q.map ρ
  source_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    source.hom.app M = cofinalX.hom.app
        ((a.TX.obj (a.r.G.obj (a.RY.obj M))).obj) ≫
      (coefficientSequenceLimit l L X).map
        ((integralComparisonDerivedSequenceScalar l E L i X).map
          ((integralAdjunctionR.right.inv.app M).hom)) ≫
      a.scalarModelX.realization.inv.app (a.GR.obj M).obj
  target_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    target.hom.app M = cofinalX.hom.app
        ((a.s.G.obj (a.TY.obj (a.RY.obj M))).obj) ≫
      (coefficientSequenceLimit l L X).map
        ((a.s.G.map (scalarReduction.inv.app M)).hom) ≫
      (coefficientSequenceLimit l L X).map
        ((integralAdjunctionS.right.inv.app (a.TIY.obj M)).hom) ≫
      (@asIso _ _ _ _ (a.UX.adjunction.unit.app (a.GS.obj (a.TIY.obj M)).obj)
        (reconstructionS (a.GS.obj (a.TIY.obj M)))).inv
  coherent_transpose : ∀ N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory,
    a.s.F.map ((a.beta h).app N) ≫ a.s.adjunction.counit.app (a.TY.obj N) =
      (@asIso _ _ _ _ a.alpha h).inv.app (a.r.G.obj N) ≫ a.TY.map (a.r.adjunction.counit.app N)
  finite_transpose : ∀ (n : ℕ) (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    ((FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n)).map
        ((a.beta h).app N) ≫
      (a.s.exceptionalEvaluation (retainedIndex e n)).hom.app (a.TY.obj N) ≫
      (FiniteExceptional.G l L D hl f c (retainedIndex e n)).map
        ((evalY n).hom.app N)).hom =
    ((evalX n).hom.app (a.r.G.obj N)).hom ≫
    (((FiniteExceptional.adjunction l L D hl f c (retainedIndex e n)).homEquiv _ _)
      (ObjectProperty.homMk (Y :=
          (finiteTensorRestricted l E L i e he hp Y n (finiteY n)).obj
            ((FiniteAdjunctionDiagram.evaluation l E Y n).obj N))
        (((FiniteExceptional.F l L D hl f c (retainedIndex e n)).map
          ((finiteTensorRestricted l E L i e he hp X n (finiteX n)).map
            ((a.r.exceptionalEvaluation n).hom.app N))).hom ≫
        (@asIso _ _ _ _
          (finiteAlpha l E L i D hl f c e he hp n
            ((FiniteAdjunctionDiagram.evaluation l E Y n ⋙
              FiniteExceptional.G l E D hl f c n).obj N))
          (alphaFinite n _)).inv ≫
          (finiteTensor l E L i e he hp Y n).map
            ((FiniteExceptional.adjunction l E D hl f c n).counit.app
              ((FiniteAdjunctionDiagram.evaluation l E Y n).obj N)).hom))).hom
  integral_transpose : ∀ M : sfIntegralConstructibleCategory l E Y,
    source.inv.app M ≫ (retainedLimit l L X e).map
        (((a.beta h).app (a.RY.obj M)).hom) ≫ target.hom.app M =
      (((a.adjS.homEquiv _ _)
        (integralAlpha.inv.app (a.GR.obj M) ≫
          a.TIY.map (a.adjR.counit.app M))).hom)


variable (l E L i D hl f c)

/-- Finite scalar exceptional mates are one coherent transpose, whose total limit
is the specified integral transpose. The realization data, finite-Tor preservation,
comparison isomorphisms and all their normalization equations are conclusions.

Source: current blueprint coefficient-extension exceptional-image proof;
Stacks 0941, 079P, 07A6 (blueprint: lem-coef-finite-scalar-mate-realization).

Proof: choose simultaneous coefficient-system K-flat and K-injective models.
Finite extension of valuation rings is finite free. On a single integral basis,
tensor is a finite sum, so the proper projection and open-extension tensor map
are invertible, independent of the basis. This constructs alpha on entire systems.
Restrict to normalized finite-Tor systems. At retained exponent e(n+1), tensor
reassociation with the normalized lower transition identifies its evaluation with
tensor A_(n+1) to B_(n+1). The finite exceptional quotient cocycles and finite-free
squares identify the evaluated units and counits with their specified finite maps.
Form beta by transposing alpha inverse followed by the scalar-extended system
counit. The system transpose identity holds before taking any finite evaluation.
Evaluating the normalized adjunction gives exactly finite_transpose.
For integral M, its reduction and exceptional reduction have common finite Tor
intervals by residue Tor and preservation. The reduction/total-limit adjunction,
the finite-free completed comparison and the cofinal e(n+1) subsequence give
source and target with the displayed unit/counit normalizations. They identify
alpha with integralAlpha. Apply total limit to the system transpose identity;
transport its counit using the normalized reconstruction adjunction. Its adjunct
is integralAlpha inverse followed by the scalar image of the integral counit.
Injectivity of the integral adjunction bijection gives integral_transpose, as an
equality of natural maps. No faithfulness of finite projections is used. The same
constructions include identity extensions, identity morphisms, zero inputs and
empty schemes. -/
theorem finiteScalarMateRealization (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) :
    ∃ (a : Context l E L i D hl f c) (h : IsIso a.alpha),
      Nonempty (Realization a h e he hp) := by
  sorry

end WeilConjectures.FiniteScalarMate
