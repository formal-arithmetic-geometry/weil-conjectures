/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTranspose
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations

/-!
# Finite-ring site transport, including exceptional base change

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (2)--(3), and the eleven-step
finite-ring transport refinement
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

The existing tensor-transport module supplies the canonical comparison, projection,
tensor and pullback constructions. The assertions below state their precise counit,
projection, tensor-transpose and base-change identities without unconditionally
asserting projection invertibility.
The pro-etale adjoints take values in the full localizing subcategories, with ambient Hom
sets. All coefficient categories are ordinary and uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- The bounded-below etale compact-support exchange viewed in the ambient categories.
Only the existing bounded-below inclusion comparisons are inserted.
Source: Stacks 0F7F; node base-change clause
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingEtaleExchangeMap (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (hM : DerivedCategory.TStructure.t.plus M) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingEtaleShriek B c).obj M) ⟶
      (finiteRingEtaleShriek B (c.ofIsPullback sq)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj M) :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).inv.app ⟨M, hM⟩) ≫
    DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (ULift.{u + 1} B) sq c).app ⟨M, hM⟩) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) (c.ofIsPullback sq)).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          g').mapDerivedCategoryPlus.obj ⟨M, hM⟩)

/-- The ambient pro-etale proper-mate/open exchange, using exact pullback coordinates.
The two inserted isomorphisms identify the derived pullbacks with termwise pullback.
Source: Stacks 0F7F, 0GL1; node base-change clause
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingProExchangeMap (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingProShriek B c).obj M) ⟶
      (finiteRingProShriek B (c.ofIsPullback sq)).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).inv.app _ ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq c).app M ≫
    (finiteRingProShriek B (c.ofIsPullback sq)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').hom.app M)

/-- Finite primary coefficients transport the unique counit-normalized adjoint comparison,
the canonical signed projection square, its tensor/counit transposes, and the specified
bounded-below compact-support exchange. The assertions use the published constructions
with every tensor, unit, pullback and projection fixed canonically. Projection invertibility
is only a
hypothesis of the separate dualizing-transpose clause.

Source: latest blueprint general-ring proof (2)--(3); node proof steps 1--11
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof: finite-Tor constructible generation and finite comparison identify the ordinary
etale category with the full pro-etale localizing closure (step 1). The unbounded proper
counit mate followed by the adjoint-normalized open comparison gives B and preserves the
closure (step 2). The Hom-chain and Yoneda give the unique adjoint isomorphism with its
counit equation (step 3); applying the inverse adjunction bijection gives transport of
every transpose (step 4). K-flat pure tensors preserve unitors and signed symmetry
(step 5). Paste the proper tensor/counit square with the open tensor square (steps 6--7).
Invert only the indicated projections and use the counit equation at the coefficient
unit to obtain the omega tensor-transpose identity (step 8). Apply the specified
proper/open exchange transport on bounded-below inputs (step 9). Transpose its inverse
followed by the pulled-back counit (step 10). Fully faithful inclusions restrict all
identities to bounded constructible finite-Tor inputs; naturality cancels a change of
etale origin (step 11). No orientation or exceptional-exchange invertibility is used. -/
theorem finiteRingSiteTensorTransposeWithBaseChange
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))] [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))] :
    ∃ (hX : ∀ M, finiteComparisonProEtaleClosure B eR X ((finiteRingSitePull B X).obj M))
      (hY : ∀ K, finiteComparisonProEtaleClosure B eR Y ((finiteRingSitePull B Y).obj K))
      (b : finiteRingEtaleShriek B c ⋙ finiteRingSitePull B Y ≅
        finiteRingSitePull B X ⋙ finiteRingProShriek B c),
      (∀ M, b.hom.app M = finiteComparisonCompactSupportMap B c.i c.g M) ∧
      (∀ (hs : ∀ N, finiteComparisonProEtaleClosure B eR X N →
          finiteComparisonProEtaleClosure B eR Y ((finiteRingProShriek B c).obj N))
        (R : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y ⥤
          Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
        (ae : finiteRingEtaleShriek B c ⊣ R)
        (G : (finiteComparisonProEtaleClosure B eR Y).FullSubcategory ⥤
          (finiteComparisonProEtaleClosure B eR X).FullSubcategory)
        (ap : finiteRingRestriction (finiteRingProShriek B c)
          (finiteComparisonProEtaleClosure B eR X)
          (finiteComparisonProEtaleClosure B eR Y) hs ⊣ G),
        ∃! rho : R ⋙ finiteRingImageLift (finiteRingSitePull B X)
            (finiteComparisonProEtaleClosure B eR X) hX ≅
          finiteRingImageLift (finiteRingSitePull B Y)
            (finiteComparisonProEtaleClosure B eR Y) hY ⋙ G,
          ∀ K, b.hom.app (R.obj K) ≫
            (finiteRingProShriek B c).map (rho.hom.app K).hom ≫
            (ap.counit.app ⟨(finiteRingSitePull B Y).obj K, hY K⟩).hom =
            (finiteRingSitePull B Y).map (ae.counit.app K)) ∧
      (∀ (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y),
        (finiteRingSitePull B Y).map
            (finiteRingEtalePF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c M K) ≫
          finiteComparisonCompactSupportMap B c.i c.g
            (M ⊗ (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              f).leftDerivedFunctor.obj K) ≫
          (finiteRingProShriek B c).map
            (finiteRingTensorPullbackComparison (finiteRingSitePull B X)
              (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor
              (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor
              (finiteRingSitePull B Y)
              (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) X)
              (finiteRingSitePullback (ModuleCat.{u + 1} (ULift.{u + 1} B)) f
                (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f)) M K).hom =
        (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) Y
          ((finiteRingEtaleShriek B c).obj M) K).hom ≫
          (finiteComparisonCompactSupportMap B c.i c.g M ⊗ₘ
            𝟙 ((finiteRingSitePull B Y).obj K)) ≫
          finiteRingProPF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c
            ((finiteRingSitePull B X).obj M) ((finiteRingSitePull B Y).obj K)) ∧
    ∀ {X' Y' : Scheme.{u}} [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
      [IsSeparated (X' ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
      [IsSeparated (Y' ↘ Spec (.of D.k))]
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
      [g'.IsOver (Spec (.of D.k))] [f'.IsOver (Spec (.of D.k))]
      [g.IsOver (Spec (.of D.k))]
      (sq : IsPullback g' f' f g)
      (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
      (hM : DerivedCategory.TStructure.t.plus M),
      (finiteRingSitePull B Y').map (finiteRingEtaleExchangeMap B sq c M hM) ≫
        finiteComparisonCompactSupportMap B (c.ofIsPullback sq).i
          (c.ofIsPullback sq).g
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            g').mapDerivedCategory.obj M) ≫
        (finiteRingProShriek B (c.ofIsPullback sq)).map
          ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) =
      (unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).inv.app
          ((finiteRingEtaleShriek B c).obj M) ≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.map
          (finiteComparisonCompactSupportMap B c.i c.g M) ≫
        finiteRingProExchangeMap B sq c ((finiteRingSitePull B X).obj M) := by
  sorry

/-- Every adjunction transpose is transported by the same counit equation.
The membership witnesses only restrict the actual compact-support functor and comparison
to the stated localizing closures; they supply no replacement maps.
Source: node proof step 4; Stacks 0B65
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof: apply the inverse pro-etale adjunction bijection. Expand it as compact support
followed by counit, move the comparison past the etale transpose by naturality, and
substitute the displayed counit normalization. The etale adjunction identity leaves u.
Injectivity of the bijection gives the asserted equality for every u. -/
theorem finiteRingSiteTransposeOfCounit
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hX : ∀ M, finiteComparisonProEtaleClosure B eR X ((finiteRingSitePull B X).obj M))
    (hY : ∀ K, finiteComparisonProEtaleClosure B eR Y ((finiteRingSitePull B Y).obj K))
    (hs : ∀ N, finiteComparisonProEtaleClosure B eR X N →
      finiteComparisonProEtaleClosure B eR Y ((finiteRingProShriek B c).obj N))
    (R : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (ae : finiteRingEtaleShriek B c ⊣ R)
    (G : (finiteComparisonProEtaleClosure B eR Y).FullSubcategory ⥤
      (finiteComparisonProEtaleClosure B eR X).FullSubcategory)
    (ap : finiteRingRestriction (finiteRingProShriek B c)
      (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y) hs ⊣ G)
    (b : finiteRingEtaleShriek B c ⋙ finiteRingSitePull B Y ≅
      finiteRingSitePull B X ⋙ finiteRingProShriek B c)
    (hb : ∀ M, b.hom.app M = finiteComparisonCompactSupportMap B c.i c.g M)
    (rho : R ⋙ finiteRingImageLift (finiteRingSitePull B X)
        (finiteComparisonProEtaleClosure B eR X) hX ≅
      finiteRingImageLift (finiteRingSitePull B Y)
        (finiteComparisonProEtaleClosure B eR Y) hY ⋙ G)
    (hc : ∀ K, finiteComparisonCompactSupportMap B c.i c.g (R.obj K) ≫
      (finiteRingProShriek B c).map (rho.hom.app K).hom ≫
        (ap.counit.app ⟨(finiteRingSitePull B Y).obj K, hY K⟩).hom =
      (finiteRingSitePull B Y).map (ae.counit.app K))
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y)
    (v : (finiteRingEtaleShriek B c).obj M ⟶ K) :
    (finiteRingSitePull B X).map (ae.homEquiv M K v) ≫ (rho.hom.app K).hom =
      (ap.homEquiv ⟨(finiteRingSitePull B X).obj M, hX M⟩
        ⟨(finiteRingSitePull B Y).obj K, hY K⟩
        (ObjectProperty.homMk (b.inv.app M ≫ (finiteRingSitePull B Y).map v))).hom := by
  sorry

/-- The counit-defined exceptional exchange is preserved by the unique adjoint comparisons.
The isomorphisms exE and exP retain the actual compact-support exchange as their hom;
only these compact-support exchanges are inverted, never the exceptional exchange.
Source: latest general-ring proof (2)--(3), node proof steps 9--11; Stacks 0B65, 0F7F
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof: apply the inverse target adjunction bijection. Naturality of the pro-etale
exchange moves the old adjoint comparison through its inverse. The compact-support
exchange square then replaces that inverse and the pulled-back B by comparison of
the etale inverse exchange. The old counit equation replaces the remaining pulled-back
pro-etale counit. The target counit equation and injectivity of its Hom equivalence
give the displayed identity. Full subcategory inclusions retain precisely ambient
maps, so this also gives the constructible restrictions. Naturality in an isomorphism
of etale origins cancels that isomorphism, including for section fibres. -/
theorem finiteRingExceptionalExchangeTransport
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hX : ∀ M, finiteComparisonProEtaleClosure B eR X ((finiteRingSitePull B X).obj M))
    (hY : ∀ K, finiteComparisonProEtaleClosure B eR Y ((finiteRingSitePull B Y).obj K))
    (hs : ∀ N, finiteComparisonProEtaleClosure B eR X N →
      finiteComparisonProEtaleClosure B eR Y ((finiteRingProShriek B c).obj N))
    (R : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (ae : finiteRingEtaleShriek B c ⊣ R)
    (G : (finiteComparisonProEtaleClosure B eR Y).FullSubcategory ⥤
      (finiteComparisonProEtaleClosure B eR X).FullSubcategory)
    (ap : finiteRingRestriction (finiteRingProShriek B c)
      (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y) hs ⊣ G)
    (b : finiteRingEtaleShriek B c ⋙ finiteRingSitePull B Y ≅
      finiteRingSitePull B X ⋙ finiteRingProShriek B c)
    (hb : ∀ M, b.hom.app M = finiteComparisonCompactSupportMap B c.i c.g M)
    (rho : R ⋙ finiteRingImageLift (finiteRingSitePull B X)
        (finiteComparisonProEtaleClosure B eR X) hX ≅
      finiteRingImageLift (finiteRingSitePull B Y)
        (finiteComparisonProEtaleClosure B eR Y) hY ⋙ G)
    {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (hX' : ∀ M, finiteComparisonProEtaleClosure B eR X' ((finiteRingSitePull B X').obj M))
    (hY' : ∀ K, finiteComparisonProEtaleClosure B eR Y' ((finiteRingSitePull B Y').obj K))
    (hs' : ∀ N, finiteComparisonProEtaleClosure B eR X' N →
      finiteComparisonProEtaleClosure B eR Y'
        ((finiteRingProShriek B (c.ofIsPullback sq)).obj N))
    (R' : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y' ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1} B) X')
    (ae' : finiteRingEtaleShriek B (c.ofIsPullback sq) ⊣ R')
    (G' : (finiteComparisonProEtaleClosure B eR Y').FullSubcategory ⥤
      (finiteComparisonProEtaleClosure B eR X').FullSubcategory)
    (ap' : finiteRingRestriction (finiteRingProShriek B (c.ofIsPullback sq))
      (finiteComparisonProEtaleClosure B eR X') (finiteComparisonProEtaleClosure B eR Y')
        hs' ⊣ G')
    (rho' : R' ⋙ finiteRingImageLift (finiteRingSitePull B X')
        (finiteComparisonProEtaleClosure B eR X') hX' ≅
      finiteRingImageLift (finiteRingSitePull B Y')
        (finiteComparisonProEtaleClosure B eR Y') hY' ⋙ G')
    (hc : ∀ K, finiteComparisonCompactSupportMap B c.i c.g (R.obj K) ≫
      (finiteRingProShriek B c).map (rho.hom.app K).hom ≫
        (ap.counit.app ⟨(finiteRingSitePull B Y).obj K, hY K⟩).hom =
      (finiteRingSitePull B Y).map (ae.counit.app K))
    (hc' : ∀ K, finiteComparisonCompactSupportMap B (c.ofIsPullback sq).i
        (c.ofIsPullback sq).g (R'.obj K) ≫
      (finiteRingProShriek B (c.ofIsPullback sq)).map (rho'.hom.app K).hom ≫
        (ap'.counit.app ⟨(finiteRingSitePull B Y').obj K, hY' K⟩).hom =
      (finiteRingSitePull B Y').map (ae'.counit.app K))
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y)
    (hK : Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) Y K)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) a b K)
    (hRK : DerivedCategory.TStructure.t.plus (R.obj K))
    (hR'K : DerivedCategory.TStructure.t.plus
      (R'.obj ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
        g).mapDerivedCategory.obj K)))
    (hJ : finiteComparisonProEtaleClosure B eR X'
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj
        (G.obj ⟨(finiteRingSitePull B Y).obj K, hY K⟩).obj))
    (hQ : finiteComparisonProEtaleClosure B eR Y'
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingSitePull B Y).obj K)))
    (exE : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingEtaleShriek B c).obj (R.obj K)) ≅
      (finiteRingEtaleShriek B (c.ofIsPullback sq)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj
          (R.obj K)))
    (hexE : exE.hom = finiteRingEtaleExchangeMap B sq c (R.obj K) hRK)
    (exP : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingProShriek B c).obj
          (G.obj ⟨(finiteRingSitePull B Y).obj K, hY K⟩).obj) ≅
      (finiteRingProShriek B (c.ofIsPullback sq)).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj
          (G.obj ⟨(finiteRingSitePull B Y).obj K, hY K⟩).obj))
    (hexP : exP.hom = finiteRingProExchangeMap B sq c
      (G.obj ⟨(finiteRingSitePull B Y).obj K, hY K⟩).obj) :
    (finiteRingSitePull B X').map
        (ae'.homEquiv _ _ (exE.inv ≫
          (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.map
            (ae.counit.app K))) ≫
      (rho'.hom.app ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
        g).mapDerivedCategory.obj K)).hom ≫
      (G'.map (ObjectProperty.homMk
        ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).inv.app K))).hom =
    (unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app (R.obj K) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.map
        (rho.hom.app K).hom ≫
      (ap'.homEquiv ⟨_, hJ⟩ ⟨_, hQ⟩
        (ObjectProperty.homMk (exP.inv ≫
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.map
            (ap.counit.app ⟨(finiteRingSitePull B Y).obj K, hY K⟩).hom))).hom := by
  sorry

/-- Etale origins of a bounded constructible finite-Tor object have a unique transition
lifting their specified comparison isomorphisms. Thus restricting the preceding natural
counit, tensor and exchange identities to constructible adjunctions loses no morphisms
and introduces no dependence on a choice of etale origin.
Source: node final paragraph and proof step 11; Stacks 09AK, 0B65
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof: finite comparison is fully faithful on the whole ordinary etale category.
Fullness lifts alpha followed by inverse alpha'; faithfulness lifts its inverse and
both identity equations. Naturality of each of the named comparisons and transposes
then identifies its conjugates under that transition. Full subcategory inclusions
retain the same Hom sets, including when all inputs and right-adjoint images are
bounded constructible of finite Tor amplitude. -/
theorem finiteRingSiteConstructibleOriginIndependence
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    (M M' : Etale.DerivedCategoryModule (ULift.{u + 1} B) T)
    (hM : Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) T M)
    (hM' : Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) T M')
    (ht : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) a b M)
    (ht' : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) a b M')
    (N : DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B))))
    (alpha : (finiteRingSitePull B T).obj M ≅ N)
    (alpha' : (finiteRingSitePull B T).obj M' ≅ N) :
    ∃! v : M ≅ M', (finiteRingSitePull B T).mapIso v = alpha ≪≫ alpha'.symm := by
  sorry

/-- The omega tensor transpose, with the coefficient unit and both occurrences of the
adjoint comparison retained. The projection isomorphisms are normalized by hom equations
to the coefficient-first canonical signed projection maps; no arbitrary projection is used.
Source: node omega clause and proof step 8; Stacks 0B65, 07A4, 0GL1
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof: paste the canonical projection square at omega_e with naturality in the map
from comparison of omega_e to omega_p. Invert only the two indicated projection maps.
Use the counit equation at the coefficient unit and its unit comparison; preservation
of the right unitor identifies the remaining tensor-counit maps. Applying the general
transpose formula and naturality in the source gives the displayed identity. -/
theorem finiteRingSiteDualizingTranspose
    (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
    [DiscreteTopology B] [IsTopologicalRing B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hX : ∀ M, finiteComparisonProEtaleClosure B eR X ((finiteRingSitePull B X).obj M))
    (hY : ∀ K, finiteComparisonProEtaleClosure B eR Y ((finiteRingSitePull B Y).obj K))
    (hs : ∀ N, finiteComparisonProEtaleClosure B eR X N →
      finiteComparisonProEtaleClosure B eR Y ((finiteRingProShriek B c).obj N))
    (R : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (ae : finiteRingEtaleShriek B c ⊣ R)
    (G : (finiteComparisonProEtaleClosure B eR Y).FullSubcategory ⥤
      (finiteComparisonProEtaleClosure B eR X).FullSubcategory)
    (ap : finiteRingRestriction (finiteRingProShriek B c)
      (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y) hs ⊣ G)
    (b : finiteRingEtaleShriek B c ⋙ finiteRingSitePull B Y ≅
      finiteRingSitePull B X ⋙ finiteRingProShriek B c)
    (hb : ∀ M, b.hom.app M = finiteComparisonCompactSupportMap B c.i c.g M)
    (rho : R ⋙ finiteRingImageLift (finiteRingSitePull B X)
        (finiteComparisonProEtaleClosure B eR X) hX ≅
      finiteRingImageLift (finiteRingSitePull B Y)
        (finiteComparisonProEtaleClosure B eR Y) hY ⋙ G)
    (hc : ∀ K, finiteComparisonCompactSupportMap B c.i c.g (R.obj K) ≫
      (finiteRingProShriek B c).map (rho.hom.app K).hom ≫
        (ap.counit.app ⟨(finiteRingSitePull B Y).obj K, hY K⟩).hom =
      (finiteRingSitePull B Y).map (ae.counit.app K))
    (hUnit : finiteComparisonProEtaleClosure B eR Y (𝟙_ _))
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y)
    (hN : finiteComparisonProEtaleClosure B eR X
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor.obj
          ((finiteRingSitePull B Y).obj K) ⊗ (G.obj ⟨𝟙_ _, hUnit⟩).obj))
    (pe : K ⊗ (finiteRingEtaleShriek B c).obj (R.obj (𝟙_ _)) ≅
      (finiteRingEtaleShriek B c).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor.obj K ⊗
          R.obj (𝟙_ _)))
    (hpe : pe.hom =
      (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) _ _).hom ≫
        finiteRingEtalePF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c (R.obj (𝟙_ _)) K ≫
        (finiteRingEtaleShriek B c).map
          (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) _ _).hom)
    (pp : (finiteRingSitePull B Y).obj K ⊗
        (finiteRingProShriek B c).obj (G.obj ⟨𝟙_ _, hUnit⟩).obj ≅
      (finiteRingProShriek B c).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor.obj
          ((finiteRingSitePull B Y).obj K) ⊗ (G.obj ⟨𝟙_ _, hUnit⟩).obj))
    (hpp : pp.hom =
      (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) _ _).hom ≫
        finiteRingProPF (ModuleCat.{u + 1} (ULift.{u + 1} B)) c
          (G.obj ⟨𝟙_ _, hUnit⟩).obj ((finiteRingSitePull B Y).obj K) ≫
        (finiteRingProShriek B c).map
          (@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) _ _).hom) :
    (finiteRingSitePull B X).map
        (ae.homEquiv _ _ (pe.inv ≫
          (𝟙 K ⊗ₘ ae.counit.app (𝟙_ _)) ≫ (ρ_ K).hom)) ≫
      (rho.hom.app K).hom =
    (finiteRingSiteTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).leftDerivedFunctor.obj K)
      (R.obj (𝟙_ _))).hom ≫
    ((finiteRingSitePullback (ModuleCat.{u + 1} (ULift.{u + 1} B)) f
        (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f) K).hom ⊗ₘ
      ((rho.hom.app (𝟙_ _)).hom ≫
        (G.map (ObjectProperty.homMk
          (finiteRingSiteUnit (ModuleCat.{u + 1} (ULift.{u + 1} B)) Y).hom)).hom)) ≫
    (ap.homEquiv ⟨_, hN⟩ ⟨(finiteRingSitePull B Y).obj K, hY K⟩
      (ObjectProperty.homMk (pp.inv ≫
        (𝟙 ((finiteRingSitePull B Y).obj K) ⊗ₘ
          (ap.counit.app ⟨𝟙_ _, hUnit⟩).hom) ≫
        (ρ_ ((finiteRingSitePull B Y).obj K)).hom))).hom := by
  sorry

end AlgebraicGeometry.ProEtale
