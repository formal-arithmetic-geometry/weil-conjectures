/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.GeneralFieldDctf
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence

/-!
# General-field compact-support scalar/site square

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md, Existence and Locality and Charts
(blueprint: lem-pur-general-field-compact-scalar-site-square).

The statement uses the canonical intrinsic scalar map and the canonical etale-origin
comparison.  Its proof is postponed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Canonical compact-support comparison for an etale-origin input.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Charts.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).

The comparison is assembled from the published site comparison,
the fixed constant-ring compact-support comparison, and the ordinary
compactification comparison.  Keeping it as a definition prevents an
arbitrary natural isomorphism from entering the statement. -/
noncomputable def canonicalCompactSupportSiteIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≅
    (reductionCompactSupport A c.i c.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) := by
  simpa only [reductionCompactSupport, Scheme.sfIntrinsicCompactSupport,
    reductionConstantPush_eq] using
    (Scheme.FiniteCompactScalar.compactSiteIso A c L)

/-- Canonical scalar/site comparison on an etale-origin object.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Charts.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).
-/
noncomputable def canonicalSiteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  Scheme.FiniteCompactScalar.siteScalarIso φ T

/-- Intrinsic compact-support compositor obtained by transporting the chosen
etale compositor through the finite coefficient site comparisons.  The etale
compositor is `coherenceEtaleCompositor` for exactly the three supplied
compactifications (chosen compositor conjugated by the canonical compactification
changes), so no further triangle datum is needed.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.md, Step 4.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`). -/
noncomputable def canonicalIntrinsicCompactSupportCompositor
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionCompactSupport A cg.i cg.g).obj
        ((reductionCompactSupport A cf.i cf.g).obj
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≅
      (reductionCompactSupport A cfg.i cfg.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) := by
  let Ecf := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).obj E
  let qcf := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).app E
  let qcg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg).app Ecf
  let qcfg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cfg).app E
  exact (Functor.mapIso (reductionCompactSupport A cg.i cg.g)
      (canonicalCompactSupportSiteIso A cf E).symm) ≪≫
    (Functor.mapIso (reductionCompactSupport A cg.i cg.g)
      ((finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcf.symm)) ≪≫
    (canonicalCompactSupportSiteIso A cg Ecf).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso qcg.symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso
      (DerivedCategory.Plus.ι.mapIso
        ((coherenceEtaleCompositor (ULift.{u + 1, u} A) cf cg cfg).app E)) ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso qcfg ≪≫
    canonicalCompactSupportSiteIso A cfg E

/-- Intrinsic compact-support refinement comparison obtained by transporting
the canonical bounded-plus refinement isomorphism through the site comparisons.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.md, Step 4.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`). -/
noncomputable def canonicalIntrinsicCompactSupportRefinement
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {cf cd : Compactification f} (r : cf.Refinement cd)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionCompactSupport A cd.i cd.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≅
      (reductionCompactSupport A cf.i cf.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) := by
  let qcd := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cd).app E
  let qcf := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).app E
  exact (canonicalCompactSupportSiteIso A cd E).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcd.symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso
      (DerivedCategory.Plus.ι.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso
          (ULift.{u + 1, u} A) r).app E)) ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcf ≪≫
    canonicalCompactSupportSiteIso A cf E

/-- General-field compact-support scalar/site square.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Existence and Locality:
`b`, open balancing and composition; Charts: identification with finite-site computation
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).

Proof steps: (1) construct the intrinsic constant-ring comparison from the etale
proper mate and the exact open tensor comparison; (2) prove the proper square by
the finite-coefficient projection formula; (3) prove the open square by the
unit-normalized balancing map; (4) paste the proper and open squares to obtain
the displayed formula; (5) transport it through every etale-origin presentation;
(6) use the canonical etale compact-support compositor, its intrinsic site transport,
and the finite-site coherence calculation to identify the composite b-map with
`F_{v,B}(b_u) ≫ b_v(F_{u,A})`; the coefficient-mate and tensor/site squares
transport this identity through `φ`.  Use the canonical etale lower-shriek
composition isomorphism to identify the corresponding beta composite. (7) use the
canonical proper-refinement comparison, the pro-etale refinement coefficient mate,
and their intrinsic site transport for the b square; use the canonical lower-shriek
refinement comparison for the beta scalar square.  The naturality clause transports
the displayed formula through `η` by naturality of the scalar map and of both
reduction functors.
The proof is postponed. -/
theorem generalFieldCompactScalarSiteSquare
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : pchar ≠ ell)
    (k : Type u) [Field k] [CharP k pchar]
    {Z W : Scheme.{u}}
    [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))]
    [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (h : Z ⟶ W) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification h)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
    (φ : A →+* B)
    (M : proEtaleDerivedCategory Z A)
    (hM : generalFieldDctf Z A M)
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hL : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z L.obj)
    (hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj))
    (η : (finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj ≅ M) :
    IsIso ((reductionDirectImageComparison φ c.i c.g).app M) ∧
      generalFieldDctf W B
        ((scalarExtensionFunctor φ W).obj
          ((reductionCompactSupport A c.i c.g).obj M)) ∧
      generalFieldDctf W B
        ((reductionCompactSupport B c.i c.g).obj
          ((scalarExtensionFunctor φ Z).obj M)) ∧
      IsIso ((Etale.compactScalarMap
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app L.obj) ∧
      generalFieldDctf Z A
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj) ∧
      generalFieldDctf W B
        ((finiteCoefficientIntrinsicDerivedComparison W B).obj
          ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).obj
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj))) ∧
      ((reductionDirectImageComparison φ c.i c.g).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj)) =
        (scalarExtensionFunctor φ W).map
          (canonicalCompactSupportSiteIso A c L).inv ≫
          (canonicalSiteScalarIso φ W).hom.app ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
          (finiteCoefficientIntrinsicDerivedComparison W B).map
            ((Etale.compactScalarMap
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app L.obj) ≫
          (canonicalCompactSupportSiteIso B c
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj, hLB⟩).hom ≫
          (reductionCompactSupport B c.i c.g).map
            ((canonicalSiteScalarIso φ Z).inv.app L.obj) ∧
      ((scalarExtensionFunctor φ W).map
          ((reductionCompactSupport A c.i c.g).map η.hom) ≫
        (reductionDirectImageComparison φ c.i c.g).app M) =
        (reductionDirectImageComparison φ c.i c.g).app
            ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj) ≫
          (reductionCompactSupport B c.i c.g).map
            ((scalarExtensionFunctor φ Z).map η.hom) ∧
      (∀ {C : Type u} [CommRing C] [Finite C]
        (hC : ∃ n : ℕ, ∀ x : C, (ell ^ n) • x = 0)
        (ψ : B →+* C),
        (scalarExtensionFunctor_composition φ ψ W).hom.app
            ((reductionCompactSupport A c.i c.g).obj M) ≫
          (reductionDirectImageComparison (ψ.comp φ) c.i c.g).app M =
        (scalarExtensionFunctor ψ W).map
            ((reductionDirectImageComparison φ c.i c.g).app M) ≫
          (reductionDirectImageComparison ψ c.i c.g).app
            ((scalarExtensionFunctor φ Z).obj M) ≫
          (reductionCompactSupport C c.i c.g).map
            ((scalarExtensionFunctor_composition φ ψ Z).hom.app M)) ∧
      (∀ {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S]
        {f : X ⟶ Y} {g : Y ⟶ S} [IsSeparated f] [LocallyOfFiniteType f]
        [QuasiCompact f] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        (cf : Compactification f) (cg : Compactification g)
        (cfg : Compactification (f ≫ g))
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)),
        (scalarExtensionFunctor φ S).map
            (canonicalIntrinsicCompactSupportCompositor A cf cg cfg E).inv ≫
          (reductionDirectImageComparison φ cg.i cg.g).app
            ((reductionCompactSupport A cf.i cf.g).obj
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionDirectImageComparison φ cf.i cf.g).app
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionCompactSupport B cf.i cf.g).map
              ((canonicalSiteScalarIso φ X).hom.app E.obj)) ≫
          (canonicalIntrinsicCompactSupportCompositor B cf cg cfg
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom =
        (reductionDirectImageComparison φ cfg.i cfg.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cfg.i cfg.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj)) ∧
      (∀ {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
        {f : X ⟶ Y} {g : Y ⟶ Z}
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        (d : Compactification g) (e : Compactification (f ≫ d.i))
        (E : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))),
        (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).map
            ((Etale.rightDerivedLowerShriekOfCompactificationCompIso
              (ULift.{u + 1, u} A) d e).hom.app E) ≫
          (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) (d.comp e)).app E =
        (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) d).app
            ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e.restrict).obj E) ≫
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
            ((Etale.compactScalarMap
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) e.restrict).app E) ≫
          (Etale.rightDerivedLowerShriekOfCompactificationCompIso
            (ULift.{u + 1, u} B) d e).hom.app
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E)) ∧
      (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        {cf cd : Compactification f} (r : cf.Refinement cd)
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)),
        (scalarExtensionFunctor φ Y).map
            (canonicalIntrinsicCompactSupportRefinement A f r E).hom ≫
          (reductionDirectImageComparison φ cf.i cf.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cf.i cf.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) =
        (reductionDirectImageComparison φ cd.i cd.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cd.i cd.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) ≫
          (canonicalIntrinsicCompactSupportRefinement B f r
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom) ∧
      (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        {cf cd : Compactification f} (r : cf.Refinement cd)
        (hcart : IsPullback cf.i (𝟙 X) r.hom cd.i)
        (E : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))),
        (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).map
            ((Etale.rightDerivedLowerShriekOfCompactificationComparison
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r hcart).app E) ≫
          (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) cf).app E =
        (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) cd).app E ≫
          (Etale.rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) r hcart).app
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E)) := by
  sorry

end AlgebraicGeometry.ProEtale
