/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AffineRestrictionLocality.CondensedAffineRestrictionLocality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange

/-! # Invertibility of the completed proper/open tower map

Source: Stacks 0F7J; Bhatt--Scholze Definition 6.7.6 and Lemmas 6.7.7, 6.1.13.
(blueprint: lem-zl-completed-composition-tower-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))] [Z.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Z ↘ Spec (.of K₀))] [QuasiCompact (Z ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [g.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

include hl in
/-- The actual proper/open map on one tower is invertible on integral inputs.
Source: Stacks 0F7J and Bhatt--Scholze Definition 6.7.6, Lemmas 6.7.7 and 6.1.13
(blueprint: lem-zl-completed-composition-tower-is-iso).

Proof: extension by zero is fully faithful, so the open unit is invertible.
Proper base change for the cartesian square e.isPullback_restrict identifies
Lambda with the restriction exchange followed by this inverse unit. On the
strict derived reduction system its components are the finite proper/open
isomorphisms on the bounded constructible etale origins of K. Derived-complete
conservativity makes Lambda invertible. Its inverse open adjunct Gamma has those
same finite proper/open reductions. Open extension and proper direct image keep
the completed constructible domain, so the cone of Gamma is complete; its zero
reductions make it zero. Thus Gamma is invertible. The remaining factors of
sfCompletedCompositionOnTower are functorial images of the canonical proper and
open compositors and the equality e.restrict_i_fst. All are invertible, so their
composite is invertible. This includes zero inputs and empty schemes. -/
theorem sfCompletedCompositionOnTower_isIso
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : sfIntegralConstructibleCategory l E X) :
    ∃ hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)),
    ∃ hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
        e.isPullback_restrict.w.symm
          ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη),
      IsIso (sfCompletedCompositionOnTower l E d e K.obj hη hLambda) := by sorry

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual normalized composition word on a compatible tower is invertible on
ordinary bounded constructible condensed Qbar objects. The witnesses include the
identity-on-the-open normalized middle map, its uniqueness, and its invertibility.
All structural morphisms on the tower are finite type over the geometric field;
these explicit instances express the usual tower over that field.
Source: latest blueprint lem-zl-composition-weight-bound, using the compact-support
composition prerequisite and its proper/open normalization.
(blueprint: lem-zl-completed-composition-tower-is-iso).

Proof: the field-coefficient Tor theorem puts K in Dctf. Exact open extension preserves
Dctf. Apply normalized condensed proper/open interchange to the intermediate
compactification and this extended object. Its component m is uniquely normalized and
invertible. The remaining open compositor, proper compositor, and equality transport
are isomorphisms. Functors preserve these isomorphisms, so their displayed composite is
invertible. Empty schemes and zero inputs are included by the same argument. -/
theorem sfCompletedCompositionOnTower_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    [QuasiCompact (T.cf.g ≫ T.cg.i)]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [T.cf.Z.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [T.cg.Z.Over (Spec (.of D.k))] [T.cfg.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T.cf.Z ↘ Spec (.of D.k))]
    [QuasiCompact (T.cf.Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T.cg.Z ↘ Spec (.of D.k))]
    [QuasiCompact (T.cg.Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T.cfg.Z ↘ Spec (.of D.k))]
    [QuasiCompact (T.cfg.Z ↘ Spec (.of D.k))]
    [T.cf.g.IsOver (Spec (.of D.k))] [T.cg.i.IsOver (Spec (.of D.k))]
    [T.q.IsOver (Spec (.of D.k))] [T.p.IsOver (Spec (.of D.k))]
    (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) :
    ∃ m, compositionInterchangeIsNormalized (Profinite.padicAlgClRingObj ℓ)
        T.cf.g T.cg.i (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) m ∧
      (∀ m', compositionInterchangeIsNormalized (Profinite.padicAlgClRingObj ℓ)
        T.cf.g T.cg.i (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) m' → m' = m) ∧
      IsIso m ∧
      IsIso (R((T.cg.g)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (m ≫ R((T.p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
            ((openFactor (Profinite.padicAlgClRingObj ℓ) T.cf.i T.q T.cfg.i T.i_q).hom.app
              K.obj)) ≫
          (rightDerivedLowerStarComp (Profinite.padicAlgClRingObj ℓ) T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar (Profinite.padicAlgClRingObj ℓ)) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj)) := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have : CompactSpace T.cf.Z :=
    QuasiCompact.compactSpace_of_compactSpace (T.cf.Z ↘ Spec (.of D.k))
  have : IsLocallyNoetherian T.cf.Z :=
    LocallyOfFiniteType.isLocallyNoetherian (T.cf.Z ↘ Spec (.of D.k))
  have : IsNoetherian T.cf.Z := ⟨⟩
  have heq := (localizingClosure_ctf_equals_bc ℓ X Λ
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  have hK : (constantModelBoundedConstructible Λ X ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K.obj := by
    simpa only [heq] using K.property
  have hJ := (AffineRestrictionLocality.open_preserves_ctf (CommMon.mk Λ) T.cf.i).2
    K.obj hK
  obtain ⟨δ, hδ⟩ := condensedProperOpenInterchange D ℓ hℓ
    (ULift.{u} (Padic ℓ)) 1 (by omega) Λ
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))) T.cf.g T.cg.i
    (detSfBoundaryCompactification (middle T))
  obtain ⟨hnorm, huniq, hiso⟩ := hδ
    (D((T.cf.i)_!open⟦Λ⟧).obj K.obj)
  have hm := hiso hJ
  let := hm
  refine ⟨_, hnorm, huniq, hm, ?_⟩
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
