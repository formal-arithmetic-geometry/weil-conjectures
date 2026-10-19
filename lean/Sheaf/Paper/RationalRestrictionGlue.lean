/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Mathlib.CategoryTheory.Adjunction.Restrict
import Sheaf.SixFunctors.IntegralRestrictionBoundedDescent
import Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent
import Sheaf.Paper.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.Paper.RestrictionLocal
import Sheaf.Compactification.BoundaryRefinement

/-!
# Gluing rational constructibility and restricting the exceptional adjunction

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction/
sk-thm-restriction-glue.md and its proof (blueprint: det-thm-restriction-glue).

The two restriction functors below retain the objects and maps of the supplied
compactification functor and its right adjoint. The theorem identifies their Hom
bijection with the original adjunction, including its naturality.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restrict the actual compactification composite to bounded constructible objects.
The membership proof changes neither its objects nor its maps.
Source: blueprint sk-thm-restriction-glue, paragraph (2)
(blueprint: det-thm-restriction-glue). -/
noncomputable def restrictionGlueLowerShriek (c : Compactification f)
    (hF : ∀ A, constantModelBoundedConstructible Λ X A →
      constantModelBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c).obj A)) :
    ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ Y :=
  (constantModelBoundedConstructible Λ Y).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ c)
    (fun A ↦ hF A.obj A.property)

/-- Restrict the supplied right adjoint, using the full inclusion of Dbc into Loc(Dctf).
No new exceptional inverse image is chosen.
Source: blueprint sk-thm-restriction-glue, paragraph (2)
(blueprint: det-thm-restriction-glue). -/
noncomputable def restrictionGlueUpperShriek
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (hY : constantModelBoundedConstructible Λ Y ≤ localizingClosureProEtale Λ Y)
    (hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
        constantModelBoundedConstructible Λ X (G.obj K).obj) :
    ConstantModelBoundedConstructible Λ Y ⥤ ConstantModelBoundedConstructible Λ X :=
  (constantModelBoundedConstructible Λ X).lift
    (ObjectProperty.ιOfLE hY ⋙ G ⋙ (localizingClosureProEtale Λ X).ι)
    (fun K ↦ hG ⟨K.obj, hY K.obj K.property⟩ K.property)

/-- Finite open covers detect bounded constructibility, and the supplied exceptional
adjunction restricts to Dbc. The final equality says that its natural Hom bijection is
exactly the original one, after forgetting the full-subcategory membership proofs.
The arguments `h`, `G`, and `adj` name the functor and adjunction supplied by
sk-prop-sf-existence; no preservation of Dbc or inclusion in the localizing closure
is assumed. The coefficient identification is an isomorphism of condensed ring objects.
Source: blueprint sk-thm-restriction-glue, clauses (1)--(2)
(blueprint: det-thm-restriction-glue).

Proof, following the unit's local-factorization and gluing route:
1. Finite type and quasi-compactness over the field make X and Y Noetherian.
   The rational cases of localizingClosure_ctf_equals_bc identify Dctf with Dbc,
   so Dbc lies in the localizing closure. The admissible-coefficient predicate
   includes the finite-subextension-valued algebraic-closure coefficient.
2. Transport open restrictions through leftDerivedUpperStarIsoMapDerivedCategory.
   Apply bounded_finiteOpenDescent and cohomology_finiteOpenDescent: these proved,
   coefficient-independent lemmas glue the cohomological bounds and the finite
   scheme stratifications. They include empty schemes and empty index types.
3. Apply compactification_localizing to the actual boundary compactification.
   Convert Dbc to Dctf using step 1 and retain the Dbc component of its image.
4. Apply restrictionLocal to the supplied G and adjunction. Its finite affine
   cover has closed factorizations through affine spaces over affine target charts.
   Replace source charts by their open ranges and transport the factorizations.
   Establish their finite-type, separatedness and quasi-compactness instances.
   For each projection and closed immersion, compactificationOverField and
   exists_localizingExceptionalAdjoint supply the auxiliary adjunctions required
   by restrictionLocal. Its local preservation clause applies to K in Dbc.
   Glue these restrictions by step 2, indexed by Fin n in its own universe.
5. Apply Adjunction.restrictFullyFaithful to the two concrete restriction lifts.
   Their commuting comparisons are identity isomorphisms. Unfold the Hom
   equivalence and full inclusions to obtain exactly the original homEquiv,
   with its inherited naturality.
-/
theorem rationalRestrictionGlue
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ A, localizingClosureProEtale Λ X A → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    (∀ (I : Type w) [Finite I] (U : I → X.Opens), iSup U = ⊤ →
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        (∀ i : I, constantModelBoundedConstructible Λ (U i).toScheme
          (((upperStar Λ (U i).ι).mapDerivedCategory).obj M)) →
            constantModelBoundedConstructible Λ X M) ∧
    ∃ (hX : constantModelBoundedConstructible Λ X ≤ localizingClosureProEtale Λ X)
      (hY : constantModelBoundedConstructible Λ Y ≤ localizingClosureProEtale Λ Y)
      (hF : ∀ A, constantModelBoundedConstructible Λ X A →
        constantModelBoundedConstructible Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A))
      (hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
        constantModelBoundedConstructible Λ Y K.obj →
          constantModelBoundedConstructible Λ X (G.obj K).obj),
      ∃ adjbc : restrictionGlueLowerShriek Λ c.obj.obj hF ⊣
          restrictionGlueUpperShriek Λ G hY hG,
        ∀ (A : ConstantModelBoundedConstructible Λ X)
          (K : ConstantModelBoundedConstructible Λ Y)
          (t : (restrictionGlueLowerShriek Λ c.obj.obj hF).obj A ⟶ K),
          (adjbc.homEquiv A K t).hom =
            (adj.homEquiv ⟨A.obj, hX A.obj A.property⟩
              ⟨K.obj, hY K.obj K.property⟩ (ObjectProperty.homMk t.hom)).hom := by
  classical
  let : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  let : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p]; exact hpℓ⟩
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  have hcoeff : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with hE | hbar
    · exact Or.inl ⟨⟨E, inferInstance⟩, hE⟩
    · exact Or.inr hbar
  have htor (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      (constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T := by
    apply (localizingClosure_ctf_equals_bc ℓ T Λ ?_).1.2.2.1
    rcases hcoeff with ⟨E, hE⟩ | hbar
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
    · exact Or.inr (Or.inr (Or.inr hbar))
  have hinc (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      constantModelBoundedConstructible Λ T ≤ localizingClosureProEtale Λ T := by
    intro K hK P hP hSP
    apply hSP K
    rw [htor T]
    exact hK
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hcoeff with hE | hbar
    · exact Or.inr (Or.inr (Or.inr (Or.inl hE)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbar)))))
  have hF : ∀ A, constantModelBoundedConstructible Λ X A →
      constantModelBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A) := by
    intro A hA
    exact ((compactification_localizing Λ ℓ k f c hadm).2.2.2 A
      ((congrFun (htor X) A).mpr hA)).1
  have hglue : ∀ (I : Type w) [Finite I] (U : I → X.Opens), iSup U = ⊤ →
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        (∀ i : I, constantModelBoundedConstructible Λ (U i).toScheme
          (((upperStar Λ (U i).ι).mapDerivedCategory).obj M)) →
            constantModelBoundedConstructible Λ X M := by
    intro I _ U hU M hM
    let isoClosed (T : Scheme.{u}) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ T).2.1
    let e i := (leftDerivedUpperStarIsoMapDerivedCategory Λ (U i).ι).app M
    have hM' i : constantModelBoundedConstructible Λ (U i).toScheme
        ((upperStar Λ (U i).ι).leftDerivedFunctor.obj M) :=
      @ObjectProperty.prop_of_iso _ _ _ (isoClosed (U i).toScheme) _ _
        (e i).symm (hM i)
    exact ⟨IntegralCompactSupport.IntegralRestriction.bounded_finiteOpenDescent
        Λ X I U hU M (fun i ↦ (hM' i).1),
      IntegralCompactSupport.IntegralRestriction.cohomology_finiteOpenDescent
        Λ X I U hU M hM'⟩
  have brown {S T : Scheme.{u}} [S.Over (Spec (.of k))] [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
      [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))]
      (g : S ⟶ T) [g.IsOver (Spec (.of k))]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (cg : Compactification.BoundaryCompactification g) :
      ∃ (hg : ∀ A, localizingClosureProEtale Λ S A → localizingClosureProEtale Λ T
          ((rightDerivedLowerShriekOfCompactification Λ cg.obj.obj).obj A))
        (J : (localizingClosureProEtale Λ T).FullSubcategory ⥤
          (localizingClosureProEtale Λ S).FullSubcategory),
        Nonempty (localizingLowerShriek Λ cg.obj.obj hg ⊣ J) := by
    obtain ⟨hg, hS, hT, hb⟩ := exists_localizingExceptionalAdjoint Λ ℓ k g cg hadm
    let := hS
    let := hT
    obtain ⟨_, _, _, _, J, s, hs⟩ := hb
    let := s
    obtain ⟨_, _, a, _⟩ := hs
    exact ⟨hg, J, ⟨a⟩⟩
  have hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
        constantModelBoundedConstructible Λ X (G.obj K).obj := by
    intro K hK
    obtain ⟨hloc, n, A, u, hA, hcov, hfac⟩ :=
      restrictionLocal Λ ℓ k hcoeff f c h G adj
    have hu : ∀ a, IsOpenImmersion (u a) := fun a ↦ (hA a).2
    let O : Fin n → X.Opens := fun a ↦ (u a).opensRange
    have hO : iSup O = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨a, y, hy⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, y, hy⟩
    have hlocal (a : Fin n) : constantModelBoundedConstructible Λ (O a).toScheme
        (((upperStar Λ (O a).ι).mapDerivedCategory).obj (G.obj K).obj) := by
      have : IsAffine (A a) := (hA a).1
      obtain ⟨V, v, hV, hv, d, i, hi, q, hqi, hq⟩ := hfac a
      have : IsAffine V := hV
      have : IsOpenImmersion v := hv
      have : IsClosedImmersion i := hi
      let e := (u a).isoOpensRange
      have : IsAffine (O a).toScheme := IsAffine.of_isIso e.inv
      let i' := e.inv ≫ i
      let q' := e.inv ≫ q
      have hi' : IsClosedImmersion i' := inferInstance
      have hqi' : i' ≫ (AffineSpace.over (ULift.{u} (Fin d)) V).hom = q' := by
        dsimp [i', q']
        rw [Category.assoc, hqi]
      have heq : e.inv ≫ u a = (O a).ι :=
        (Iso.inv_comp_eq e).mpr (Scheme.Hom.isoOpensRange_hom_ι (u a)).symm
      have hq' : q' ≫ v = (O a).ι ≫ f := by
        dsimp [q']
        rw [Category.assoc, hq, ← Category.assoc, heq]
      let : V.Over (Spec (.of k)) := ⟨v ≫ (Y ↘ Spec (.of k))⟩
      have : v.IsOver (Spec (.of k)) := ⟨rfl⟩
      have : LocallyOfFiniteType (V ↘ Spec (.of k)) :=
        (show LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
      have : IsSeparated (V ↘ Spec (.of k)) :=
        (show IsSeparated (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
      have : IsLocallyNoetherian V :=
        LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of k))
      have : IsNoetherian V := ⟨⟩
      have : QuasiCompact (V ↘ Spec (.of k)) := by
        have : QuasiCompact v := ⟨fun W _hW _hc ↦
          TopologicalSpace.NoetherianSpace.isCompact _⟩
        exact (show QuasiCompact (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
      have : LocallyOfFiniteType ((O a).toScheme ↘ Spec (.of k)) :=
        (show LocallyOfFiniteType ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
      have : IsSeparated ((O a).toScheme ↘ Spec (.of k)) :=
        (show IsSeparated ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
      have : IsLocallyNoetherian (O a).toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian ((O a).toScheme ↘ Spec (.of k))
      have : IsNoetherian (O a).toScheme := ⟨⟩
      have : QuasiCompact ((O a).toScheme ↘ Spec (.of k)) := by
        have : QuasiCompact (O a).ι := ⟨fun W _hW _hc ↦
          TopologicalSpace.NoetherianSpace.isCompact _⟩
        exact (show QuasiCompact ((O a).ι ≫ (X ↘ Spec (.of k))) from inferInstance)
      let P := AffineSpace (ULift.{u} (Fin d)) V
      let pr : P ⟶ V := (AffineSpace.over (ULift.{u} (Fin d)) V).hom
      have : LocallyOfFinitePresentation pr :=
        inferInstanceAs (LocallyOfFinitePresentation (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
      have : LocallyOfFiniteType pr := inferInstance
      have : LocallyOfFiniteType (P ↘ Spec (.of k)) :=
        (show LocallyOfFiniteType (pr ≫ (V ↘ Spec (.of k))) from inferInstance)
      have : IsSeparated (P ↘ Spec (.of k)) :=
        (show IsSeparated (pr ≫ (V ↘ Spec (.of k))) from inferInstance)
      have : QuasiCompact (P ↘ Spec (.of k)) :=
        (show QuasiCompact (pr ≫ (V ↘ Spec (.of k))) from inferInstance)
      have : pr.IsOver (Spec (.of k)) := ⟨rfl⟩
      have : i'.IsOver (Spec (.of k)) := ⟨by
        change i' ≫ (pr ≫ (v ≫ (Y ↘ Spec (.of k)))) =
          (O a).ι ≫ (X ↘ Spec (.of k))
        rw [← Category.assoc i' pr, hqi', ← Category.assoc, hq', Category.assoc,
          comp_over]⟩
      let cp := AlgebraicGeometry.compactificationOverField k pr
      let ci := AlgebraicGeometry.compactificationOverField k i'
      obtain ⟨hp, Fp, ⟨ap⟩⟩ := brown pr cp
      obtain ⟨hi, Fi, ⟨ai⟩⟩ := brown i' ci
      obtain ⟨huStar, _, _, hpres⟩ := hloc v (O a).ι hV inferInstance hv inferInstance
        d i' hi' q' hqi' hq' cp hp Fp ap ci hi Fi ai
      obtain ⟨hK', hbc⟩ := hpres K.obj hK
      let := (constantModelConstructibleFiniteTor_wellDefined Λ (O a).toScheme).2.1
      exact ObjectProperty.prop_of_iso _
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ (O a).ι).app (G.obj K).obj) hbc
    exact ⟨IntegralCompactSupport.IntegralRestriction.bounded_finiteOpenDescent
        Λ X (Fin n) O hO (G.obj K).obj (fun a ↦ by
          let := (constantModelConstructibleFiniteTor_wellDefined Λ (O a).toScheme).2.1
          exact (ObjectProperty.prop_of_iso _
            ((leftDerivedUpperStarIsoMapDerivedCategory Λ (O a).ι).app
              (G.obj K).obj).symm (hlocal a)).1),
      IntegralCompactSupport.IntegralRestriction.cohomology_finiteOpenDescent
        Λ X (Fin n) O hO (G.obj K).obj (fun a ↦ by
          let := (constantModelConstructibleFiniteTor_wellDefined Λ (O a).toScheme).2.1
          exact ObjectProperty.prop_of_iso _
            ((leftDerivedUpperStarIsoMapDerivedCategory Λ (O a).ι).app
              (G.obj K).obj).symm (hlocal a))⟩
  refine ⟨hglue, hinc X, hinc Y, hF, hG, ?_⟩
  let adjbc := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (hinc X))
    (ObjectProperty.fullyFaithfulιOfLE (hinc Y))
    (L := restrictionGlueLowerShriek Λ c.obj.obj hF)
    (R := restrictionGlueUpperShriek Λ G (hinc Y) hG) (Iso.refl _) (Iso.refl _)
  refine ⟨adjbc, ?_⟩
  intro A K t
  simp [adjbc, Adjunction.restrictFullyFaithful, ObjectProperty.fullyFaithfulιOfLE,
    ObjectProperty.ιOfLE, Functor.FullyFaithful.homEquiv]

end AlgebraicGeometry.ProEtale.CondensedRing
