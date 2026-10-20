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
import Sheaf.Paper.CoefficientHeart
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.Compactification.BoundaryRefinement
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.RestrictionLocal
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

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

Proof plan, following the six steps of the DAG:
1. The standing finite-type schemes are Noetherian by pqf-lem-locnoeth-lft and
   lem-weil-pbc-qcqs-over-affine. The rational assertion sk-lem-coefficient-heart
   identifies Dctf with Dbc, hence puts Dbc inside sk-def-localizing-closure.
   For Qbar use the finite-subextension-valued sk-def-sfb-qlbar-condensed ring.
2. By sk-prop-sfb-cartesian-coefficients open restriction is exact and commutes
   with cohomology. For a nonempty scheme take the minimum and maximum of the
   finitely many local cohomological bounds. Cohomology outside this interval
   vanishes by the sheaf axiom on the induced covers of pro-etale test objects.
   If X is empty, the empty-cover sheaf axiom makes every module zero; this
   also treats an empty indexing type and covers consisting of empty opens.
3. Use sk-lem-coefficient-heart to stratify the finitely many local cohomology
   sheaves. Compose their immersions into X (lem-weil-pbc-proper-fp-permanence),
   and add reduced closed complements (lem-weil-pbc-reduced-induced-closed-subscheme).
   Apply det-lem-coefficient-heart-common-stratification to these finitely many
   stratifications. Every nonempty refined stratum lies in a cover member;
   its lisse restriction is supplied by that node's second clause, applied to
   the already constructible local sheaf. The heart criterion and step 2 give Dbc.
4. For K in Dbc, det-thm-restriction-local gives a finite affine cover where
   f^!K is bounded constructible. Apply clause (1) just established.
5. The boundary compactification has quasi-compact open part and proper second
   part (sk-def-nagata-sketch-data). Apply det-sf-comp-coherence-single to
   Rp_* D(j_!). Step 1 identifies its Dctf preservation with Dbc preservation.
6. The inclusions of Dbc and the localizing closures are full. Thus the same
   Hom equivalence of sk-prop-sf-existence is the claimed restricted equivalence;
   its naturality equations are unchanged. Equivalently apply
   CategoryTheory.Adjunction.restrictFullyFaithful to the two concrete lifts.
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
