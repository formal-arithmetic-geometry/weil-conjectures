/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import Sheaf.Paper.RestrictionLocal
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.IntegralTensorInverseImage

/-!
# Finite-open gluing and restriction of the integral Brown adjunction

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
sk-thm-int-restriction-glue.md (blueprint: det-thm-int-restriction-glue).

The bounded constructible category uses finite constant scalar models. The restricted
adjunction has exactly the Hom equivalences of the given integral Brown adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The literal full inclusion Dbc into its ordinary localizing closure.
Source: blueprint sk-thm-int-restriction-glue, clause 2, final sentence
(blueprint: det-thm-int-restriction-glue). -/
def constructibleInclusion (X : Scheme.{u}) :
    (generators Λ X).FullSubcategory ⥤ (localizing Λ X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- Restriction of the actual compactification composite Rp_* D(j_!) to Dbc,
using its asserted preservation of Dbc, without changing any morphism.
Source: blueprint sk-thm-int-restriction-glue, clause 2, final sentence
(blueprint: det-thm-int-restriction-glue). -/
def restrictedLowerShriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ K, generators Λ X K → generators Λ Y ((image Λ c).obj K)) :
    (generators Λ X).FullSubcategory ⥤ (generators Λ Y).FullSubcategory :=
  (generators Λ Y).lift ((generators Λ X).ι ⋙ image Λ c)
    (fun K ↦ hF K.obj K.property)

/-- Restriction of the given Brown right adjoint to Dbc using its asserted preservation.
Source: blueprint sk-thm-int-restriction-glue, clause 2
(blueprint: det-thm-int-restriction-glue). -/
def restrictedUpperShriek {X Y : Scheme.{u}}
    (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory)
    (hG : ∀ K : (localizing Λ Y).FullSubcategory,
      generators Λ Y K.obj → generators Λ X (G.obj K).obj) :
    (generators Λ Y).FullSubcategory ⥤ (generators Λ X).FullSubcategory :=
  (generators Λ X).lift (constructibleInclusion Λ Y ⋙ G ⋙ (localizing Λ X).ι)
    (fun K ↦ hG ((constructibleInclusion Λ Y).obj K) K.property)

/-- The two clauses of finite-open gluing and integral exceptional preservation.
The quantification over a right adjoint with its adjunction refers to every representative
of the unique Brown adjoint, rather than choosing new exceptional-inverse-image data.
The Hom equality requires the restricted adjunction to inherit the given one.
Source: blueprint sk-thm-int-restriction-glue, clauses 1 and 2
(blueprint: det-thm-int-restriction-glue). -/
def integralRestrictionGlueAssertions (k : Type u) [Field k] : Prop :=
  (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      (I : Type w) [Finite I] (U : I → X.Opens),
      iSup U = ⊤ → ∀ M : Ambient Λ X,
        (∀ i : I, generators Λ (U i).toScheme ((pull Λ (U i).ι).obj M)) →
        generators Λ X M) ∧
  (∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      (c : Compactification.BoundaryCompactification f)
      (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c.obj.obj).obj K))
      (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory)
      (adj : lowerShriek Λ c.obj.obj h ⊣ G),
    ∃ (hF : ∀ K, generators Λ X K → generators Λ Y ((image Λ c.obj.obj).obj K))
      (hG : ∀ K : (localizing Λ Y).FullSubcategory,
        generators Λ Y K.obj → generators Λ X (G.obj K).obj),
      ∃ adj' : restrictedLowerShriek Λ c.obj.obj hF ⊣ restrictedUpperShriek Λ G hG,
        ∀ (A : (generators Λ X).FullSubcategory) (B : (generators Λ Y).FullSubcategory)
          (m : (restrictedLowerShriek Λ c.obj.obj hF).obj A ⟶ B),
          (adj'.homEquiv A B m).hom =
            (adj.homEquiv ((constructibleInclusion Λ X).obj A)
              ((constructibleInclusion Λ Y).obj B) (ObjectProperty.homMk m.hom)).hom)

/-- Bounded integral constructibility glues along finite open covers, and the Brown
exceptional inverse image preserves Dbc and restricts its adjunction to Dbc.
Source: blueprint main-20261015, sk-thm-int-restriction-glue.md and its proof
(blueprint: det-thm-int-restriction-glue).

Proof plan (the eight steps of the DAG node):
1. Identify an open's pro-etale site with the slice by
   lem-weil-proetale-weakly-etale-localization. The integral ring restricts by
   det-prop-sfb-qlbar-colimit-x-integral-limit. Exact restriction follows from
   lem-pur-site-restriction-module-adjunction-exact, and commutes with cohomology.
2. Take the minimum lower and maximum upper cohomological bounds on a nonempty
   finite cover (sk-def-sfb-bounded-constructible). Vanishing is detected on the
   cover by sheaf uniqueness (def-weil-pbc-proetale-site). For an empty cover X is
   empty and every sheaf is zero, so boundedness holds directly.
3. Refine the local finite constructible stratifications by intersections of their
   strata and closed complements. The schemes are Noetherian by
   lem-weil-pbc-finite-type-over-noetherian in sk-def-sfb-dc-setting, so locally
   closed strata are constructible (def-weil-constructible-subset). Pull back the
   finite scalar matrix presentations of sk-def-sfb-constructible to refined strata.
4. Boundedness and this constructibility are exactly generators, by
   sk-def-sfb-constructible; no derived-completeness assertion is needed.
5. Use the geometric chart clause of det-thm-restriction-local at coefficient E:
   finite affine opens U,V and closed U -> A^d_V, with f u = v p i. Noetherianity
   makes all these maps remain in the standing separated finite-type setting.
6. det-def-localizing-closure-ctf-equals-bc identifies the integral localizing
   categories. det-sf-mate-open-restriction gives w^! = w^* on opens. Composition
   from det-prop-int-brown-construction and counit-compatible adjoint uniqueness
   from det-prop-int-brown-adjoint give u^* f^! = i^! p^! v^*.
7. sk-lem-int-tensor puts v^*K in Dbc; det-thm-int-restriction-line puts p^!v^*K
   in Dbc; det-thm-int-restriction-closed puts i^!p^!v^*K in Dbc. Clause 1 now
   glues these local conclusions and shows f^!K belongs to Dbc.
8. det-prop-int-brown-construction preserves Dbc under Rf_!. Both inclusions into
   their localizing categories are full (sk-def-localizing-closure). Restrict the
   original natural Hom equivalences, obtaining the claimed adjunction and Hom
   equality, hence the inherited unit and counit.
-/
theorem integralRestrictionGlue (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    integralRestrictionGlueAssertions.{u, w} (Profinite.padicIntegersRingObj ℓ E.val) k := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
