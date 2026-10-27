/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel

/-!
# Flatness of the canonical scalar algebra after pullback from the point

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat.
(blueprint: lem-sfb-scalar-counit-flat-pullback)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] constantScalarSheaf_laxBraided

/-- The canonical constant-scalar counit on the profinite site.
Source: the constant-sheaf/evaluation adjunction, Stacks Tag 093J.
(blueprint: lem-sfb-scalar-counit-flat-pullback) -/
abbrev pointScalarCounit
    (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Γ] [IsCommMonObj Γ] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Γ) ⟶ Γ :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).counit.app Γ

/-- The counit is a homomorphism of ring objects.
Source: monoidality of the constant-sheaf adjunction, Stacks Tag 093J.
(blueprint: lem-sfb-scalar-counit-flat-pullback) -/
instance pointScalarCounit_isMonHom
    (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Γ] [IsCommMonObj Γ] :
    IsMonHom (pointScalarCounit Γ) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := scalarSections.{u}
  let adj : C ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  exact adj.isMonHom_counitAlgHom Γ

/-- The constant scalar ring is commutative.
Source: the braided constant-sheaf functor, Stacks Tag 093J.
(blueprint: lem-sfb-scalar-counit-flat-pullback) -/
instance pointScalarCounit_source_comm
    (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Γ] [IsCommMonObj Γ] :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Γ)) := Functor.isCommMonObj_obj

/-- Flatness of the point scalar algebra persists for the actual canonical scalar map on
an arbitrary scheme. The hypothesis concerns all modules on the profinite site, rather
than only constant modules.

Source: Stacks Project, Modules on Sites, Tag 05VD, lemma-pullback-flat; Tag 03ER,
definition-flat; the canonical scalar map of blueprint local-model paragraph (2).
(blueprint: lem-sfb-scalar-counit-flat-pullback)

Proof. Put C = constant Γ(*) and ε = pointScalarCounit Γ. The comparison
Mod.extendForgetTensorIso identifies extension by ε, after forgetting, with tensoring
by N = Res_ε Γ, after forgetting. Since forgetting preserves and reflects finite limits,
the hypothesis makes tensoring by N left exact. Tensor is right exact, and its symmetry
identifies its two sides, so N is flat. Transfer N through the internal/section-module
tensor equivalence. Pull back this flat module along the geometric inverse image from
the profinite site to Spec Z, and then along W → Spec Z, applying Tag 05VD with identity
change of rings at each stage. The algebraic inverse-image presentations use the usual
sheafified left Kan extensions; their finite-limit and operation comparisons are the
ones defining pointUpperStar and upperStar. Transfer back to internal modules.
The natural isomorphism mapModComapIso for ε identifies the resulting module with the
restriction of the pulled-back regular Γ-module along p_W^* ε. The monoidal unit
comparison identifies the pulled-back regular module with the regular module of Γ_W.
By the definitions of scalarConstant and scalarCoefficientHom, p_W^* C is exactly the
source scalar ring in the conclusion and p_W^* ε is exactly its canonical scalar map.
Transport flatness across these module isomorphisms. This argument also applies to the
zero ring, the empty scheme, and empty finite relations. -/
theorem scalarCounit_flat_pullback
    (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Γ] [IsCommMonObj Γ]
    (h : PreservesFiniteLimits (Mod.extendScalars (pointScalarCounit Γ)))
    (W : Scheme.{u}) :
    ObjectProperty.flat
      ((Mod.comap (scalarCoefficientHom Γ W)).obj
        (Mod.regular (condensedRingObj Γ W))) := by sorry

end AlgebraicGeometry.ProEtale
