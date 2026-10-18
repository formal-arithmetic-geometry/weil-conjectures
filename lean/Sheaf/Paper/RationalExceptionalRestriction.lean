/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.CompactificationLocalizing
import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Rational exceptional inverse image preserves constructibility

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction,
statement and four proof paragraphs (blueprint: sk-thm-restriction).

The right adjoint is specified by its adjunction to the recorded localizing
compactification functor. The two functor equalities identify the restrictions
on objects and maps with those same functors, using the full inclusions.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The full inclusion of Dctf into its localizing closure. On objects and maps
this is the ambient identity: membership follows directly from the intersection
that defines the closure, since every intersected property contains Dctf.
Source: blueprint sk-thm-restriction, last proof paragraph and
sk-def-localizing-closure, defining intersection (blueprint: sk-thm-restriction). -/
noncomputable def constantModelFiniteTorToLocalizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Λ X ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hSP ↦ hSP K hK)

namespace CondensedRing

/-- For rational coefficients the exceptional inverse image on the localizing
closures preserves Dctf, and both functors restrict to an adjoint pair on Dctf.
The equalities after the full inclusions specify the actual restrictions of the
compactification lower shriek and its given right adjoint, including their maps.
Source: blueprint main-20261015, sk-thm-restriction, statement and proof
(blueprint: sk-thm-restriction).

Proof:
1. Finite type over the field gives finite affine covers. Separatedness implies
   quasi-separatedness, so the schemes and the affine charts are qcqs. Apply
   det-def-localizing-closure-ctf-equals-bc to identify Dctf with Dbc and their closures.
2. On each affine chart U over an affine V, choose generators of its finite-type
   coordinate algebra. Evaluation from the polynomial algebra is surjective,
   giving a closed immersion i : U -> A^d_V and f u = v p i. The charts cover X.
   This uses def-weil-finite-type-morphism, def-weil-closed-immersion and
   def-sbc-affine-space; the dimension may vary with the chart.
3. Apply det-thm-restriction-local to these maps to get u^* f^! = i^! p^! v^*.
4. Exact open restriction preserves the cohomological bounds and restricts the
   finite constant local models of sk-def-sfb-constructible. Thus v^* K is Dbc.
   By det-cor-affine-space-rational-induction, p^! v^* K is Dbc as well.
5. By det-prop-closed-adjoint-constructible-support its supported sections on U
   are Dbc; det-prop-closed-adjoint-constructible-yoneda identifies these with
   i^! p^! v^* K. Hence u^* f^! K is Dbc on every chart.
6. Apply det-thm-restriction-glue. Take the minimum and maximum of the finitely
   many local bounds. Refine the finite constructible locally closed partitions
   on the charts to one partition of X. Affine opens are retrocompact in the
   quasi-separated X, so their constructible subsets stay constructible in X
   (def-weil-constructible-subset and lem-weil-pbc-qcqs-morphism-permanence).
   Restrict the finite constant local models to each refined piece. This proves
   global bounded constructibility; for empty X the zero category gives it directly.
7. Returning through the equality in step 1 proves the first conjunct. In the
   chosen compactification f = r j, j is quasi-compact by qcqs permanence.
   det-sf-comp-coherence-single gives preservation of Dctf by Rr_* j_!, hence
   the lower shriek also restricts. Both restrictions have the same ambient maps.
8. Every property in the intersection defining sk-def-localizing-closure contains
   Dctf, so constantModelFiniteTorToLocalizing is the full inclusion into that
   closure. Restrict the Hom equivalences of sk-prop-sf-existence to the two full
   Dctf subcategories. Bijectivity and naturality are unchanged; equivalently
   apply Adjunction.restrictFullyFaithful. This gives the final adjunction.
-/
theorem rationalExceptional_preserves_constructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (_adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    (∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      (constantModelBoundedConstructible Λ Y K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      constantModelBoundedConstructible Λ X (G.obj K).obj ∧
        DerivedCategory.finiteTorAmplitude _ (G.obj K).obj) ∧
    ∃ (F₀ : ConstantModelConstructibleFiniteTor Λ X ⥤
        ConstantModelConstructibleFiniteTor Λ Y)
      (G₀ : ConstantModelConstructibleFiniteTor Λ Y ⥤
        ConstantModelConstructibleFiniteTor Λ X),
      F₀ ⋙ constantModelFiniteTorToLocalizing Λ Y =
        constantModelFiniteTorToLocalizing Λ X ⋙ localizingLowerShriek Λ c.obj.obj h ∧
      G₀ ⋙ constantModelFiniteTorToLocalizing Λ X =
        constantModelFiniteTorToLocalizing Λ Y ⋙ G ∧
      Nonempty (F₀ ⊣ G₀) := by
  sorry

end CondensedRing

end AlgebraicGeometry.ProEtale
