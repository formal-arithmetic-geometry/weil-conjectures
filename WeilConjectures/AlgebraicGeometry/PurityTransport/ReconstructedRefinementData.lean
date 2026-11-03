/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Reconstructed refinement data for a fixed condensed coefficient and morphism

The data record contains, for the given coefficient sheaf `Λ` and morphism `f`, the
canonical compactification candidates `P_c` on `Dctf(X, Λ)`, the canonical refinement
components `α_h` at objects of `Dctf(X, Λ)`, the restricted exceptional inverse image
`J = f^!`, and the unique counit-compatible comparison of any right adjoint of the
restricted compact support with `J`.  Every field is tied to the published construction
by an equality field.  Coherence of the `α_h`, the smooth Brown comparison and the
finite-reduction compatibilities (with the finite-stage `f^!` of `def-pur-conventions`,
`Scheme.finiteExceptionalInverseImage`) are statements of their own DAG nodes.

Source: blueprint `part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-setup/
sec-the-purity-statement/sk-thm-purity-transport`, Proof Step 3 (clauses 1--2) and
Proof Step 1 (clause 3)
(blueprint: def-pur-reconstructed-refinement-data).
-/
@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Canonical compact-support and adjoint data for the specified `f` and `Λ`.

Clause 1: `P c` is `R f̄_* j_!` for the boundary compactification `c`, restricted to
`Dctf(X, Λ)` through its inclusion into the localizing closure, and `alpha h K` is the
canonical refinement component `α_{h,K} : P_c(K) → P_d(K)` for `h : d ⟶ c`, built from
the compositor and open-extension map of `def-sf-comp-refinement-data`.
Clause 2: `J` is the restricted Brown right adjoint `f^!` of `det-def-sf-operations`,
and `rightAdjointComparison G adj` is the unique counit-compatible isomorphism
`G ≅ J` of `det-sp-unique-right-adjoint` for any right adjoint `G` of `Rf_!` on `Dctf`.
Clause 3 introduces no data.  The fields are tied to the published constructions by
the accompanying equality fields; no coherence or comparison proposition is copied.
Source: blueprint `sk-thm-purity-transport`, Proof Steps 3 and 1
(blueprint: def-pur-reconstructed-refinement-data). -/
structure ReconstructedRefinementData
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcd : BaseFieldFiniteCD ell D.k)
    [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) where
  /-- The canonical compactification candidate `P_c = R f̄_* j_!` on `Dctf(X, Λ)`. -/
  P : ∀ c : Compactification.BoundaryCompactification f.left,
    type_of% (ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ell D.k hcd f hΛ).source_mem ⋙
      CondensedRing.compactificationLocalizingCandidate Λ c)
  /-- The candidate field is the published candidate restricted to `Dctf(X, Λ)`. -/
  P_canonical : ∀ c : Compactification.BoundaryCompactification f.left,
    P c = ObjectProperty.ιOfLE
        (sixOperationsLocalizingAdjunction Λ ell D.k hcd f hΛ).source_mem ⋙
      CondensedRing.compactificationLocalizingCandidate Λ c
  /-- The canonical refinement component `α_{h,K} : P_c(K) → P_d(K)` at `K ∈ Dctf(X, Λ)`. -/
  alpha : ∀ {c d : Compactification.BoundaryCompactification f.left} (h : d ⟶ c)
      (K : ConstantModelConstructibleFiniteTor Λ X.left),
    type_of% (CondensedRing.compactificationRefinementComponent Λ h K.obj)
  /-- The refinement component is the published canonical map. -/
  alpha_canonical : ∀ {c d : Compactification.BoundaryCompactification f.left}
      (h : d ⟶ c) (K : ConstantModelConstructibleFiniteTor Λ X.left),
    alpha h K = CondensedRing.compactificationRefinementComponent Λ h K.obj
  /-- The restricted exceptional inverse image `J = f^!`. -/
  J : type_of% (CondensedRing.ctfExceptionalInverseImage Λ ell D.k hcd f hΛ)
  /-- `J` is the published restricted Brown right adjoint. -/
  J_canonical : J = CondensedRing.ctfExceptionalInverseImage Λ ell D.k hcd f hΛ
  /-- The comparison of a chosen right-adjoint presentation `G` of `Rf_!` on `Dctf`
  with `J`. -/
  rightAdjointComparison :
    ∀ (G : ConstantModelConstructibleFiniteTor Λ Y.left ⥤
        ConstantModelConstructibleFiniteTor Λ X.left),
      (CondensedRing.ctfLowerShriek Λ ell D.k hcd f hΛ ⊣ G) →
        (G ≅ CondensedRing.ctfExceptionalInverseImage Λ ell D.k hcd f hΛ)
  /-- It is the unique counit-compatible right-adjoint isomorphism. -/
  rightAdjointComparison_canonical :
    ∀ (G : ConstantModelConstructibleFiniteTor Λ Y.left ⥤
        ConstantModelConstructibleFiniteTor Λ X.left)
      (adj : CondensedRing.ctfLowerShriek Λ ell D.k hcd f hΛ ⊣ G),
      rightAdjointComparison G adj =
        adj.rightAdjointUniq (CondensedRing.ctfExceptionalAdjunction Λ ell D.k hcd f hΛ)

end AlgebraicGeometry.ProEtale.PurityTransport
