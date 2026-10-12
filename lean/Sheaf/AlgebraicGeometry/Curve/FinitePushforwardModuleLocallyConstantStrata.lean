/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Locally constant source strata for a finite direct image

Source: Stacks Project, Tags 095K, 0959, 04DZ and 0A5D, with the generic
finite-algebra splitting refinement for module coefficients.
(blueprint: lem-weil-pbc-finite-module-locally-constant-strata)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The local constancy part of finite direct-image constructibility reflection.
Source: Stacks Project, Tag 095K (lemma-decompose-quasi-finite-morphism), Tag 0959
(lemma-finite-pushforward-commutes-with-base-change), Tag 04DZ, and the
finite-stratification refinement of Tag 0A5D.
(blueprint: lem-weil-pbc-finite-module-locally-constant-strata)

Proof:
1. Pass to the reduced target using topological invariance. The Noetherian curve
has finitely many irreducible components. Choose disjoint affine integral dense
opens in its positive-dimensional components, avoiding the zero-dimensional
components, and shrink them into the locally constant strata of the constructible
sheaf f_*F. Their complement consists of finitely many closed points.
2. Over each chosen Spec A, write its finite inverse image as Spec B. Apply
lem-weil-pbc-generic-finite-algebra-splitting, then shrink further. After a
surjective finite etale base change U, the reduced inverse image splits into
finitely many components universally homeomorphic to U. Finite base change and
pullback stability show that the direct image over U is finite locally constant.
3. The equivalences of etale sites induced by reduction and the component
universal homeomorphisms identify the component sheaves with direct summands of
this finite locally constant sheaf on U. Trivialize the ambient sheaf as M_U
with M finitely generated. Its summand projector is locally a constant linear
map: its values on finitely many generators are simultaneously locally constant.
Discard empty cover members; evaluation at a geometric point makes the map
idempotent. Its image is a constant module sheaf. Thus each summand is locally
constant. Transport along the universal homeomorphisms and descend along the
etale covers by composing trivializing covers. This gives local constancy on
the inverse images of the chosen dense opens, including nonreduced sources.
4. The inverse image of each omitted closed point is finite over the algebraically
closed field k. Its reduced scheme is a finite disjoint union of Spec k. Every
module sheaf on these points is constant, without any finite generation
hypothesis. Topological invariance therefore makes the source restrictions
locally constant on these remaining point strata. Choose their reduced induced
scheme structures, immersed in X. The dense source opens and these finitely many
points partition X into constructible locally closed strata; X is Noetherian
because it is finite over Y. These immersions define the asserted Stratification.
For an empty source choose the empty stratification; empty fibres contribute no
strata. Zero modules and degree-one maps require no separate assumptions.

Only local constancy is asserted here. Finiteness of all source stalks is proved
separately using the finite direct-image counit, and is not part of this hole. -/
theorem Scheme.exists_locallyConstant_stratification_of_finite_lowerStar_module
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : Scheme.IsConstructibleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) :
    ∃ S : Scheme.Stratification X, ∀ i : Fin S.n,
      Scheme.IsLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj F) := by sorry

end AlgebraicGeometry
