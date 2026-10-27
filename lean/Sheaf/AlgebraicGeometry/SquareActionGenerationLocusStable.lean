/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Connected.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.FiniteStability
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Stability of the positive-power section-generation locus

Source: Guo, Divisors on coherent schemes and homogeneous spaces, section 5.6 and
Lemma 6.3(ii), printed p.15, smooth separated finite-presentation specialization
(blueprint: lem-sfb-square-action-generation-locus-stable).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The union of all nonvanishing loci of sections of positive tensor powers is open
and stable under the action. The square hypothesis is an existence of invertible base
modules and isomorphisms, with no choices or coherence requirements. In `Over S`, `X ⊗ B`
is `X ×_S B`; the map `(snd X B ≫ g) • fst X B` sends `(x,b)` to `g(b)x`.
Its pullback of `M` is canonically `τ_g^* M_B` by pullback composition.
The final factorization is the action restricted to the open subscheme `E`.

Source: Guo, section 5.6 and Lemma 6.3(ii), printed p.15
(blueprint: lem-sfb-square-action-generation-locus-stable).

Proof:
1. Put E_n equal to the union of the nonvanishing opens of all sections of M.tensorPow n.
   Finite presentation over the affine base makes X quasi-compact; separatedness and
   invertibility give the separated and quasi-coherent inputs for flat cohomology base change.
2. A point of H ×_S E_n gives h and y over its residue field K, with x = hy. Pass to an
   algebraic closure Ω. Connectedness and the rational identity imply geometric connectedness
   (`lem-sbc-connected-rational-point-geometrically-connected`). Finite presentation survives
   base change (`lem-weil-pbc-finite-presentation-base-change-composition`). The group identity
   component theorem (`lem-sfb-locally-algebraic-group-identity-component`) makes H_Ω irreducible.
3. The open W of v with vx in (E_n)_Ω contains h⁻¹. Irreducibility makes W ∩ inv⁻¹(W)
   nonempty. A residue-field point g of this intersection gives both gx and g⁻¹x in E_n,
   witnessed by original global sections s_+ and s_- of M.tensorPow n.
4. At the image p of g in H put R = O_{H,p}, B = Spec R. The canonical B → H is flat
   (`lem-sbc-canonical-stalk-spectrum-flat`), and H → S is flat by smoothness
   (`lem-pc-smooth-flat`). Composition and the affine flatness criterion make R flat over
   the base ring. The local-spectrum bijection and canonical stalk-spectrum morphism
   (`lem-weil-pbc-morphism-from-spec-local-ring`,
   `lem-weil-pbc-spec-local-ring-canonical-morphism`) factor g through B, giving a lift of x.
5. Apply the square condition to the canonical B-point and its inverse. The base line N
   is trivial over the local spectrum B. Pullback commutes with tensor powers
   (`lem-sc-pullback-tensor-power-iso`). Tensor the translated pullbacks of s_+ and s_-
   to obtain a section r of M_B.tensorPow (2*n), nonzero at the lift of x by
   `lem-weil-pbc-tensor-power-section-nonvanishing-pullback` and rank-one linear algebra.
6. The degree-zero canonical flat-cohomology comparison
   (`lem-pc-flat-cohomology-separated`, `def-pc-flat-cohomology-comparison`) writes
   r as a finite sum of R-multiples of base changes of global sections of M.tensorPow (2*n).
   If all these sections vanished at x, r would vanish at its lift. Thus x belongs to E_{2n}.
7. Taking the union over positive n proves that the action image is contained in E.
   The identity section gives the reverse inclusion. Since E is open, the restricted
   action factors through its open subscheme, giving the last conjunct. -/
theorem square_action_generation_locus_stable
    (S : Scheme.{u}) [IsAffine S]
    (H : Over S) [GrpObj H] [Smooth H.hom] [IsSeparated H.hom]
    [LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom] [QuasiSeparated H.hom]
    (hH : ∀ s : S, ConnectedSpace (H.hom.fiber s))
    (X : Over S) [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [ModObj H X]
    (M : X.left.Modules) [M.IsInvertible]
    (hsquare : ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧
        Nonempty
          (((Scheme.Modules.tensorPullback
              (((snd X B ≫ (g * h)) • fst X B).left)).obj M ⊗
            (Scheme.Modules.tensorPullback (fst X B).left).obj M) ≅
           (((Scheme.Modules.tensorPullback
               (((snd X B ≫ g) • fst X B).left)).obj M ⊗
             (Scheme.Modules.tensorPullback
               (((snd X B ≫ h) • fst X B).left)).obj M) ⊗
            (Scheme.Modules.tensorPullback (snd X B).left).obj N))) :
    ∃ E : X.left.Opens,
      (E : Set X.left) = ⋃ (n : ℕ) (_ : 0 < n)
        (s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤)),
          Scheme.Modules.nonvanishingLocus (M.tensorPow n) s ∧
      Set.image (γ[H, X].left.base)
        ((snd H X).left.base ⁻¹' (E : Set X.left)) = (E : Set X.left) ∧
      ∃ aE : (H ⊗ Over.mk (E.ι ≫ X.hom)).left ⟶ E.toScheme,
        aE ≫ E.ι = ((H ◁ Over.homMk E.ι) ≫ γ[H, X]).left := by
  sorry

end AlgebraicGeometry
