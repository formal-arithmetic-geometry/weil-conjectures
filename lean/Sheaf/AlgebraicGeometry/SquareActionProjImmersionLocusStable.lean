/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent
import Sheaf.AlgebraicGeometry.ProjCanonicalMapTwistComparison
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import WeilConjectures.AlgebraicGeometry.AmpleIso

/-! # Stability of the target-open immersion locus of a section-ring morphism

Source: Guo, Divisors on coherent schemes and homogeneous spaces, section 6.1 and
Proposition 6.2(iii), printed pp.14--15, March 31, 2026 version.
(blueprint: lem-sfb-square-action-proj-immersion-locus-stable)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules

/-- Translation on the base change, with coordinates `(b, x) ↦ (b, g(b) • x)`.
The product is the chosen scheme fibre product in `Over S`, with its factors reversed
from the notation `X_B`; its second projection pulls the module back from `X`.
Source: Guo, section 6.1, translation in Proposition 6.2.
(blueprint: lem-sfb-square-action-proj-immersion-locus-stable) -/
def squareActionTranslation {S : Scheme.{u}} (H X : Over S) [GrpObj H] [ModObj H X]
    (B : Over S) (g : B ⟶ H) : (B ⊗ X).left ⟶ (B ⊗ X).left :=
  (lift (fst B X) (lift (fst B X ≫ g) (snd B X) ≫ γ[H, X])).left

/-- The canonical section-ring map has a group-stable target-open immersion locus,
and the line bundle is absolutely ample on every quasi-compact open in its preimage.
Source: Guo, section 6.1 and Proposition 6.2(iii), printed pp.14--15.
(blueprint: lem-sfb-square-action-proj-immersion-locus-stable)

Proof plan:
1. On a smooth affine test base B, smooth base change and open restriction are smooth,
   hence flat, locally finitely presented and open (lem-pc-proper-base-change,
   lem-weil-pbc-smooth-restrict-open-subschemes, lem-pc-smooth-flat,
   lem-weil-pbc-flat-lfp-open). Pulling back admissible target opens shows that the
   inverse image of P₀ lies in the target-open immersion locus Q_B.
2. For an admissible open V in P_B, its image I in P is open. The smooth surjection
   V → I is fpqc: over each affine open in I finitely many affine neighborhoods in V
   suffice, by affine quasi-compactness (def-weil-pbc-fpqc-covering,
   lem-weil-pbc-affine-scheme-qcqs). Descend the open immersion over V by
   lem-galois-fpqc-descend-open-immersion. Thus Q_B is exactly the pullback of P₀.
3. The neighborhood isomorphism of lem-sfb-square-action-proj-translation-extension
   transports admissible opens and their inverse images under r_B. Intersect with
   its domain first; this leaves the inverse image unchanged. Conjugation by that
   isomorphism and the translation preserves open immersions. Apply this also to
   the inverse translation to obtain equality of the source loci.
4. Cover H by affine opens B and use the universal element B → H. These smooth test
   bases show that the action on H × W has image in W. The unit section supplies
   the reverse inclusion, so the image on all underlying points is exactly W.
5. The restrictions of r over admissible target opens glue to an open immersion of
   W into P, since their inverses agree on overlaps (def-weil-open-immersion).
   A quasi-compact open T in W is therefore isomorphic to a quasi-compact open U in P.
6. Restrict sections to T. The restricted chart formulas are the canonical ones of
   lem-sc-ample-proj-canonical-map. Apply lem-trf-proj-canonical-map-twist-comparison
   and lem-trf-proj-qc-open-twist-ample; a common positive multiple m gives both an
   ample twist on U and its pullback identification with (M|T)^{⊗m}.
7. Transport affine nonvanishing neighborhoods through T ≅ U and use lem-sc-ample-iso.
   Finally a section of ((M|T)^{⊗m})^{⊗n} is a section in positive degree mn of M|T.
   Thus the same affine neighborhoods verify def-weil-pbc-ample-invertible-module
   for M|T itself. Its quasi-compactness is assumed; the empty T is included.

The chart conditions are exactly the characterization of the canonical map in
lem-sc-ample-proj-canonical-map. The square condition asserts only existence of an
invertible base module and a module isomorphism, with no chosen coherent data.
The final image is taken on the inverse image of W under the second projection;
this is the underlying open subscheme H ×_S W of H ×_S X. -/
theorem squareAction_proj_immersion_locus_stable
    (S : Scheme.{u}) [IsAffine S]
    (H X : Over S) [GrpObj H] [ModObj H X]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFinitePresentation H.hom]
    [QuasiCompact H.hom] (hconnected : ∀ s : S, ConnectedSpace (H.hom.fiber s))
    [IsSeparated X.hom] [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]
    (M : X.left.Modules) [M.IsInvertible]
    (hsquare : ∀ (B : Over S) (g h : B ⟶ H),
      ∃ N : B.left.Modules, N.IsInvertible ∧ Nonempty
        (((tensorPullback (squareActionTranslation H X B (g * h))).obj
            ((tensorPullback (snd B X).left).obj M)) ⊗
          ((tensorPullback (snd B X).left).obj M) ≅
        (((tensorPullback (squareActionTranslation H X B g)).obj
            ((tensorPullback (snd B X).left).obj M)) ⊗
          ((tensorPullback (squareActionTranslation H X B h)).obj
            ((tensorPullback (snd B X).left).obj M))) ⊗
          ((tensorPullback (fst B X).left).obj N)))
    (hcover : ∀ x : X.left, ∃ (d : ℕ) (s : sectionRingGrade M d),
      0 < d ∧ x ∈ nonvanishingLocus (M.tensorPow d) (s.val d))
    (r : X.left ⟶ Proj (sectionRingGrade M))
    (hr : ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade M d),
      (r ⁻¹ᵁ Proj.basicOpen (sectionRingGrade M) s.val : Set X.left) =
        nonvanishingLocus (M.tensorPow d) (s.val d) ∧
      ∀ (n : ℕ) (ξ : sectionRingGrade M (n • d)),
        (r.app (Proj.basicOpen (sectionRingGrade M) s.val)
          (Proj.awayToSection (sectionRingGrade M) s.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade M) s.property n
              ξ.val ξ.property))) •
          (M.tensorPow (n • d)).presheaf.map (homOfLE
            (le_top : r ⁻¹ᵁ Proj.basicOpen (sectionRingGrade M) s.val ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (M.tensorPow (n • d)).presheaf.map (homOfLE
            (le_top : r ⁻¹ᵁ Proj.basicOpen (sectionRingGrade M) s.val ≤ ⊤)).op
          (ξ.val (n • d)))
    (P₀ : (Proj (sectionRingGrade M)).Opens)
    (hP₀ : P₀ = sSup {V | IsOpenImmersion (r ∣_ V)}) :
    (γ[H, X]).left '' ((snd H X).left ⁻¹' (r ⁻¹ᵁ P₀ : Set X.left)) =
        (r ⁻¹ᵁ P₀ : Set X.left) ∧
      ∀ (T : X.left.Opens), T ≤ r ⁻¹ᵁ P₀ → CompactSpace T.toScheme →
        @IsAmple T.toScheme (M.restrict T.ι)
          (IsInvertible.of_iso ((restrictFunctorIsoPullback T.ι).app M).symm) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
