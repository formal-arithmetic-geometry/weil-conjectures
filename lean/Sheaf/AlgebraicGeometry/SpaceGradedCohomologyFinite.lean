module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Finite graded cohomology on proper algebraic spaces

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08AT, lemma-graded-finiteness;
Tag 073E, lemma-colimits (blueprint: lem-sfb-space-graded-cohomology-finite).

The pulled-back graded algebra is encoded by its homogeneous constant-section action.
An O-linear additive action of B_k, with the scalar and product laws below, extends
uniquely to the tensor pullback of the associated algebra: locally send c tensor b to
c times mu(b). Conversely a module over that tensor pullback gives exactly these maps.
Local O-spans of constant homogeneous multiples therefore express precisely local
finite generation over that algebra, including coefficients that are only locally
finite sums of pure tensors. No choice of an auxiliary algebra or of its action occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Underlying-additive cohomology of a homogeneous module piece. This is Mathlib's
abelian sheaf cohomology after restriction to the existing small affine étale model.
Source: Stacks, Tags 08AT, 073E and 039Z
(blueprint: lem-sfb-space-graded-cohomology-finite). -/
abbrev gradedCohomologyPiece {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G : X.Modules) (q : ℕ) : Type u :=
  Sheaf.H ((SheafOfModules.toSheaf X.smallStructureRings).obj
    (X.smallModuleRestriction.obj G)) q

/-- Graded cohomology is finite for the specified homogeneous multiplication action.
Source: Stacks, Cohomology of Algebraic Spaces, Tags 08AT and 073E
(blueprint: lem-sfb-space-graded-cohomology-finite).

The finite-sum identity in the conclusion is the convolution formula: collecting
terms with r+k=d gives its degree-d component. Both inputs range through arbitrary
finite sums. The scalar law includes a=1, hence the unit, and identifies the degree-zero
A-action with multiplication by the actual pullback of a on every étale chart.

Proof:
1. Forget the grading on the sheaf direct sum of G_r. It is quasi-coherent by
lem-sfb-space-qcoh-kernels-colimits. Extend the homogeneous actions by finite sums and
sheafification. The displayed local generators make this ungraded module finite type
because sections of a sheaf direct sum are locally finite homogeneous sums.
2. Form Y = X times_(Spec A) Spec B. The ring B is Noetherian by
lem-weil-pbc-finite-type-algebra-noetherian, and Y is proper over Spec B by
lem-sfb-space-proper-base-change. The chart test in def-sfb-space-morphism-properties
and pqf-lem-locnoeth-lft make Y locally Noetherian. Properness over an affine scheme
also makes X and Y quasi-compact and quasi-separated, using their closed relative
diagonals and the quasi-compact diagonal of the affine base.
3. By lem-sfb-space-relative-spec-correspondence, Y is the relative spectrum of the
pulled-back algebra. Apply lem-sfb-space-affine-module-correspondence to obtain a
quasi-coherent F on Y with p_*F equal to the ungraded direct sum, respecting the action.
4. On affine étale generator charts the finite free surjection corresponds to a finite
free surjection on Y. Cokernels remain quasi-coherent by
lem-sfb-space-qcoh-kernels-colimits, so the equivalence detects these epimorphisms.
Thus F is finite type. Apply pqf-lem-coherent-ft-locnoeth on charts and
lem-sfb-space-qcoh-groupoid-equivalence to make F coherent.
5. By lem-sfb-space-proper-coherent-higher-images its higher image on Spec B is coherent.
Its sections are finite B-modules. Apply lem-sfb-space-affine-base-higher-image-sections
and lem-sfb-ringed-site-global-module-abelian-cohomology, naturally in F and in scalar
multiplications, to deduce that additive H^q(Y,F) is finite over B.
6. The affine comparison lem-sfb-space-affine-cohomology identifies H^q(X,p_*F) with
H^q(Y,F). It respects multiplication: use naturality of
lem-sfb-ringed-site-leray-spectral-sequence and positive-row vanishing from
lem-sfb-space-affine-module-higher-image-vanishing, and the natural module/additive
comparison lem-sfb-ringed-site-global-module-abelian-cohomology.
7. Express the direct sum as the filtered colimit of its finite partial sums.
By lem-weil-pbc-module-sheaves-colimits-forgetful this remains the same colimit after
forgetting modules. Apply lem-sfb-space-cohomology-filtered-colimit and additivity on
finite sums. The resulting isomorphism from the direct sum of H^q(G_r) is characterized
on each summand by cohomology of its sheaf injection.
8. Multiplication by b in B_k carries the r-th injection to the (r+k)-th injection
composed with mu(r,k,b). Functoriality of additive cohomology gives the homogeneous
formula. Expand both finite inputs to obtain the displayed convolution identity.
The product, unit and additive laws make this a B-module action, with the stated
A-normalization. Pull a finite set of generators back through the B-linear comparison.
-/
theorem space_graded_cohomology_finite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {b c : B}, b ∈ graded k → c ∈ graded l → b * c ∈ graded (k + l))
    (hscalar : ∀ a : A, algebraMap A B a ∈ graded 0)
    {S : Scheme.{u}} (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) (hf : MapIsProper f)
    (G : ℕ → X.Modules) (hG : ∀ r : ℕ, (G r).IsQuasicoherent)
    (mu : ∀ r k : ℕ, graded k → (G r ⟶ G (r + k)))
    (hadd : ∀ (r k : ℕ) (b c : graded k), mu r k (b + c) = mu r k b + mu r k c)
    (hassoc : ∀ (r k l : ℕ) (b : graded k) (c : graded l),
      HEq (mu r l c ≫ mu (r + l) k b)
        (mu r (k + l) ⟨b.val * c.val, hmul k l b.property c.property⟩))
    (hbase : ∀ (r : ℕ) (a : A) (U : X.EtaleSite) (s : (G r).val.obj (op U)),
      HEq ((mu r 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) s)
        ((((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map
          (((yoneda.preimage (U.obj.hom ≫ f.hom.hom)).left ≫ e.hom).op)).hom a) • s))
    (hfinite : ∀ U : X.EtaleSite, ∃ R : Sieve U,
      R ∈ X.etaleTopology U ∧ ∀ (V : X.EtaleSite) (i : V ⟶ U), R i →
        ∃ (n : ℕ) (d : Fin n → ℕ) (s : ∀ j : Fin n, (G (d j)).val.obj (op V)),
          ∀ (W : X.EtaleSite) (j : W ⟶ V) (r : ℕ) (t : (G r).val.obj (op W)),
            ∃ T : Sieve W, T ∈ X.etaleTopology W ∧
              ∀ (Z : X.EtaleSite) (h : Z ⟶ W), T h →
                (G r).val.map h.op t ∈ Submodule.span (X.structureSheaf.obj.obj (op Z))
                  {z | ∃ a : Fin n, d a ≤ r ∧ ∃ b : graded (r - d a),
                    HEq z ((mu (d a) (r - d a) b).val.app (op Z)
                      ((G (d a)).val.map (h ≫ j).op (s a)))})
    (q : ℕ) :
    ∃ mod : Module B (DirectSum ℕ (fun r ↦ gradedCohomologyPiece X (G r) q)),
      (∀ (K R : Finset ℕ) (b : ∀ k : ℕ, graded k)
        (x : ∀ r : ℕ, gradedCohomologyPiece X (G r) q),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          (∑ k ∈ K, (b k).val)
          (∑ r ∈ R, DirectSum.of (fun t ↦ gradedCohomologyPiece X (G t) q) r (x r)) =
        ∑ k ∈ K, ∑ r ∈ R,
          DirectSum.of (fun t ↦ gradedCohomologyPiece X (G t) q) (r + k)
            (Sheaf.H.map ((X.smallModuleRestriction ⋙
              SheafOfModules.toSheaf X.smallStructureRings).map (mu r k (b k))) q (x r))) ∧
      @Module.Finite B _ _ _ mod := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
