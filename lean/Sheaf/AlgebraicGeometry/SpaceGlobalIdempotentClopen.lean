/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.Idempotent
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Global idempotents and clopen subspaces of an algebraic space

Source: Stacks Project, Spaces over Fields, Tag 0DMY, proof (2), idempotent paragraph;
Properties of Spaces, Tag 03BZ (blueprint: lem-sfb-space-global-idempotent-clopen).

Global functions are the compatible families of regular functions on the existing small
étale site, using Mathlib's `RingCat.sectionsSubring`. No atlas is part of the data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Compatible regular functions inherit pointwise commutativity from the chart rings.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: lem-sfb-space-global-idempotent-clopen). -/
instance structureSectionsCommRing {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CommRing (RingCat.sectionsSubring X.structurePresheaf) :=
  @Subring.toCommRing (∀ T : X.EtaleSiteᵒᵖ, Scheme.Γ.obj (op (X.etaleForget.obj T.unop)))
    inferInstance (RingCat.sectionsSubring X.structurePresheaf)

/-- Idempotent global regular functions correspond to open subspaces with closed point
image. These images are exactly the clopens, with unique open-subspace structure. On
an affine étale chart the pullback is the principal open of the restricted function.
The inverse function is one on the subspace and zero on its complement, expressed by
its germs on every scheme chart. The last four clauses give the Boolean identities
as equalities of subfunctors, hence of open subspaces. No finiteness or nonemptiness
hypothesis is required.

Source: Stacks Project, Spaces over Fields, Tag 0DMY, proof (2), idempotent paragraph;
Properties of Spaces, Tag 03BZ (blueprint: lem-sfb-space-global-idempotent-clopen).

Proof:
1. Choose a surjective étale scheme atlas P → X. The equalizer description of
   lem-trf-space-enlarged-etale-ringed-site-model identifies global functions with
   functions on P agreeing on R = P ×_X P; restriction to P is injective. Restrict an
   idempotent e to a on P and apply lem-weil-pbc-scheme-clopen-idempotent. Its clopen
   V has equal inverse images under the two projections from R.
2. By lem-a1-space-point-open-calculus, points with the same atlas image lift to R.
   Thus the inverse image of C = |p|(V) is V. The open surjective atlas point map
   (lem-a1-space-etale-open-image) makes C and its complement open. The open-subspace
   classification gives the unique U_e with image C. Apply the same calculation on
   P ×_X T for any scheme chart T. Surjectivity over T gives the chart formula, which
   is D(e|_T) on Spec B by lem-weil-pbc-spec-clopen-idempotent.
3. Conversely pull a clopen C and its complement back to P. The scheme correspondence
   gives the unique idempotent a equal to one on V and zero off V. Its two restrictions
   to R have the same clopen and are equal by scheme injectivity. The equalizer descends
   a to a unique e. Atlas injectivity proves idempotence. The chart formula identifies
   its image with C and its restrictions with one and zero on the complementary opens.
4. Equal open subspaces give equal atlas clopens, hence equal atlas idempotents, hence
   equal global functions. This proves the bijection and the inverse description.
   The uniqueness of the open-subspace structure is Tag 03BZ. Sheaf uniqueness on the
   two complementary opens also gives uniqueness of the section with these values.
5. Compute zero, one, complement and product on P. Idempotent germs are zero or one,
   so the loci are empty, full, complementary and intersected, respectively. Atlas
   point-surjectivity descends these identities, and open-subspace uniqueness makes
   them identities of subfunctors. This uses no finiteness assumptions. For empty X,
   the empty-cover sheaf axiom makes the global ring the zero ring; its sole idempotent
   corresponds to the sole open subspace, and all formulas remain valid. -/
theorem global_idempotent_clopen {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ E : {e : RingCat.sectionsSubring X.structurePresheaf // IsIdempotentElem e} ≃
        {U : OpenSubspace X // IsClosed (pointImage U.val.ι)},
      (∀ U : {U : OpenSubspace X // IsClosed (pointImage U.val.ι)},
        IsClopen (pointImage U.val.val.ι)) ∧
      (∀ C : Set (Point X.obj.obj), IsClopen C →
        ∃! U : OpenSubspace X, pointImage U.val.ι = C) ∧
      (∀ (e : {e : RingCat.sectionsSubring X.structurePresheaf // IsIdempotentElem e})
        (B : CommRingCat.{u}) (p : Spec B ⟶ S)
        (a : yoneda.obj (Over.mk p) ⟶ X.obj.obj) (ha : IsEtale a),
        schemePointMap a ⁻¹' pointImage (E e).val.val.ι =
          (PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso B).hom
            (e.val.val (op ⟨CostructuredArrow.mk a, ha⟩)))).carrier) ∧
      (∀ (U : {U : OpenSubspace X // IsClosed (pointImage U.val.ι)})
        (T : X.EtaleSite) (x : X.etaleForget.obj T),
        (schemePointMap T.obj.hom x ∈ pointImage U.val.val.ι →
          (X.etaleForget.obj T).presheaf.Γgerm x ((E.symm U).val.val (op T)) = 1) ∧
        (schemePointMap T.obj.hom x ∉ pointImage U.val.val.ι →
          (X.etaleForget.obj T).presheaf.Γgerm x ((E.symm U).val.val (op T)) = 0)) ∧
      (E 0).val.val = ⊥ ∧
      (E 1).val.val = ⊤ ∧
      (∀ e : {e : RingCat.sectionsSubring X.structurePresheaf // IsIdempotentElem e},
        pointImage (E ⟨1 - e.val, e.property.one_sub⟩).val.val.ι =
          (pointImage (E e).val.val.ι)ᶜ) ∧
      (∀ e f : {e : RingCat.sectionsSubring X.structurePresheaf // IsIdempotentElem e},
        (E ⟨e.val * f.val, e.property.mul f.property⟩).val.val =
          (E e).val.val ⊓ (E f).val.val) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
