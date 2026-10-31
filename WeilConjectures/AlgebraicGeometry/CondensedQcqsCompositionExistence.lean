/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionFormal
import WeilConjectures.AlgebraicGeometry.QcqsCompositionCoreExistence
import WeilConjectures.AlgebraicGeometry.QcqsCompositionCoreShift

/-! # Existence interfaces for qcqs condensed compact-support composition

Source: Stacks Tag 0F7J and the qcqs compactification tower construction
(blueprint: lem-zl-qcqs-composition-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Normalized qcqs compactification comparisons with shift and triangle compatibility.
This isolates the geometric construction from its formal exactness and Weil consequences.
Source: Stacks Tag 0F7J, compatible compactification triangles and common refinements;
latest blueprint lem-zl-shriek-composition.proof and sk-thm-sf-comp-composition
(blueprint: lem-zl-qcqs-composition-existence).

Proof:
1. Base change the two separated finite-type maps. Their sources and targets remain finite
   type and quasi-separated over the geometric field. The boundedness theorem supplies their
   compactifications and preservation of ordinary Dbc. Choose a compactification (i,q) of g.
   The compatible-triangle theorem supplies a proper map p over its ambient scheme and an open
   a from X. Pulling back along i gives an open b, a proper r and an open j from X, with
   b j = a, r j = h and p b = i r. All opens are quasi-compact. The tower compactifications
   of h and gh are (j,r) and (a,qp). Properness, finite type and qcqs permanence place every
   scheme needed by the proper/open calculus in its stated class, without absolute separatedness.
2. Apply Gamma from condensed-open-proper-pasting to p b = i r. Whisker Gamma by Rq and j_!,
   then compose with the canonical proper and open compositors. This gives the compositor from
   Rq_* i_! Rr_* j_! to R(qp)_* a_!. The open-adjunction transpose of Gamma is inverse
   restriction. Thus the uniqueness clause of condensed-proper-open-interchange identifies it
   with the specified normalized interchange, invertible on Dctf = Dbc. The boundedness theorem
   restricts the resulting functors and natural isomorphism to Dbc. The qcqs shift calculus gives
   compatibility with the canonical shifts, and naturality gives the image-triangle squares.
3. For a proper refinement v from d to c, use Gamma for v j_d = j_c followed by the proper
   compositor to construct rho_v from the compact-support expression at c to the one at d.
   The same transpose calculation identifies this with the prescribed refinement transformation
   CompactificationReindexing.refinement. Gamma is invertible on Dbc by the same normalized
   interchange theorem. Identity and pasting give rho_id = id and the refinement cocycle.
   Define comparison(c,d) using a common refinement and the inverse of its second rho. A further
   common refinement cancels by invertibility, proving independence of this choice and the
   comparison cocycle. On a compatible tower, properOpen_tower_refinement identifies the two
   compositor expressions through these three exterior comparisons. Common refining towers
   therefore extend the compositor to arbitrary compactifications and prove its independence.
   Its tower normalization is precisely the transpose characterization in step 2.
4. For each of h, g and gh, pull a compactification back along the target automorphism.
   The Cartesian automorphism square identifies the source pullback with the original source.
   Compose the proper exchange, the normalized open exchange, the exact-to-total-derived
   pullback identifications, and the comparison from step 3. This is the specified expression
   exchangeComponent. The isomorphism-square and open-exchange theorems give invertibility.
   The mixed cube, applied to the identity-source square defining a refinement, proves that
   exchange commutes with rho. Common refinements then prove independence of the model.
   The qcqs calculus gives shift compatibility of these specified factors; naturality gives
   compatibility with the connecting maps as well as the first two image-triangle squares.
5. Pull the tower of step 1 back by the target automorphism, using the compatible-tower theorem.
   Expand its compositor and the three exchanges by steps 2 and 4. The ambient mate formulas
   cancel adjacent units and counits by the triangle identities; open-exchange pasting cancels
   the exterior open factors. The remaining middle square is exactly the mixed-cube equation
   of condensed-open-proper-pasting. Whisker it by the exterior proper image and j_!, then insert
   the proper and open compositors. Its two sides are the two sides of comp_exchange.
   The independence from steps 3 and 4 removes the tower and model choices. This proves an
   equality of global derived morphisms. Collect the three Systems, compositor, independence,
   normalized exchanges and this equation into Comparisons; their shift and triangle
   compatibilities give ShiftCompatibility. -/
theorem qcqsCompositionDataExists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated] :
    ∃ A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀),
      ShiftCompatibility ℓ A := by
  obtain ⟨A⟩ := qcqsCompositionCoreExists ℓ D hℓ h₀ g₀
  exact ⟨A, qcqsCompositionCoreShift ℓ D hℓ h₀ g₀ A⟩


end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
