/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.RelativeSectionAlgebraCanonicalMap
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Sheaf.AlgebraicGeometry.SectionAlgebraOpenCoverDescent
import Sheaf.AlgebraicGeometry.SectionAlgebraCanonicalMapOpenDescent

/-! # Gluing the canonical section-algebra map to relative Proj

Source: Stacks Project, Morphisms, Tag 01VJ, section-algebra and canonical-map paragraphs
of (3) implies (5); Constructions, Tag 01O9(3)
(blueprint: lem-trf-canonical-proj-open-cover-gluing).

The existing `RelativeSectionAlgebra` presents the actual direct-image tensor powers on
an affine basis. The open comparison below fixes its graded maps on every homogeneous
section by restriction and the normalized tensor-pullback unit. Thus it identifies the
adjunction evaluations, rather than merely unrelated graded algebras or Proj schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict a homogeneous section to an open base change, using the actual section
`1 ⊗ s` and the canonical tensor-power comparison, including degree zero.
Source: Stacks, Tag 01VJ, (3) implies (5), and Tag 01O9(3)
(blueprint: lem-trf-canonical-proj-open-cover-gluing). -/
def canonicalSectionOpenPull {Z S : Scheme.{u}} (h : Z ⟶ S) (N : Z.Modules)
    (U : S.Opens) (V : S.affineOpens) (W : U.toScheme.affineOpens)
    (hle : W.1 ≤ U.ι ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(N.tensorPow n, h ⁻¹ᵁ V.1)) :
    Γ(((tensorPullback (h ⁻¹ᵁ U).ι).obj N).tensorPow n, (h ∣_ U) ⁻¹ᵁ W.1) :=
  (((tensorPullback (h ⁻¹ᵁ U).ι).obj N).tensorPow n).val.map
    (homOfLE (by
      intro x hx
      change h ((h ⁻¹ᵁ U).ι x) ∈ V.1
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι]
      exact hle hx)).op
    ((boundaryPullbackPowIso (h ⁻¹ᵁ U).ι N n).hom.app _
      (tensorPullbackSection (h ⁻¹ᵁ U).ι (N.tensorPow n) (h ⁻¹ᵁ V.1) s))

/-- The canonical graded isomorphism from the restriction of the global section algebra
to the local section algebra. `PullbackData` asserts coefficientwise base change; since
`U.ι` is an open inclusion, this is precisely an isomorphism on restricted sheaves.
The section equation fixes it in every degree, including the scalar/unit degree zero.
The adjunction evaluations are thereby identified on every local tensor generator:
both send `a ⊗ s` to `a` times the section displayed on the right.
Source: Stacks, Tag 01VJ, (3) implies (5); Tag 01O9(3)
(blueprint: lem-trf-canonical-proj-open-cover-gluing). -/
structure RelativeSectionAlgebra.OpenComparison {Z S : Scheme.{u}} {h : Z ⟶ S}
    {N : Z.Modules} (A : RelativeSectionAlgebra h N) (U : S.Opens)
    (B : RelativeSectionAlgebra (h ∣_ U) ((tensorPullback (h ⁻¹ᵁ U).ι).obj N)) where
  data : Scheme.GradedAlgebraData.PullbackData U.ι A.data B.data
  section_eq (V : S.affineOpens) (W : U.toScheme.affineOpens)
      (hle : W.1 ≤ U.ι ⁻¹ᵁ V.1) (n : ℕ) (a : A.data.grading V n) :
    B.sectionEquiv W n ⟨data.map hle a, (data.map hle).map_mem a.property⟩ =
      canonicalSectionOpenPull h N U V W hle n (A.sectionEquiv V n a)

/-- Canonical section algebras, adjunction evaluations, generation loci and Proj maps
are compatible with an affine open cover. If every local generation locus is full and
the local canonical maps are open immersions, the global canonical map is an everywhere
defined open immersion. The normalization in `OpenComparison.section_eq` specifies the
graded isomorphisms and the evaluation comparisons; its `data.relProjIsoPullback` is the
canonical Proj restriction isomorphism. The final equation identifies the canonical maps
under these isomorphisms. Full local and global generation identifies their loci as well.

Source: Stacks, Morphisms, Tag 01VJ, section-algebra and canonical-map paragraphs in
(3) implies (5); Constructions, Tag 01O9(3)
(blueprint: lem-trf-canonical-proj-open-cover-gluing).

Proof:
1. On every open contained in U_i, direct-image sections are the sections on the same
inverse-image open. Restriction preserves sheaf tensor powers, including the structure
module in degree zero, and sheaf coproducts. These identities preserve multiplication
and unit, satisfy the overlap cocycle, and give the normalized graded comparisons.
Local quasi-coherence of the given algebras implies global quasi-coherence by the
 affine-neighbourhood definition (pqf-def-coherent). This constructs A in the existing
quasi-coherent affine-basis presentation (def-weil-pbc-graded-sheaf-structures and
def-weil-pbc-quasi-coherent-algebra).
2. The normalized tensor-pullback adjunction evaluates a tensor a ⊗ s as a times the
restricted section. The formula is unchanged on an open base restriction; the same
is true in every degree. Hence the graded comparisons identify the evaluations
(def-pc-module-pullback and def-pur-sheaf-tensor-product).
3. Relative Proj exists and commutes with open base change
(lemma-nagata-relative-proj-exists and lemma-nagata-relative-proj-base-change-arbitrary).
Apply the scheme clause of lem-trf-space-line-module-proj-map to the identified
evaluations. Generation loci and the canonical maps restrict to the local ones.
The local loci are full and the inverse-image opens cover Z, so the global locus is
full and the canonical map r is defined on Z. The same comparison gives the displayed
map equation.
4. Since r is over S, two points with the same image have the same base point. Choose
one U_i containing it; both points lie in Z_i and injectivity of r_i makes them equal.
On every Z_i, r is the composite of r_i with the Proj comparison open immersion.
Thus r is injective and locally on its source an open immersion, so apply
lem-weil-pbc-open-immersion-injective-local-source. Empty schemes and empty covers
are allowed, and intersections of affine base opens need not be affine. -/
theorem canonical_proj_open_cover_gluing {Z S : Scheme.{u}} (h : Z ⟶ S)
    [QuasiCompact h] [IsSeparated h] (N : Z.Modules) [N.IsInvertible]
    {I : Type v} (U : I → S.Opens) (_hU : ∀ i : I, IsAffineOpen (U i))
    (_hcover : iSup U = ⊤)
    (A_local : ∀ i : I, RelativeSectionAlgebra (h ∣_ U i)
      ((tensorPullback (h ⁻¹ᵁ U i).ι).obj N))
    (_hgen : ∀ i : I, (A_local i).GeneratesEverywhere)
    (r_local : ∀ i : I, (h ⁻¹ᵁ U i).toScheme ⟶ (A_local i).data.relProj)
    (_hcanonical : ∀ i : I, (A_local i).IsCanonicalMap (r_local i))
    (_hopen : ∀ i : I, IsOpenImmersion (r_local i)) :
    ∃ A : RelativeSectionAlgebra h N, A.GeneratesEverywhere ∧
      ∃ r : Z ⟶ A.data.relProj, A.IsCanonicalMap r ∧ IsOpenImmersion r ∧
        ∀ i : I, ∃ D : A.OpenComparison (U i) (A_local i),
          (h ⁻¹ᵁ U i).ι ≫ r = r_local i ≫ D.data.relProjComparison := by
  classical
  obtain ⟨A, hA⟩ := exists_section_algebra_open_cover_descent h N U _hU _hcover A_local
  choose D hD using hA
  obtain ⟨hgen, r, hr, hres⟩ := section_canonical_map_open_descent h N U _hU _hcover
    A A_local D hD _hgen r_local _hcanonical
  have hcomparison (i : I) : IsOpenImmersion (D i).relProjComparison :=
    MorphismProperty.of_isPullback (D i).isPullback.flip inferInstance
  have hlocal (i : I) : IsOpenImmersion ((h ⁻¹ᵁ U i).ι ≫ r) := by
    rw [hres i]
    have := _hopen i
    have := hcomparison i
    infer_instance
  have hmem (x : Z) : ∃ i : I, h x ∈ U i := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [_hcover]
    trivial
  have hinj : Function.Injective r := by
    intro x y hxy
    obtain ⟨i, hx⟩ := hmem x
    have hbase : h x = h y := by
      rw [← hr.1]
      simpa only [Scheme.Hom.comp_apply] using congrArg A.data.relProjHom hxy
    have hy : h y ∈ U i := hbase ▸ hx
    let x' : (h ⁻¹ᵁ U i).toScheme := ⟨x, hx⟩
    let y' : (h ⁻¹ᵁ U i).toScheme := ⟨y, hy⟩
    have := hlocal i
    have he : ((h ⁻¹ᵁ U i).ι ≫ r) x' = ((h ⁻¹ᵁ U i).ι ≫ r) y' := hxy
    exact congrArg Subtype.val (((h ⁻¹ᵁ U i).ι ≫ r).isOpenEmbedding.injective he)
  have hopen : IsOpenImmersion r := by
    apply IsOpenImmersion.of_forall_source_exists r hinj
    intro x
    obtain ⟨i, hx⟩ := hmem x
    refine ⟨(h ⁻¹ᵁ U i).toScheme, (h ⁻¹ᵁ U i).ι, inferInstance, ?_, hlocal i⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨A, hgen, r, hr, hopen, ?_⟩
  intro i
  exact ⟨⟨D i, hD i⟩, hres i⟩

end AlgebraicGeometry.Scheme.Modules
