/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Irreducible
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.DeligneLaumon.EtaleUnibranchLocalDomain
import Mathlib.Topology.Compactness.Compact

/-! # Etale schemes over geometrically unibranch integral schemes

Source: Stacks Project, more-morphisms.tex, Tag 0GS9, proof of
lemma-global-unramified-dominant-unibranch-is-etale (finite-component paragraph with
Descent, Tag 0BAL, and the geometrically-unibranch paragraph), with the domain-reduction
paragraph of More on Algebra, Tag 0GSC
(blueprint: lem-dl-a1-etale-unibranch-finite-components).

## Main statements

* `AlgebraicGeometry.etale_unibranch_finite_components`: for an etale `g : U ⟶ X` over
  an integral scheme whose local rings are geometrically unibranch, every quasi-compact
  open of `U` has finitely many irreducible components, and every point of `U` lies on
  at most one irreducible component of `U`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

open Set Topology

private theorem component_eq_closure_of_irreducible_open
    {T : Type*} [TopologicalSpace T] {V C : Set T}
    (hVo : IsOpen V) (hVi : IsIrreducible V)
    (hC : C ∈ irreducibleComponents T) (hne : (C ∩ V).Nonempty) :
    C = closure V := by
  have hsub : C ⊆ closure V :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hVo hne).trans
      (closure_mono inter_subset_right)
  exact hsub.antisymm (hC.2 hVi.closure hsub)

private theorem finite_components_of_compact_locally_irreducible
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (hlocal : ∀ x : T, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ IsIrreducible V) :
    (irreducibleComponents T).Finite := by
  classical
  choose V hVo hxV hVi using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hxV x⟩)
  let t : Finset (Set T) := s.image (fun x ↦ closure (V x))
  have htclosed : ∀ C ∈ t, IsClosed C := by
    intro C hC
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hC
    exact isClosed_closure
  have htcover : (univ : Set T) ⊆ ⋃₀ (t : Set (Set T)) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_sUnion.mpr ⟨closure (V i), Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      subset_closure hxi⟩
  apply t.finite_toSet.subset
  intro C hC
  obtain ⟨D, hDt, hCD⟩ := isIrreducible_iff_sUnion_isClosed.mp hC.1 t htclosed
    ((subset_univ C).trans htcover)
  obtain ⟨i, hi, hDi⟩ := Finset.mem_image.mp hDt
  have hDi' : IsIrreducible D := hDi ▸ (hVi i).closure
  have heq : C = D := hCD.antisymm (hC.2 hDi' hCD)
  exact heq.symm ▸ hDt

/-- An etale scheme over an integral geometrically unibranch scheme has finitely many
irreducible components on every quasi-compact open, and at most one component through
any point. Geometric unibranchness of `X` is the hypothesis `hgeom`: for every point `x`
the spectrum of every strict henselization of the stalk `𝒪_{X,x}` (relative to a
separable closure of its residue field) is irreducible.

Source: Stacks Project, More on Morphisms, Tag 0GS9, the proof of
`lemma-global-unramified-dominant-unibranch-is-etale`; the finite-component paragraph
uses Descent, Tag 0BAL, and the local domain neighbourhoods come from the
domain-reduction paragraph of More on Algebra, Tag 0GSC
(blueprint: lem-dl-a1-etale-unibranch-finite-components).

Proof, using `lem-dl-a1-etale-unibranch-local-domain`:
1. Every point has an affine open neighbourhood with domain coordinate ring. The
   affine isomorphism with its spectrum makes this neighbourhood irreducible.
2. If an irreducible component `C` meets an irreducible open `V`, then `C ∩ V` is
   dense in `C`, so `C ⊆ closure V`. Since `closure V` is irreducible, maximality
   gives `C = closure V`. Two components through a point therefore coincide.
3. For a compact open `W`, intersect the neighbourhoods from step 1 with `W`.
   These are irreducible open neighbourhoods in `W`, since a nonempty open subset
   of an irreducible space is irreducible.
4. Choose a finite subcover by compactness. The closures of its members form a
   finite irreducible closed cover of `W`. Every irreducible component of `W` is
   contained in one member of this finite closed cover; maximality makes it equal
   to that member. Thus the set of components is finite.
-/
theorem etale_unibranch_finite_components
    {X U : Scheme.{u}} [IsIntegral X]
    (hgeom : ∀ (x : X) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [Algebra (X.presheaf.stalk x) K]
      [IsScalarTower (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) K]
      [CommRing H] [Algebra (X.presheaf.stalk x) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (X.presheaf.stalk x) K H →
        IrreducibleSpace (PrimeSpectrum H))
    (g : U ⟶ X) [Etale g] :
    (∀ W : U.Opens, IsCompact (W : Set U) →
      (irreducibleComponents W).Finite) ∧
      (∀ u : U, ∀ C D : Set U,
        C ∈ irreducibleComponents U → D ∈ irreducibleComponents U →
          u ∈ C → u ∈ D → C = D) := by
  classical
  have hlocal : ∀ x : U, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
    intro x
    obtain ⟨V, hV, hxV, hdom⟩ := etale_unibranch_local_domain hgeom g x
    have : IsDomain Γ(U, V) := hdom
    have : IrreducibleSpace V :=
      hV.isoSpec.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
    exact ⟨V, V.isOpen, hxV,
      isIrreducible_iff_irreducibleSpace.mpr ‹IrreducibleSpace V›⟩
  constructor
  · intro W hW
    have : CompactSpace W := isCompact_iff_compactSpace.mp hW
    apply finite_components_of_compact_locally_irreducible
    intro x
    obtain ⟨V, hVo, hxV, hVi⟩ := hlocal x.val
    refine ⟨Subtype.val ⁻¹' V, hVo.preimage continuous_subtype_val, hxV, ?_⟩
    exact hVi.preimage W.isOpen.isOpenEmbedding_subtypeVal
      ⟨x.val, hxV, ⟨x, rfl⟩⟩
  · intro x C D hC hD hxC hxD
    obtain ⟨V, hVo, hxV, hVi⟩ := hlocal x
    exact (component_eq_closure_of_irreducible_open hVo hVi hC ⟨x, hxC, hxV⟩).trans
      (component_eq_closure_of_irreducible_open hVo hVi hD ⟨x, hxD, hxV⟩).symm

end AlgebraicGeometry
