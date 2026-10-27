/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import WeilConjectures.Topology.SpectralClosedRestriction
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-!
# Zariski degree-zero comparison for a proper scheme over a henselian pair

Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B
(blueprint: lem-weil-pbc-zariski-h0-proper-henselian-pair).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopologicalSpace

-- The same-universe open-set transport used in
-- WeilConjectures.Topology.EmbeddingPushforwardTransport.
private theorem homeomorph_opens_dense
    {T U : Type u} [TopologicalSpace T] [TopologicalSpace U] (e : T ≃ₜ U) :
    e.opensCongr.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology U) := by
  let E := e.opensCongr.equivalence
  change E.functor.IsDenseSubsite _ _
  refine { functorPushforward_mem_iff := ?_ }
  intro V R
  constructor
  · intro h x hx
    have hx' : e x ∈ E.functor.obj V := by
      change e.symm (e x) ∈ V
      simpa using hx
    obtain ⟨W, f, ⟨N, g, k, hg, _⟩, hw⟩ := h (e x) hx'
    refine ⟨N, g, hg, ?_⟩
    have hn := k.le hw
    change e.symm (e x) ∈ N at hn
    simpa using hn
  · intro h y hy
    change e.symm y ∈ V at hy
    obtain ⟨W, f, hf, hw⟩ := h (e.symm y) hy
    refine ⟨E.functor.obj W, E.functor.map f, ?_, hw⟩
    exact ⟨W, f, 𝟙 _, hf, (Category.id_comp _).symm⟩

-- The image part of ClosedEmbeddingRestrictionTransport, at Type u rather than
-- Type (u + 1). The ambient space and its sheaf stay fixed, so only the image
-- homeomorphism and the inverse-mate unit equation are needed.
private theorem bijective_restriction_of_embedding
    {T U : TopCat.{u}} [SpectralSpace T] (i : U ⟶ T)
    (hi : Topology.IsClosedEmbedding i)
    (hc : ∀ x : T, ConnectedSpace (↥(Set.range i ∩ closure ({x} : Set T))))
    (F : T.Sheaf (Type u)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom.app
        (op ⊤)) := by
  let D : Set T := Set.range i
  let j : TopCat.of D ⟶ T := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let h : D ≃ₜ U := hi.isEmbedding.toHomeomorph.symm
  let H := h.symm.opensCongr.equivalence
  have : H.inverse.IsDenseSubsite
      (Opens.grothendieckTopology D) (Opens.grothendieckTopology U) :=
    homeomorph_opens_dense h
  let S := H.sheafCongr (Opens.grothendieckTopology U)
    (Opens.grothendieckTopology D) (Type u)
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i
  let B := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) j
  let r : TopCat.Sheaf.pushforward (Type u) i ⋙ 𝟭 _ ≅
      S.functor ⋙ TopCat.Sheaf.pushforward (Type u) j :=
    NatIso.ofComponents (fun G ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro G G' f
      rfl)
  let α := (mateEquiv A B).symm
    (TwoSquare.mk _ S.functor (𝟭 _) _ r.hom)
  have : IsIso α.natTrans := isIso_inverseMate_of_equivalences A B r
  have hu := unit_mateEquiv_symm A B
    (TwoSquare.mk _ S.functor (𝟭 _) _ r.hom) F
  change A.unit.app F ≫ (r.app _).hom =
    B.unit.app F ≫ (TopCat.Sheaf.pushforward (Type u) j).map (α.app F) at hu
  have heq : A.unit.app F = B.unit.app F ≫
      (TopCat.Sheaf.pushforward (Type u) j).map (α.app F) ≫ (r.app _).inv := by
    rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hb := TopCat.spectral_closed_restriction T D hi.isClosed_range hc F
  have he := congrArg (fun f ↦ f.hom.app (op ⊤)) heq
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso ((r.app _).inv.hom.app (op ⊤))).comp
    ((ConcreteCategory.bijective_of_isIso
      (((TopCat.Sheaf.pushforward (Type u) j).map (α.app F)).hom.app (op ⊤))).comp hb)

namespace AlgebraicGeometry

/-- For a proper scheme over a henselian pair, sections of any sheaf of sets are
unchanged on the closed fibre.
Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B
(blueprint: lem-weil-pbc-zariski-h0-proper-henselian-pair).

Proof (the six steps of the node):
1. The quotient spectrum map is a closed immersion, as is its base change
   (`lem-weil-pbc-spec-quotient-closed-immersion`,
   `lem-weil-pbc-closed-immersion-base-change`). Fibre-product points identify its image
   with the inverse image of V(I) (`lem-weil-pbc-fibre-product-points`). Properness over
   an affine base makes X quasi-compact and quasi-separated, hence spectral
   (`lem-weil-pbc-qcqs-over-affine`, `lem-weil-pbc-qcqs-scheme-spectral`, Tag 094L).
2. The spectral restriction criterion (`lem-weil-pbc-h0-spectral-closed-restriction`,
   Tag 09ZG) reduces bijectivity to connectedness of the closed fibre intersected with
   the closure of every point of X.
3. Realize that closure as an irreducible closed subscheme Y
   (`lem-weil-pbc-closed-subset-closed-subscheme`). Its composite map to Spec A is proper
   (`lem-weil-pbc-proper-fp-permanence`), and its closed fibre is homeomorphic to the
   required intersection.
4. Factor Y through Spec B by Stein factorization
   (`def-weil-pbc-stein-factorization`, `lem-weil-pbc-stein-factorization-affine`, Tag 03H2).
   The first map is proper with connected nonempty fibres, A to B is integral, and
   (B, IB) is henselian (`lem-weil-pbc-integral-over-henselian-pair`, Tag 09XK).
5. The image of Y in Spec B is closed and irreducible, hence V(q) for a prime q
   (`lem-weil-pbc-scheme-sober`). Its intersection with V(IB) is V(q + IB), connected
   and nonempty (`lem-weil-pbc-henselian-pair-prime-connected`, Tag 09Y6).
6. The closed fibre of Y maps surjectively and closedly onto V(q + IB), with connected
   fibres. This gives a quotient map, so its source is connected
   (`lem-weil-pbc-connected-fibres-quotient-preimage-connected`, Tag 0377).
   Step 3 identifies the intersection, and Step 2 proves the assertion.

The displayed map is the global component of the unit of the inverse-image adjunction
`TopCat.Sheaf.pullbackPushforwardAdjunction` (STATE INVERSE IMAGE, Type u), the form of
`lem-weil-pbc-h0-spectral-closed-restriction`: the colimit coprojection followed by
sheafification, the restriction map specified in the node.
-/
theorem zariski_h0_proper_henselian_pair
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f] :
    ∀ (𝓕 : TopCat.Sheaf (Type u) X),
      Function.Bijective
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
          (pullback.fst f
            (Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)).op)).base).unit.app
              𝓕).hom.app (op ⊤)) := by
  classical
  let q := Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)).op
  let i : pullback f q ⟶ X := pullback.fst f q
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of A) I
  have : IsClosedImmersion i := inferInstance
  have hrange : Set.range i = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [Scheme.Pullback.range_fst]
    change f ⁻¹' Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp only [Ideal.mk_ker]
  obtain ⟨hspectral, _, hconnected⟩ :=
    f.spectralSpace_and_isClosed_and_isConnected_inter I
  let : SpectralSpace X := hspectral
  have hc (x : X) : ConnectedSpace (↥(Set.range i ∩ closure ({x} : Set X))) := by
    apply isConnected_iff_connectedSpace.mp
    rw [Set.inter_comm, hrange]
    exact hconnected _ isClosed_closure isIrreducible_singleton.closure
  intro F
  exact bijective_restriction_of_embedding i.base i.isClosedEmbedding hc F

end AlgebraicGeometry
