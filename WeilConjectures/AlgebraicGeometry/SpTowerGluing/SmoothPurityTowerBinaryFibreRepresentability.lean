/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Binary fibre gluing of ordinary tower representing pairs

Source: the Gluing paragraph of det-sp-tower-gluing, with the released
fibre correction bpq #42, B. (blueprint: lem-sp-tower-binary-fibre-representability).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

/-- Two open-local representing pairs glue by the fibre of derived open direct images.
The overlap pair is available by restriction from either input. This is only the binary
step: no coordinate cover, coordinate adjunction family, or global smooth existence is
assumed or concluded.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md, Gluing;
released correction bpq #42, B
(blueprint: lem-sp-tower-binary-fibre-representability).

Proof. Pull U,V back to any open subscheme Z whose image is contained in U union V.
The input properties supply representing pairs on these two opens and their intersection.
Restrict pairs by the open adjunction and compact-support composition. Transpose their
counits to obtain the unique overlap isomorphism c, and use injectivity to prove its
counit equation. On the ringed sequence site use the subterminal derived-image calculus
for the self and cross comparisons. Form t from RjU*GU plus RjV*GV to RjW*(GV|W),
with components the restriction units followed by c and minus the restriction unit.
Choose a distinguished fibre triangle H -> P -> Q -> H[1]. On U and V its second map
has the split forms (s,-1) and (1,-s'). Exact Hom sequences show that the projections
H|U -> GU and H|V -> GV are isomorphisms. The triangle equation gives their overlap
compatibility. Exact evaluation detects common cohomological bounds. Glue the finite
constructible stratifications on U and V minus U and use open locality of the finite-ring
Tor interval at every level. Thus H is a uniformly constructible finite-Tor tower, even
though the separate derived direct images need not be bounded. Apply compact support
to the signed open-extension triangle of H. The sum of the transported local counits
annihilates its first arrow by the overlap equation. Hom-out exactness lifts that sum
to a counit on H. The open-cover Hom sequences for a test tower and all its shifts,
compared by this counit, have four exterior isomorphisms. The five lemma proves the
middle bijection. This applies to every Z and every compactification, giving the stated
open-local property. Empty and redundant opens use the same split-triangle argument. -/
theorem tower_representableOn_sup
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar]
    (hk : Finite k ∨ IsAlgClosed k) (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (K : SpTowerCalculus.C l E b q Y.left) (U V : X.left.Opens)
    (hU : TowerRepresentableOn l E b o q f.left K U)
    (hV : TowerRepresentableOn l E b o q f.left K V) :
    TowerRepresentableOn l E b o q f.left K (U ⊔ V) := by
  have _ := hk
  have _ := hne
  intro Z j _ hj g hg c
  let : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isOpenImmersion j
  let : TopologicalSpace.NoetherianSpace Z := j.isOpenEmbedding.isInducing.noetherianSpace
  let : CompactSpace Z := TopologicalSpace.NoetherianSpace.compactSpace Z
  let : IsNoetherian Z := ⟨⟩
  let : QuasiCompact j := quasiCompact_of_noetherianSpace_source j
  let X' : Over (Spec (.of k)) := Over.mk (j ≫ X.hom)
  let : IsSeparated X'.hom := (inferInstance : IsSeparated (j ≫ X.hom))
  let : LocallyOfFiniteType X'.hom :=
    (inferInstance : LocallyOfFiniteType (j ≫ X.hom))
  let : QuasiCompact X'.hom := (inferInstance : QuasiCompact (j ≫ X.hom))
  let g' : X' ⟶ Y := Over.homMk g (by
    change g ≫ Y.hom = j ≫ X.hom
    rw [← hg, Category.assoc, Over.w f])
  let U' := j ⁻¹ᵁ U
  let V' := j ⁻¹ᵁ V
  have hcover : U' ⊔ V' = ⊤ := by
    apply top_unique
    intro x hx
    exact hj ⟨x, rfl⟩
  obtain ⟨HU, epsU, hrepU⟩ := hU U'.toScheme (U'.ι ≫ j) (by
    rintro x ⟨w, rfl⟩
    exact w.property) (U'.ι ≫ g) (by simp only [Category.assoc, hg])
      (c.precomp U'.ι)
  obtain ⟨HV, epsV, hrepV⟩ := hV V'.toScheme (V'.ι ≫ j) (by
    rintro x ⟨w, rfl⟩
    exact w.property) (V'.ι ≫ g) (by simp only [Category.assoc, hg])
      (c.precomp V'.ι)
  exact tower_binary_pair_gluing l E b o q k z h cal X' Y g' c K U' V' hcover
    HU HV epsU epsV hrepU hrepV

end AlgebraicGeometry.ProEtale.SpTowerGluing
