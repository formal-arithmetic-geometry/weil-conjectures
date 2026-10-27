/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogIdealAlgebraizationData

import Sheaf.AlgebraicGeometry.LogIdealImageExistence
import Sheaf.AlgebraicGeometry.LogIdealImageChartFormula
import Sheaf.AlgebraicGeometry.LogIdealImageStrictEtale
import Sheaf.AlgebraicGeometry.IdealTensorPullbackComparison

/-!
# Algebraization of a coherent logarithmic ideal

Source: ILO, Exposé VIII 3.3.7 and 3.4.2; Stacks, Tags 01IB, 01IC, 03DX and 05VG
(blueprint: lem-trf-log-ideal-algebraization-descent).

Image ideals are described by local membership at geometric stalks, rather than
by the generally incorrect sectionwise span. The map into the structure sheaf is
the actual tensor pullback of the ideal inclusion followed by the canonical
structure-sheaf comparison. All comparisons below are normalized by this map.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.IdealSheafData.toModules
attribute [local irreducible] Scheme.IdealSheafData.toModulesι

private theorem exists_ideal_eq_iso {X : Scheme.{u}} {J L : X.IdealSheafData}
    (h : J = L) :
    ∃ e : J.toModules ≅ L.toModules, e.hom ≫ L.toModulesι = J.toModulesι := by
  subst L
  exact ⟨Iso.refl _, Category.id_comp _⟩

private theorem canonical_etale_ideal_descent {X : Scheme.{u}} (K : X.IdealSheafData) :
    HasCanonicalEtaleIdealDescent.{u, v} K := by
  classical
  intro ι U L hL
  have hr (a : ι) (V : X.Etale) (f : V ⟶ U a) :
      (L a).comap f.left = K.comap V.hom := by
    rw [hL a, ← Scheme.IdealSheafData.comap_comp]
    have hw : f.left ≫ (U a).hom = V.hom := f.w
    exact congrArg (fun k : V.left ⟶ X ↦ K.comap k) hw
  have hex (a b : ι) (V : X.Etale) (f : V ⟶ U a) (g : V ⟶ U b) :
      ∃ e : ((L a).comap f.left).toModules ≅ ((L b).comap g.left).toModules,
        e.hom ≫ ((L b).comap g.left).toModulesι =
          ((L a).comap f.left).toModulesι :=
    exists_ideal_eq_iso ((hr a V f).trans (hr b V g).symm)
  choose e he using hex
  refine ⟨e, he, ?_, ?_, hr, ?_⟩
  · intro a V f
    apply Iso.ext
    apply (cancel_mono ((L a).comap f.left).toModulesι).1
    exact (he a a V f f).trans
      (Category.id_comp (((L a).comap f.left).toModulesι)).symm
  · intro a b c V f g h
    apply (cancel_mono ((L c).comap h.left).toModulesι).1
    calc
      ((e a b V f g).hom ≫ (e b c V g h).hom) ≫ ((L c).comap h.left).toModulesι =
          (e a b V f g).hom ≫
            ((e b c V g h).hom ≫ ((L c).comap h.left).toModulesι) :=
        Category.assoc _ _ _
      _ = (e a b V f g).hom ≫ ((L b).comap g.left).toModulesι :=
        congrArg (fun k ↦ (e a b V f g).hom ≫ k) (he b c V g h)
      _ = ((L a).comap f.left).toModulesι := he a b V f g
      _ = (e a c V f h).hom ≫ ((L c).comap h.left).toModulesι :=
        (he a c V f h).symm
  · intro a b V f g q hq
    apply Iso.ext
    apply (cancel_mono ((L b).comap g.left).toModulesι).1
    exact hq.trans (he a b V f g).symm

private theorem etale_ideal_tensor_comparison {X Y : Scheme.{u}}
    (K : X.IdealSheafData) (f : Y ⟶ X) [Etale f] :
    ∃! e : (Scheme.Modules.tensorPullback f).obj K.toModules ≅ (K.comap f).toModules,
      e.hom ≫ (K.comap f).toModulesι = logIdealTensorInclusion K f := by
  obtain ⟨d, hd, _⟩ := existsUnique_idealTensorPullbackComparison f K
  have : IsIso d := hd.2.2 inferInstance
  refine ⟨asIso d, hd.1, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_mono (K.comap f).toModulesι).1
  exact he.trans hd.1.symm

/-- A nonempty coherent ideal on a fine log scheme algebraizes uniquely to a finite-type
quasi-coherent ideal, with the affine tilde formula, canonical effective descent and strict
étale base change, all respecting inclusions and structural image ideals.
Source: ILO VIII 3.3.7, 3.4.2; Stacks, Tags 01IB, 01IC, 03DX, 05VG and 0GN7
(blueprint: lem-trf-log-ideal-algebraization-descent).

Proof:
1. On a fine chart with finite generators `E`, every ideal germ is `e*m`; its structural
image is `α(e)α(m)`. Thus the sheaf image is the image of the finite free map with
coefficients `α(e)`, using local membership, never global lifting of image sections.
2. The Zariski image of the same free map is quasi-coherent by
`lem-weil-pbc-quasi-coherent-module-cokernel-image`. Its affine sections are the chart ring
ideal, and the tilde counit identifies the inclusion by naturality
(`lem-weil-pbc-affine-tilde-gamma-adjunction`). Association preserves the free epimorphism
by `lem-trf-etale-extension-free-presentations-hom` and preserves the image inclusion by
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`.
3. These charts show site quasi-coherence. Apply
`lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` and its inverse, restriction to
opens, to the image ideal and its inclusion. This gives a genuine ideal subsheaf `K` and
uniqueness as an ideal, not only an isomorphism class. The finite-type comparison reflects
the finite free local epimorphisms. No coherence or Noetherian hypothesis is used.
4. The natural restriction comparison and full faithfulness give the chart formula with
its inclusion. On double overlaps both restrictions have the same inclusion in the
structure sheaf; the unique inclusion-preserving isomorphisms give the transitions.
Cancellation against that monomorphism gives naturality, diagonal identity and cocycle.
The global ideal `K` realizes these data, even when overlaps are nonaffine.
5. Under a strict étale map the log structure is the associated inverse image, and the
pulled-back finite generators generate the pulled-back log ideal. Their structural images
generate exactly the restricted image ideal. Apply the inverse equivalence on the source
to identify the pulled-back ideal with its algebraization. Inclusion normalizations also
preserve the chart identifications and all descent transitions and their compositions. -/
theorem logIdeal_algebraization_descent {X : Scheme.{u}} (M : EtaleLogStructure X)
    (hM : M.IsFine) (I : M.IdealFamily) (hI : M.IsNonemptyFineCoherentIdeal I) :
    ∃ K : X.IdealSheafData,
      Scheme.Modules.IsQuasiCoherentFiniteType K.toModules ∧
      M.IsImageIdealAlgebraization I K ∧
      (∀ L : X.IdealSheafData, M.IsImageIdealAlgebraization I L → L = K) ∧
      M.HasImageIdealChartFormula I K ∧ HasCanonicalEtaleIdealDescent.{u, v} K ∧
      (∀ W : X.Etale,
        ∃! e : (Scheme.Modules.tensorPullback W.hom).obj K.toModules ≅
            (K.comap W.hom).toModules,
          e.hom ≫ (K.comap W.hom).toModulesι = logIdealTensorInclusion K W.hom) ∧
      ∀ (Y : Scheme.{u}) (N : EtaleLogStructure Y) (f : EtaleLogMap N M),
        f.IsStrictEtale →
          N.IsFine ∧ N.IsNonemptyFineCoherentIdeal (f.pullbackIdeal I) ∧
          Scheme.Modules.IsQuasiCoherentFiniteType (K.comap f.base).toModules ∧
          N.IsImageIdealAlgebraization (f.pullbackIdeal I) (K.comap f.base) ∧
          (∀ L : Y.IdealSheafData,
            N.IsImageIdealAlgebraization (f.pullbackIdeal I) L → L = K.comap f.base) ∧
          N.HasImageIdealChartFormula (f.pullbackIdeal I) (K.comap f.base) ∧
          HasCanonicalEtaleIdealDescent.{u, v} (K.comap f.base) ∧
          (∀ (hf : Etale f.base) (V : Y.Etale),
            N.imageIdealSections (f.pullbackIdeal I) V =
              M.imageIdealSections I
                (@Scheme.Etale.mk X V.left (V.hom ≫ f.base) (by
                  have := hf
                  infer_instance))) ∧
          (∃! e : (Scheme.Modules.tensorPullback f.base).obj K.toModules ≅
              (K.comap f.base).toModules,
            e.hom ≫ (K.comap f.base).toModulesι = logIdealTensorInclusion K f.base) := by
  obtain ⟨K, hKft, hK, huniq⟩ := logIdeal_image_exists_unique M hM I hI
  refine ⟨K, hKft, hK, huniq, logIdeal_image_chart_formula M I K hK,
    canonical_etale_ideal_descent K, ?_, ?_⟩
  · intro W
    exact etale_ideal_tensor_comparison K W.hom
  · intro Y N f hf
    obtain ⟨hN, hNI, hNK, hsections⟩ :=
      logIdeal_image_strict_etale M hM I hI K hK N f hf
    obtain ⟨L, hLft, hL, hLuniq⟩ :=
      logIdeal_image_exists_unique N hN (f.pullbackIdeal I) hNI
    have hKL : K.comap f.base = L := hLuniq _ hNK
    have hft : Scheme.Modules.IsQuasiCoherentFiniteType (K.comap f.base).toModules := by
      rw [hKL]
      exact hLft
    have hsourceuniq (J : Y.IdealSheafData)
        (hJ : N.IsImageIdealAlgebraization (f.pullbackIdeal I) J) :
        J = K.comap f.base := (hLuniq J hJ).trans hKL.symm
    have : Etale f.base := hf.choose
    exact ⟨hN, hNI, hft, hNK, hsourceuniq,
      logIdeal_image_chart_formula N (f.pullbackIdeal I) (K.comap f.base) hNK,
      canonical_etale_ideal_descent (K.comap f.base), hsections,
      etale_ideal_tensor_comparison K f.base⟩

end AlgebraicGeometry
