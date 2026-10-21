/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
import Mathlib.Topology.Separation.Profinite

/-!
# Clopen inverse images and spectral connected-component spaces

Source: agent consequence of Stacks Project, `topology.tex`, Tags 0906
(lemma-spectral-pi0), 005F (lemma-connected-component-intersection), and 08ZZ
(lemma-profinite-refine-open-covering)
(blueprint: lem-sfb-spectral-clopen-component-homeomorphism).
-/

@[expose] public section

universe u v

/-- A continuous map of spectral spaces whose inverse-image map on clopens is bijective
induces a homeomorphism of connected-component quotients, normalized by the quotient maps.
No nonemptiness assumption is imposed.

Source: agent consequence of Stacks Project, `topology.tex`, Tags 0906
(lemma-spectral-pi0), 005F (lemma-connected-component-intersection), and 08ZZ
(lemma-profinite-refine-open-covering)
(blueprint: lem-sfb-spectral-clopen-component-homeomorphism).

Proof for stage 3:
1. A continuous map sends each connected component into a connected component. The induced
map `h = hf.connectedComponentsMap` satisfies `h ∘ q_T = q_S ∘ f`; the quotient topology
makes it continuous, and surjectivity of `q_T` makes it the unique normalized map.
2. By `lem-pe-spectral-components-profinite`, both component quotients are compact Hausdorff
and totally disconnected. Apply `lem-weil-pbc-profinite-clopen-basis` to both quotients.
3. Every clopen of any space is a union of its connected components. Thus inverse image
under the quotient map bijects the clopens of the quotient with the clopens of the space:
the inverse sends a saturated clopen to its image, which is clopen by the quotient topology.
The normalization conjugates the given clopen-preimage bijection to that of `h`.
4. Distinct points of the source quotient can be separated by a clopen, using the clopen
basis. Express that clopen as an inverse image under `h`; its two points must have distinct
images. Hence `h` is injective.
5. If a point `y` of the target quotient is outside the image, choose around every image
point a clopen excluding `y`. Their inverse images cover the compact source quotient, so
finitely many suffice. Their finite union `V` excludes `y` but contains the image. Thus
`h` has equal inverse images of `V` and the whole target, contradicting injectivity on
clopens. This argument permits the empty finite cover when the source is empty.
6. Every clopen of the source quotient is `h`-preimage of a target clopen. Bijectivity of
`h` identifies its image with that target clopen. The clopen basis then shows `h` is open,
so its inverse is continuous. This proves the homeomorphism and the stated normalization.
If the target quotient is empty, the existence of `h` forces the source quotient empty. -/
theorem isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage
    {T : Type u} {S : Type v} [TopologicalSpace T] [TopologicalSpace S]
    [SpectralSpace T] [SpectralSpace S] {f : T → S} (hf : Continuous f)
    (hclop : Function.Bijective
      (fun U : TopologicalSpace.Clopens S ↦
        (⟨f ⁻¹' (U : Set S), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens T))) :
    IsHomeomorph hf.connectedComponentsMap ∧
      hf.connectedComponentsMap ∘ (ConnectedComponents.mk : T → ConnectedComponents T) =
        (ConnectedComponents.mk : S → ConnectedComponents S) ∘ f := by
  sorry
