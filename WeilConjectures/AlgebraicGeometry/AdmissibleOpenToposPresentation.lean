/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleModificationPresentationData

/-! # The open and topos part of admissible modifications
Source: ILO XX 4.4, printed pp.373–374.
(blueprint: lem-per-admissible-open-topos-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The geometric part of the presentation, before any coefficient sheaf or
spectral sequence is introduced. There is no completion comparison in this datum.
Source: ILO XX 4.4, printed page 373.
(blueprint: lem-per-admissible-open-topos-presentation). -/
structure AdmissibleOpenToposPresentation {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (CommRingCat.of A)).Opens) where
  C : Type (u + 1)
  [smallC : SmallCategory C]
  τ : GrothendieckTopology C
  topos : AdmissibleToposPresentation I C τ
  opens : AdmissibleOpenEmbeddings I U

attribute [instance] AdmissibleOpenToposPresentation.smallC

/-- Full-support blowups admit their common open and a presenting limit site.
Source: ILO XX 4.4, printed page 373, the paragraph before (**).
(blueprint: lem-per-admissible-open-topos-presentation).

Proof: The admissible-modification-system theorem supplies a nonempty directed
preorder of full-support finitely generated ideals and the schematically dense
open U in every blowup. Every blowup is proper over Spec A. Two morphisms over
Spec A agree on U and hence agree everywhere by schematic density and separatedness.
Thus the actual category of modifications is thin and cofiltered. The blowup is
an isomorphism over U, so its inverse there gives the cartesian open embedding;
uniqueness over U makes these embeddings natural under domination. The closed
fibres are proper over Spec(A/I), and hence qcqs. A transition is proper: its graph
is a closed immersion, and the projection from the product of two proper schemes
is proper. The same holds after restricting to the closed fibres. Apply the qcqs
etale-topos inverse-limit theorem to this small cofiltered diagram. Its finite-cover
colimit site and continuous projection functors give the required site; their
canonical composition comparisons are coherent on sheaves with any coefficients.
The theorem supplies the two-dimensional limit property and a conservative family
of compatible geometric points, which gives precisely the conservativity field.
Retaining all ideals instead of a skeleton changes none of these properties.
-/
theorem admissibleOpenToposPresentation
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : ∀ x : PrimeSpectrum A, x ∈ U ↔ x ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    Nonempty (AdmissibleOpenToposPresentation I U) := by sorry

end

end AlgebraicGeometry
