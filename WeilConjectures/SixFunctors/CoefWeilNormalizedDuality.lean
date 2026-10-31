/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefVerdierWeilData

/-! # Normalized Weil structures on completed coefficient duality

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1--3
(blueprint: lem-coef-weil-normalized-duality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- There is a completed coefficient duality, identified with its actual internal Hom
and exceptional dualizing object, with scalar-compatible Weil duality structures.
The dualizing Frobenius is normalized by the structure-morphism mate at finite and
common coefficients. This assertion concerns one scheme and contains no relative
exceptional adjunction for a general morphism.

The duality is existential: the interface `CoefQbarVerdier.Duality` pins the signed
symmetry of its finite data only on literal K-flat pairs, so its biduality may be
twisted by a locally constant sign that geometric Frobenius does not preserve (for
X₀ = Spec 𝔽_{q²}, whose two geometric points Frobenius exchanges); for such data no
Weil structure has equivariant biduality. The duality is taken from the normalized
construction, whose symmetry is the natural Koszul swap.

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1--3
(blueprint: lem-coef-weil-normalized-duality).

Proof: construct B, its internal-Hom identification and its dualizing identification
by the normalized coefficient construction of thm-coef-qbar-verdier, with the natural
signed symmetry at every finite field. Then apply the inverse-Frobenius pullback
equivalence at every rational field and
at the common coefficient stage. At the structure morphism form the right mate of
inverse compact-support Frobenius exchange. Its invertibility follows from the mate
lemma along equivalences. Apply this mate to the coefficient unit, with its canonical
pullback identification, and transport along the exceptional-unit identification of
the specified dualizing object. The tensor unit equation fixes the coefficient-unit
structure; uniqueness of right-adjoint transpose makes the resulting dualizing
structure independent of compactification. The same argument applied to the actual
scalar compact-support counit makes the dualizing comparisons equivariant.

Compose the internal-Hom pullback comparison with internal Hom of this dualizing
structure, and conjugate through the given internal-Hom identification. For a Weil
object use the inverse of its structure in the contravariant Hom slot. Naturality
proves the equation on Weil morphisms. The evaluation normalization proves evaluation
equivariance. Transpose the evaluation after signed symmetry to obtain equivariance
of the actual biduality map; injectivity of the tensor-Hom transpose gives equality.
The scalar tensor and Hom comparisons are evaluation-normalized, so their two
Frobenius routes have equal transposes. This proves both finite scalar and stage
comparison squares, using rational structure maps without any integral lattice.
At the common stage these are the same finite-origin operations: represent each
finite set of maps and equations at a common coefficient field, apply the rational
equalities, and use scalar compatibility for independence under enlargement. -/
theorem coef_weil_normalized_duality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    ∃ B : CoefVerdierWeil.FiberDuality D l hl Ω X₀,
      Nonempty (CoefVerdierWeil.FiberInternalHom D l hl Ω X₀ B) ∧
      CoefVerdierWeil.FiberDualizing D l hl Ω X₀ B ∧
      ∃ W : CoefVerdierWeil.Coefficients D l hl Ω X₀ B,
        CoefVerdierWeil.DualizingNormalization D l hl Ω X₀ B W := by sorry

end WeilConjectures
