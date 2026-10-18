module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.SixFunctors.BrownHypothesesAmbient
import Sheaf.Paper.BrownHypothesesGeneration
import Sheaf.SixFunctors.BrownHypothesesSmall

/-!
# Hypotheses of Brown representability

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md
(blueprint: sk-lem-brown-hypotheses).

`BrownHypothesesFor` bundles the conclusion, using the canonical full-subcategory shift.
`brownHypotheses` asserts it for the standing scheme and the six admissible coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- The conclusions of the Brown-hypotheses lemma, for a specified coefficient ring.
The localizing closure and constructible finite-Tor property are the recorded definitions.
All size assertions and coproducts use the fixed indexing universe `u + 1`. The existential
triangulation witness installs the canonical shift inherited from the ambient derived
category; no independently chosen shift is allowed. The coproduct witness also precedes
compactness and generation, so these clauses cannot be vacuous for lack of coproducts.
This is only a bundle of the lemma's conclusions, not an assertion for arbitrary rings.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md, conclusion
(blueprint: sk-lem-brown-hypotheses). -/
def BrownHypothesesFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  let S := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  LocallySmall.{u + 1} L.FullSubcategory ∧
    ∃ hTri : L.IsTriangulated,
      letI := hTri
      L.IsClosedUnderIsomorphisms ∧
        S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        IsIdempotentComplete L.FullSubcategory ∧
        ∃ hSums : HasCoproducts.{u + 1} L.FullSubcategory,
          letI := hSums
          ∀ (G : Type (u + 1)) [Category.{u + 1} G] (e : G ≌ S.FullSubcategory)
            (hL : ∀ g : G, L (e.functor.obj g).1),
            (∀ g : G, IsCompactObject
              (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory)) ∧
            IsTriangulatedGeneratingFamily
              (fun g : G ↦ (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory))

/-- Brown representability hypotheses for a separated finite-type scheme in positive
characteristic different from the coefficient prime, for exactly the admissible rings.
`IsLocalizingAdmissibleCoefficient` specifies the six concrete coefficient objects up to
ring-object isomorphism, including the discrete finite rings killed by a power of `ℓ`.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md and sk-lem-brown-hypotheses.proof.md
(blueprint: sk-lem-brown-hypotheses).

Proof: First unpack sk-def-sfb-dc-setting: the datum is a prime ℓ, a field of
characteristic p > 0 distinct from ℓ, and a separated finite-type k-scheme X.
Unpack sk-def-localizing-closure: Λ is one of the six specified condensed rings;
the ambient category is the unbounded derived category of modules over Λ_X;
S is the bounded constructible finite-Tor property and L is its replete localizing
intersection, with coproducts in the fixed universe and no completeness restriction.
Second apply det-brown-hypotheses-ambient to this datum to obtain local smallness,
triangulation, arbitrary sums and split idempotents of L. Apply
 det-brown-hypotheses-small to obtain thickness and essential smallness of S.
Choosing one representative per isomorphism class gives a small skeleton.
Third let G be any such skeleton and apply det-brown-hypotheses-generation:
each representative is compact in L, and vanishing of Hom(C[n], K) for all
representatives C and all integers n forces K to be zero. Compactness is exactly
def-pc-compact-object. To identify the second conclusion with def-pc-generators,
use Hom(coproduct C, K[-n]) = product Hom(C[n], K). If every morphism from the
coproduct into every shift of K is zero, the component Hom groups vanish,
so K is zero; contrapositively every nonzero K receives a nonzero map from the
coproduct into some shift. This is IsTriangulatedGeneratingFamily. All these
arguments apply to every small skeleton, with the inherited shift and any chosen
coproduct universal properties. -/
theorem brownHypotheses
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  sorry

end CategoryTheory
