/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.FiniteCompactProetale
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# A small skeleton of constructible finite-Tor complexes generates its localizing closure

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-brown-hypotheses,
sk-lem-brown-hypotheses-generation.md and its proof
(blueprint: det-brown-hypotheses-generation).

Compactness is the explicit canonical map of `CategoryTheory.IsCompactObject`, written
in the ambient ordinary derived category. The closure is full and its coproducts are
ambient coproducts by `localizingClosure_exists`, so this is precisely compactness inside
the closure. Index types use the fixed small universe `u + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProEtale

open scoped CategoryTheory.Obj ZeroObject

namespace WeilConjectures

open Classical in
/-- A small set of isomorphism-class representatives of `Dctf(X, Λ)` consists of compact
objects in its localizing closure and detects zero objects by all integer-shifted Homs.
The six alternatives in `hΛ` are ring-object isomorphisms to the actual condensed rings.
The last one uses finite-subextension-valued sections. The coefficient algebraic closure
is the fixed `PadicAlgCl ℓ`, and finite extensions are its finite intermediate fields.
`g` takes its values in the recorded full bounded constructible finite-Tor category;
`hG` gives every isomorphism class and `hG_skeletal` gives one representative per class.

The first conclusion writes the canonical direct-sum Hom map of
`CategoryTheory.IsCompactObject` with ambient morphisms and coprojections. Clause (1) of
`det-def-localizing-closure-existence` supplies these small coproducts, and clause (2)
puts them in the full closure. Thus the coproduct binder does not impose a new existence
hypothesis. The second conclusion uses ambient shifts and zero: fullness and repleteness
identify this with the same assertion inside the closure.

Source: blueprint main-20261015, sk-lem-brown-hypotheses-generation.md and .proof.md
(blueprint: det-brown-hypotheses-generation).

Proof plan (the node's seven steps):
1. For finite discrete coefficients, apply det-ctf-finite-compact-proetale to each
representative, which belongs to Dctf by its type.
2. Finite type gives a finite affine cover. Separatedness makes its intersections affine
(lem-weil-pbc-separated-affine-open-intersection), hence quasi-compact; the criterion
lem-weil-pbc-quasi-separated-affine-cover-criterion makes X qcqs. For E and Qbar,
sk-thm-sfb-qlbar-two-colimit(4) identifies Dctf with Dbc. Their intersection-defined
closures agree (det-def-localizing-closure-existence). By det-ambient-ind-derived-sums(3)
the closure lies in Dic. Apply sk-thm-constructible-compactness to each representative
and every small family in the closure. Its canonical Hom map is the displayed map,
since the inclusion is full and coproducts are ambient. E = Q_l includes Q_l.
3. For O_E, det-def-localizing-closure-ctf-equals-bc(2) identifies Dctf and Dbc on qcqs X.
Apply det-prop-int-compactness-compact(3), whose ordinary unbounded ambient category and
pulled-back valuation-topology ring are exactly ours. Its canonical Hom map gives
compactness; E = Q_l includes Z_l. No completion condition is used.
4. For K with the stated vanishing let S be the objects M of the closure for which
every map M[n] to K vanishes. It contains zero, is replete and shift-stable, and contains
Dctf: use hG to replace any constructible finite-Tor object by a representative.
5. In a distinguished triangle U to V to W to U[1] with U,V in S, shift by n using
TR2 of def-weil-triangulated-category (three rotations per shift, including inverse
rotations). The signs are (-1)^n. By lem-weil-pbc-hom-out-of-triangle-exact(ii), any
map W[n] to K factors through U[n+1], hence is zero. The closure contains W by its
triangulation and repleteness. Reverse rotation gives middle-object closure too.
6. For a small family M_i in S, shift equivalence identifies Hom((sum M_i)[n], K)
with Hom(sum M_i, K[-n]), hence with the product of Hom(M_i[n], K). All factors vanish.
The empty coproduct is included, so S is closed under all small ambient sums.
7. By minimality in det-def-localizing-closure-existence(2), S contains the entire
closure. In particular id_K = 0, using n = 0. The zero maps K to 0 and 0 to K are
inverse: their composite on K is id_K, and zero has a unique endomorphism. -/
theorem brownHypothesesGeneration
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (G : Type (u + 1)) (g : G → ConstantModelConstructibleFiniteTor Λ X)
    (hG : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj))
    (hG_skeletal : ∀ i j : G, Nonempty ((g i).obj ≅ (g j).obj) → i = j) :
    (∀ (i : G) (I : Type (u + 1))
      (E : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      [HasCoproduct E],
      (∀ j : I, localizingClosureProEtale Λ X (E j)) →
        Function.Bijective
          (DirectSum.toAddMonoid
            (fun j : I ↦ Preadditive.rightComp (g i).obj (Sigma.ι E j)) :
            (⨁ j : I, ((g i).obj ⟶ E j)) →+ ((g i).obj ⟶ ∐ E))) ∧
    (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
      (∀ (i : G) (n : ℤ), Subsingleton ((g i).obj⟦n⟧ ⟶ K)) →
        Nonempty (K ≅ 0)) := by
  sorry

end WeilConjectures
