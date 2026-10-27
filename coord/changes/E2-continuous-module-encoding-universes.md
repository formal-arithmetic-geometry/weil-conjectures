# continuousModuleEncodingUniverses

## Reason

Ordinary local-model and scalar-extension comparison lemmas must refer to the exact
encodings used by IntegralScalarConstructibleImage. Keeping those encodings in the
module whose proof imports these lemmas would create an import cycle. Move the seven
existing definitions and proved instances into a common publicly imported module.
No coefficient construction, statement, universe, visibility, instance attribute or
body changes. No adopted source-library file changes.

## Old

In `lean/Sheaf/Paper/IntegralScalarConstructibleImage.lean`, in namespace
`AlgebraicGeometry.ProEtale.CondensedRing`:

```lean
def continuousRingModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) ≌
      SheafOfModules.{u + 1, u, u + 1, u + 1} (continuousCoefficientRingSheaf X T) := by
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ by
      exact @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} T
  let φ := ContinuousRingUniverse.comparison X T
  letI := ContinuousRingUniverse.comparison_isIso X T
  exact (Mod.comapEquivalenceOfIsIso (inv φ)).trans
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A).trans
      (ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm))

/-- The two section-ring presentations agree by the identity on continuous functions.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def continuousSectionRingIso (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    latticeModuleRing X T ≅ continuousCoefficientRingSheaf X T :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The same encoding in the existing commutative coefficient-sheaf coordinates.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def continuousLatticeModuleEquivalenceUniverse (X : Scheme.{u}) (T : Type u)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :=
  (continuousRingModuleEquivalenceUniverse X T).trans
    (ringModuleEquivalenceOfIso X (continuousSectionRingIso X T))

/-- The field encoding has the specified continuous section action.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 00YV.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def continuousFieldModuleEquivalenceUniverse (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    (X : Scheme.{u}) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  continuousLatticeModuleEquivalenceUniverse X E

/-- The integral encoding in completed coordinates, transported along the supplied
coefficient isomorphism. Consumers specify that isomorphism by every residue projection.
Source: Bhatt--Scholze, Lemma 6.8.2(1) and Section 6.8; Stacks Project, Tag 00YV.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def completedContinuousModuleEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  (continuousLatticeModuleEquivalenceUniverse X
    (Padic.coefficientExtensionIntegers l E)).trans
    (ringModuleEquivalenceOfIso X ((Scheme.adicLisseForget X).mapIso c))

/-- The inverse completed integral encoding is additive.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image).
Proof: each of the three equivalences leaves the additive section maps unchanged;
restriction along a ring isomorphism does likewise. Hence sums of arrows are preserved. -/
instance completedContinuousModuleEquivalence_inverse_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)) :
    (completedContinuousModuleEquivalence l E X c).inverse.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The inverse field encoding is additive.
Source: Stacks Project, Tag 00YV; Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image).
Proof: the section-action equivalence is the identity on additive sheaf maps, as is
transport along the reconstructed section-ring isomorphism. Ring restriction also
preserves addition of maps. Their composite and inverse therefore preserve addition. -/
instance continuousFieldModuleEquivalenceUniverse_inverse_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] (X : Scheme.{u}) :
    (continuousFieldModuleEquivalenceUniverse l E X).inverse.Additive := by
  exact Functor.additive_of_preserves_binary_products _

```

## New

The identical declarations above are in
`lean/Sheaf/Paper/ContinuousModuleEncodingUniverses.lean`, with their existing
public visibility. Only their documentation's blueprint ownership changes.
`IntegralScalarConstructibleImage.lean` publicly reexports them with:

```lean
public import Sheaf.Paper.ContinuousModuleEncodingUniverses
```

That module publicly imports every original statement dependency of the moved block.
The four continuous equivalences retain their existing ownership node
`def-sfb-continuous-coefficient-module-equivalence-universe`, with its Lean module
updated. The completed equivalence and two proved additivity instances are recorded
in the new definition node
`def-weil-pbc-completed-continuous-module-encoding-universes`.
No target statement or the meaning of any definition changes; no statement review
is reopened on mathematical grounds by this location-only change.

## Users

`tools/downstream.py` and a textual source search found:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralScalarConstructibleImage | E2 | Uses the same declarations through the public import; its theorem signature is identical. |
| Sheaf.Paper.EmbeddedLatticeCoefficientComparison | V9 | Uses continuousFieldModuleEquivalenceUniverse. Public import and exact body/signature preserved; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModelEncodingUniverses | new, E2 delivery | States the ordinary model comparison using the completed inverse encoding. |
| Sheaf.Paper.ContinuousScalarEncodingUniverses | new, E2 delivery | States the ordinary exact scalar square using the same two inverse encodings. |

There are no forced adaptations and no changes to the V9 module. The unchanged
consumer is checked against the delivered encoding interface before delivery.

## Status

landed 20261023T230722-L-3471572 2026-10-23 (merge of deliver/E2/Sheaf.Paper.IntegralScalarConstructibleImage)
