## Worker report

The module `Sheaf.RingTheory.CotangentAugmentationLocalization` states
`Algebra.CotangentResolution.cotangent_augmentation_localization`. Its single theorem
has `sorry`; all helper definitions have actual data. The original statement, proof,
and proof dependencies are unchanged. The only statement-dependency addition registers
an already existing standard differential augmentation.

Hypotheses and objects:
- `A B : Type u`, `[CommRing A]`, `[CommRing B]`, `[Algebra A B]` encode an arbitrary
  ring map, equivalently its induced algebra structure. `T : Submonoid B` is an arbitrary
  multiplicative subset and `Localization T` is C with its induced A-algebra.
- `D : Algebra.CotangentResolution.Coherence` is the dependency's specified standard
  resolution data. `standardDifferentialComplex D A B` is exactly its
  `differentialComplex (D.differentials (D.standard ...))`, representing L[B/A].
- The family of `HasDerivedCategory.{u+1} (ModuleCat.{u} R)` instances is the existing
  coherence interface's chosen ambient localization size. No nonzero, finite type,
  principal localization, boundedness or characteristic hypothesis is imposed.

Clause correspondence, in order:
1. `tensorFractionIso` is the inverse of the existing
   `LocalizedModule.equivTensorProduct`. The first two conjuncts give its forward and
   inverse fraction formulas. Tensor factors use C tensor_B N, the symmetric order
   used by the recorded differential-complex interface. Thus c tensor n means the
   source's n tensor c, and the forward formula is (b/t) tensor n maps to bn/t.
2. The third conjunct is naturality for every B-linear `v`. `fractionMap` is the
   existing `IsLocalizedModule.mapExtendScalars`, with its C-linearity retained.
3. The fourth conjunct supplies the integer-degree cohomology isomorphisms `H K i`.
   Its first subclause fixes them on fraction cycles: the cycle with underlying
   element (1/t) tensor z maps to the fraction [z]/t. This specifies the canonical
   comparison, rather than an arbitrary naturally rescaled isomorphism. Its second
   subclause is naturality for every chain map and every integer degree.
4. The fifth conjunct says termwise tensor preserves every `QuasiIso`.
5. `localizedDifferentialsIso A B T` is kappa: an actual C-module isomorphism obtained
   from the tensor/fraction identification, `kahlerAlgebraMapIso`, and Mathlib's
   canonical `tensorKaehlerEquivOfFormallyEtale`. The sixth conjunct states precisely
   kappa(db/t) = (1/t)d(b/1).
6. The remaining existential provides the specified augmentations `aB` and `aC`,
   using the existing `DifferentialAugmentation` structure. That structure contains
   the chain map to Omega[0] and the formula b tensor dx maps to b d(epsilon(x));
   all remaining components have zero target. Existence is asserted here; no
   definition chooses unspecified objects from an existence theorem.
7. `lam` is a chain map from the termwise tensor of the exact standard complex to
   the exact standard complex over C. Its first clause fixes it on all tensor
   differential generators in every nonpositive degree using the dependency's
   `D.standardMap (standardLocalizationSquare A B T)`. This is the canonical map
   induced by B to C and the identity of A, rather than an unconstrained arrow.
   The next clause is `QuasiIso lam`.
8. The next clause is the equality after `DerivedCategory.Q.map`, in D(C).
   `tensorDifferentialAugmentation` explicitly tensors aB, applies
   `HomologicalComplex.singleMapHomologicalComplex`, and then the displayed
   tensor/fraction identification. Postcomposition with single(kappa) is the
   right-hand composite. The following two clauses give the value of each composite
   separately on every localized degree-zero generator: (b/t)d(epsilon(x)/1).
9. The last implication is `QuasiIso aB.map` implies quasi-isomorphism of
   `aC.map` followed by single(kappa inverse), exactly the conditional consequence.

Dependency declarations read and used:
- `Sheaf.RingTheory.CotangentResolutionCoherence`: `Coherence`, `standard`,
  `differentials`, `standardMap`, `DifferentialMap`, `differentialComplex`,
  `complexGenerator`, `cotangentComplex` and `cotangentMap`; full signatures,
  generator conditions and source/proof docstrings read.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `.D`, and
  `.linearMapEquivDerivation`, through the bundled `CommRingCat.KaehlerDifferential`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`; cohomology and `QuasiIso` use the
  corresponding `HomologicalComplex` constructions.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, `.mk`,
  `.mkLinearMap`, `IsLocalizedModule.mapExtendScalars`; the fraction criterion and
  localization-ring module action were read.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`: `TensorProduct` and its
  generator/map conventions, implemented categorically by `ModuleCat.extendScalars`.
- `Mathlib.RingTheory.Localization.BaseChange`: `LocalizedModule.equivTensorProduct`
  and its two fraction formulas. `Mathlib.RingTheory.Etale.Kaehler`:
  `KaehlerDifferential.isLocalizedModule_map` and
  `tensorKaehlerEquivOfFormallyEtale`.
- `Sheaf.RingTheory.PolynomialCotangentIdentification`:
  `DifferentialAugmentation`, `kahlerAlgebraMapIso`; these are reused, never copied.

The stated proof dependency `LocalizationCotangentVanishing` is imported. Mathlib
localization exactness, localization flatness and Kähler localization are imported
through their recorded source modules. The retract-transitivity and zero-relative-square
nodes have no recorded module at the time of reading, so there is no statement module
to import for those proof-only prerequisites; they are named in the complete proof
plan. This does not require any missing notion in the present signature.

Sources checked locally: Stacks cotangent.tex, lemma-localize (08SF), and the
standard functoriality construction; algebra.tex, lemma-tensor-localization (00DK),
proposition-localization-exact (00CS), lemma-differentials-localize (00RT), part (2).
The fraction order is explicitly symmetric to 00DK. No source correction is needed.

Edge cases checked mathematically: T containing zero (C and every C-module are zero),
T = {1}, zero source or target rings, zero modules and zero complexes, arbitrary and
infinitely generated multiplicative sets, unbounded complexes and all integer degrees,
and positive characteristic. The module generators and fraction formulas require no
cancellation of a nonzero element. The identity localization retains its actual
canonical maps rather than identifying isomorphic rings literally.

Searches: msearch LeanFinder, `localization of standard cotangent differential
augmentation naturality quasi isomorphism`, returned presentation conormal localization
maps only; Loogle, `"cotangentComplex", "localization"`, returned zero hits; Mathlib
grep, `cotangent.*[Ll]ocal|[Aa]ugmentation.*[Ll]ocal`, returned conormal and H1 results;
LeanSearch, `standard cotangent differential augmentation to Kahler differentials`,
returned the ordinary presentation-to-differentials map, not the full standard
complex. Project `rg` searches in WeilConjectures and Sheaf found the standard
coherence and the augmentation structure used here, but no theorem carrying all the
present clauses. Exact node-id searches in WeilConjectures and Sheaf found no match.
The new definition node records the search outputs verbatim and the project searches.

Validation: scompile.py compiled the isolated file and the final library module path
cleanly (12.0 s and 14.7 s); no errors or warnings were reported. The required
deliver2 dry run passed preflight and compilation (commit abac4d809d5; nothing
was pushed by that dry run). The tensor transport uses only the actual
`toAlgebra_algebraMap` equality, naming both its algebra and module instances
explicitly; no mathematical hypothesis was added.

## New nodes

`def-trf-standard-differential-augmentation` registers, with `existing: true`, the
already published `Algebra.CotangentResolution.DifferentialAugmentation` in
`Sheaf.RingTheory.PolynomialCotangentIdentification`. It introduces no Lean file and
no duplicate definition. Its statement is the chain map from the standard differential
complex to Omega[0], normalized on each b tensor dx, as in Stacks 08PN and 08QL.
The DAG search finds only the polynomial cotangent theorem listing this declaration;
there is no definition node for it. `tools/blueprint_refs.py search` returns no
blueprint unit for differential augmentation. The new node cites the three existing
definition owners of its resolution data, universal differentials, and cochain/derived
categories, and uses the item's existing blueprint ancestry.

## Second reading by Q09

Under the direct-delivery policy, no second worker was started. This independent
clause-by-clause reading was done at review (maintainer reviewer, 2026-10-24) and
replaces the earlier note that the author's account was not an independent review.

Node objects and hypotheses against the Lean:
- A→B arbitrary ring map: `A B : Type u`, `[CommRing A] [CommRing B] [Algebra A B]`. T is an
  arbitrary `Submonoid B` and C = `Localization T`. There is no nonzero, finiteness or
  principal hypothesis. The only extra binder is the `HasDerivedCategory` family required
  by `Coherence`. OK.
- L_{B/A}, L_{C/A}: `standardDifferentialComplex D A _` = `differentialComplex
  (D.differentials (D.standard …))` of def-trf-cotangent-resolution-data. OK.
- a_R: `DifferentialAugmentation D (Arrow.mk (ofHom (algebraMap A R)))`, the def node
  def-trf-standard-differential-augmentation. Its `generator` field fixes degree 0 on b ⊗ dx,
  which span B ⊗_{P₀} Ω (termIso and extendXIso are isomorphisms), and every other target
  degree is 0. So the structure is a subsingleton, and `∃ aB aC` means the specified
  augmentation. OK.
- Tensor/fraction identification: `tensorFractionIso` = the eqToIso instance transport
  composed with the inverse of Mathlib `LocalizedModule.equivTensorProduct`, which is
  canonical. Conjuncts 1–2 state (b/t)⊗n ↦ bn/t and n/t ↦ (1/t)⊗n, in the factor order
  of 00DK (algebra.tex:2088). Conjunct 3 is naturality in module maps (`fractionMap` =
  `IsLocalizedModule.mapExtendScalars`). OK.
- H^i(K⊗C) ≅ T⁻¹H^i(K), natural, for all i ∈ ℤ: `∃ H` is fixed on the classes of the
  cycles (1/t)⊗z. By exactness every cycle of K⊗C has this form, so H is pinned.
  Naturality is stated for every chain map. Conjunct 5 says termwise tensor preserves
  `QuasiIso`. OK.
- κ: `localizedDifferentialsIso`, built from canonical isomorphisms (tensor/fraction,
  `kahlerAlgebraMapIso`, `tensorKaehlerEquivOfFormallyEtale`). Conjunct 6 gives
  κ(db/t) = (1/t)·d(b/1), which pins it. Since it is an isomorphism, "κ is an
  isomorphism" holds. OK.
- λ: a chain map C⊗L_{B/A} → L_{C/A} fixed on c ⊗ gen_n(1,x) ↦ c·gen_n(1, h_n x) for every
  n, with h = `D.standardMap (standardLocalizationSquare A B T)` (base 𝟙_A, top B→C).
  These elements span every degree, so λ is the canonical map. `QuasiIso lam` holds. OK.
- a_C λ = κ[0](a_B ⊗ C) in D(C): `Q.map (lam ≫ aC.map) = Q.map (tensorDifferentialAugmentation
  T aB ≫ single.map κ)`. The right-hand side is C⊗a_B, then the single-complex commutation,
  then the fraction identification, then κ. OK.
- Generator values: both composites on (b/t) ⊗ gen₀(1,x) equal (b/t)·d(ε_B(x)/1). These are
  separate clauses that mention the maps, so they are not tautologies. OK.
- Consequence: `QuasiIso aB.map → QuasiIso (aC.map ≫ single.map κ.inv)` = κ⁻¹[0]a_C. OK.

Edge cases: 0 ∈ T (C = 0, so every clause is trivially consistent), T = {1}, an infinitely
generated T, every integer degree, and unbounded K. None of them is excluded.

Searches: rg DifferentialAugmentation in lean/Sheaf and lean/WeilConjectures finds only
PolynomialCotangentIdentification. No other node or delivery owns it, and no other S2
delivery of this item exists.

Finding (maintainer note, not a group fault): the item and the new existing:true def node
use `DifferentialAugmentation` and `kahlerAlgebraMapIso`. Both live in
Sheaf.RingTheory.PolynomialCotangentIdentification, the module of
lem-trf-smooth-cotangent-identification, whose proof_deps contain this item. The stage-3
proof import of the item into that module would close an import cycle. The group cannot
move those declarations, because the owner is outside the delivery closure. The maintainer
should move both into a def-node module (for def-trf-standard-differential-augmentation),
re-imported by PolynomialCotangentIdentification.
