## Worker report

Q70, stage 2, 2026-10-19. The delivery states
`AlgebraicGeometry.henselian_normal_completion_preparation` in
`Sheaf.RingTheory.HenselianNormalCompletionPreparation`. Its only proof is `sorry`.
No new definitions, nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`; the recorded signature is the file's entire signature.

I resumed the dispatched item by inspecting its sandbox and the shared delivery log.
Only brief markers existed; there was no earlier Q70 Lean file or delivery to repeat.
The shared Q139 delivery is the stage-1 split, not a stage-2 binding.

Hypotheses and clauses, in the order of the natural statement:

1. A reduced quasi-excellent Noetherian local commutative ring is
   `(R : Type u) [CommRing R] [IsLocalRing R] [_root_.IsReduced R]
   [IsNoetherianRing R] (hR : IsQuasiExcellent R)`.
   No excellence or normality of R is assumed. Quasi-excellence already includes
   Noetherianity, but the explicit instance is the node's stated hypothesis.
2. The ordinary henselization is `(H : Type v) [CommRing H]
   [HenselianLocalRing H] [Algebra (Localization.AtPrime
   (IsLocalRing.maximalIdeal R)) H]` with
   `hH : Algebra.IsHenselizationAtPrime' R (IsLocalRing.maximalIdeal R) H`.
   The henselian-local structure is part of the recorded notion, not an extra
   condition on R. Its input ring is R localized at its maximal ideal, canonically R.
3. H reduced, Noetherian, excellent, henselian and of the same Krull dimension is
   `_root_.IsReduced H ∧ IsNoetherianRing H ∧ IsExcellent H ∧
   HenselianLocalRing H ∧ ringKrullDim H = ringKrullDim R`.
4. The finite family of local normalization factors is
   `∃ (r : ℕ) (B : Fin r → CommRingCat.{v}) (f : ∀ a, H →+* B a), ...`.
   Bundling commutative rings avoids defining a second ring notion or inserting
   local instance lets into the signature. For every a, the first conjunction states
   `IsDomain (B a)`, `IsIntegrallyClosed (B a)`, `IsExcellent (B a)`,
   `IsNoetherianRing (B a)`, and `HenselianLocalRing (B a)`.
   Thus normal means exactly integrally closed in the fraction field.
5. The product is precisely the recorded componentwise normalization:
   `∃ e : Spec (.of (∀ a, B a)) ≅ (Spec (.of H)).reducedNormalization, ...`.
   The equality
   `sigmaSpec B ≫ e.hom ≫ (Spec (.of H)).fromReducedNormalization =
   Sigma.desc (fun a ↦ Spec.map (CommRingCat.ofHom (f a)))`
   specifies its map over Spec H. Here `sigmaSpec B` is the canonical map from
   the coproduct of the factor spectra to the spectrum of their product; for
   this finite family it is an isomorphism. The equation prevents an unrelated
   family of rings or an unrelated map from representing the normalization.
6. Finiteness as a module is `(f a).Finite`, Mathlib's restriction-of-scalars
   `Module.Finite`. The actual coproduct map has `IsFinite` and `Surjective`.
7. The dense open is `∃ U : (Spec (.of H)).Opens, Dense (U : Set ...) ∧ ...`.
   Every component's generic point belongs to U, expressed using
   `∀ Z : irreducibleComponents ..., ∀ x, IsGenericPoint x Z.1 → x ∈ U`.
   `IsIso ((Sigma.desc ...) ∣_ U)` is precisely the isomorphism above U.
8. Each dimension bound is `ringKrullDim (B a) ≤ ringKrullDim H`, not an
   equidimensionality or equality assertion.
9. The arbitrary completion clause is independently quantified as
   `∀ (A : Type w) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
   [IsDomain A], IsIntegrallyClosed A → IsExcellent A → ...`.
   This ring is unrelated to R and H and is not assumed henselian.
   Its completion is exactly `AdicCompletion (IsLocalRing.maximalIdeal A) A`.
   The outputs are `IsIntegrallyClosed`, `IsNoetherianRing`, `IsLocalRing`,
   `IsDomain`, and `Module.FaithfullyFlat A` of this completion. Its algebra
   structure is the canonical completion map, not a supplied arbitrary map.
10. The final family clause quantifies every `Z : Set (PrimeSpectrum R)` with
    `IsClosed Z` and `IsNowhereDense Z`. It gives `IsNowhereDense` of its
    inverse images under three explicit comaps: the canonical composite
    R → Localization.AtPrime m → H; that composite followed by `f a`; and
    that composite followed by `f a` and the canonical maximal-ideal completion.
    The last clause uses `∀ [IsLocalRing (B a)], ...` to make the maximal ideal
    available to elaboration without any `let` or auxiliary definition.
    This is not a missing existence condition: `HenselianLocalRing (B a)` has
    already been asserted and supplies it. The class is Prop-valued, so every
    choice of its evidence gives the same maximal ideal and completion.

Recorded statement dependencies read and used:

- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'`; I also read the imported original
  `Algebra.IsHenselizationAtPrime` and its local-map universal property.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, `IsExcellent`, with
  the G-ring, J-2 and universally catenary definitions read in full.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
  Here the objects in the statement are rings, so `_root_.IsReduced` is used;
  the affine equivalence with reduced schemes is Mathlib's existing Spec API
  (Properties.lean, the Spec instance and converse at lines 115--126).
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianLocalRing`
  (from Mathlib), whose definition and docstring were read, together with
  `HenselianRing` and `IsStrictlyHenselianLocalRing`. Strict henselization
  and a separably closed residue field are not assumed.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalization` and
  `AlgebraicGeometry.Scheme.fromReducedNormalization`, including their
  definitions as the componentwise coproduct and its canonical map.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`:
  `AdicCompletion`, its compatible-sequence definition, canonical algebra
  structure and `evalOneₐ`; the node's exact completion is reused.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, with its
  `WithBot ℕ∞` codomain, not a truncated natural-number dimension.

The modules of all recorded proof dependencies are imported without `public`
unless already public signature dependencies. Mathlib matches are imported
from their defining modules as well. In particular the proof route includes
pair henselization, the ordinary universal property, Noetherian completion,
ind-etale ascent, Nagata finiteness, affine normalization charts, finite
henselian decomposition, normal-fibre ascent, finite-extension completion,
Ratliff formal catenarity, excellence ascent, and generic normalization.
For the three upstream modules absent from the old local checkout, I read
current sources through `scompile.py --source`:
`WeilConjectures.RingTheory.PairHenselization`,
`WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`, and
`WeilConjectures.RingTheory.AdicCompletionNoetherian`.
The theorem docstring preserves all thirteen proof steps with their cited IDs.

Source checks: I read the actual local ILO PDF at PDF pages 20--22
(printed pp.14--16) and 49--50 (printed pp.43--44), and the Stacks source
passages `lemma-henselization-reduced`, `lemma-henselization-dimension`,
and `lemma-completion-normal-local-ring` in more-algebra.tex.
ILO I 6.3(ii) justifies excellence of the henselization even though R is
only quasi-excellent; III 6.2 explains normal local normalization factors,
normal completion and preservation of rare closed subsets.

Edge cases checked: a field (dimension zero and identity completion);
an already henselian ring; an already normal local ring (one factor);
a reduced local ring with several components, including unequal component
dimensions (only the stated upper bound is imposed); Z empty; and Z any
nowhere dense closed set. No connectedness or normality is imposed on R.
The zero ring is excluded by the existing nontrivial local-ring convention.
The finite index is unrestricted, and an empty product cannot satisfy the
normalization and surjectivity clauses for the nonempty spectrum of H.
The completion test ring has an independent explicit universe w. R and H
have independent u and v, using the recorded generalized henselization API;
all maps between their spectra use universe-polymorphic prime comaps.
No auto-bound implicit variables, local notation, private helpers, or
statement-level `let` are used.

Searches actually run via `msearch.py Q70` for this item (searches.jsonl):

- LeanFinder: "A reduced quasi excellent local ring has excellent henselization
  whose normalization is a finite product of henselian normal local domains
  with normal faithfully flat completions". Eight generic henselian-ring
  hits, including `HenselianLocalRing`, its TFAE, field and complete-ring
  instances; no exact theorem.
- Loogle: `HenselianLocalRing, IsIntegrallyClosed`: zero hits.
- Mathlib grep: `henseli.*normali|normali.*henseli|IsQuasiExcellent`
  in `RingTheory`: zero hits.
- LeanSearch: "henselization quasi excellent local ring normalization normal
  completion faithfully flat": eight henselian classes, constructors and
  root-lifting/TFAE hits; no combined preparation theorem.
- Direct rg in upstream WeilConjectures and shared lean/Sheaf for
  `henselian_normal_completion_preparation|henselian.*normal.*completion|` plus
  the exact item ID: only a proof-docstring mention in
  `UniformizationCompleteLocalDescent.lean`, not a declaration.
- Direct rg of dag/lean_names_upstream.json for IsQuasiExcellent and the
  proposed theorem name: no match. Dependency declarations above were read
  directly in their source modules; no private replacement was introduced.

Validation: prescribed scompile.py compiled both the sandbox and the actual
module successfully (about 3 seconds each), with no errors or warnings.
The required deliver2.py dry run and push are performed after this report.

## Second reading by Q70

I made a second clause-by-clause pass with the current JSON and completed
Lean file open. This is a self-check by the dispatched worker; the maintainer
will supply the independent review specified in the dispatcher brief.

I checked in particular that hH is ordinary henselization at the maximal
ideal, not strict henselization or pair henselization; that the canonical
R-to-H composite is the one used in every inverse image; that e identifies
the product with the existing normalization over Spec H; that normality and
Noetherianity are assertions about every factor; and that arbitrary A has
no henselian assumption. The dense open quantifies every generic point,
and the dimension bound does not force equal component dimensions.
I checked the parentheses of the three nowhere-density outputs: they lie
inside the existential choice of the same family B and maps f, so no
unrelated family or map can satisfy them. The local-structure quantifier
in the completed-factor clause is inhabited by the preceding henselian
assertion and is independent of proof evidence.

This pass found no missing hypothesis or clause and required no statement
correction. It did identify proof-only Mathlib dependencies whose modules
were previously reached transitively; they now have explicit ordinary
imports. The main proof remains exactly `by sorry`. No project or launcher
file was modified outside the assigned sandbox.
