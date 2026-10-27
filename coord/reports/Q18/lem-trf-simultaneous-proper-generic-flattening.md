## Worker report

The module `Sheaf.AlgebraicGeometry.SimultaneousProperGenericFlattening` states
`AlgebraicGeometry.exists_simultaneous_flat_finitePresentation_strictTransform_admissibleBlowup`.
Its only theorem has proof `sorry`; there are no new definitions or helper theorems.
The item's existing fields are unchanged, and its `lean.statement` is extracted verbatim
from the theorem signature. No statement correction or dependency repair is required.

Sources read: Stacks `flat.tex`, `lemma-flat-after-blowing-up` (081R), including its
proof; `morphisms.tex`, `proposition-generic-flatness` (052A), statement and proof;
`divisors.tex`, `definition-strict-transform` (080D). These give flattening after an
admissible blowup and the schematic, rather than topological, transform. The node's
seven proof steps are recorded in the declaration docstring, including the clopen
closure-kernel argument and the empty-source cases. The ILO reference is retained
as provenance; the construction here follows the supplied Stacks sources.

Every hypothesis and conclusion is rendered as follows:

| Node clause | Lean rendering and interpretation |
| --- | --- |
| Integral base scheme S | `{S : Scheme.{u}} [IsIntegral S]`; the recorded Mathlib class includes nonemptiness, reducedness and irreducibility. |
| S locally Noetherian and quasi-compact | `[IsLocallyNoetherian S] [CompactSpace S]`, exactly the two specified Noetherian conditions. No separatedness or extra base hypothesis is imposed. |
| Two schemes and their maps | `X : Fin 2 → Scheme.{u}` and `f : ∀ i : Fin 2, X i ⟶ S`; indices 0 and 1 encode the node's two labels. |
| Each morphism proper | `[∀ i : Fin 2, IsProper (f i)]`; no nonemptiness, integrality or flatness is assumed of either source. |
| Nonempty quasi-compact open U | `∃ U : S.Opens, (U : Set S).Nonempty ∧ IsCompact (U : Set S) ∧ ...`. `IsCompact` has no separation axiom. |
| Finite-type quasi-coherent ideal I, unit on U | `∃ B : IsAdmissible S U, ...`: `B.I : S.IdealSheafData` is the quasi-coherent ideal, `B.finiteType` asserts `B.I.ofFiniteType`, and `B.disjoint_support` says its support is disjoint from U, equivalently it restricts to the unit ideal there. |
| Its U-admissible blowup T → S | The canonical `B.I.blowup` and `B.I.blowupMap`, constructed by the recorded blowup API; this chooses the blowup itself, so no arbitrary morphism or unspecified comparison is substituted. |
| V = S minus V(I) | Every occurrence is the actual open `B.I.support.compl`; V can be larger than U. |
| Individual strict transforms as closed subschemes of X_i ×_S T | `strictTransform (f i) B.I.blowupMap B.I.support.compl` with its recorded `strictTransformι`. The source defines this object as `((strictTransformOpen ...).ι).image`, a closed subscheme of the actual fibre product. |
| Flat over T | `∀ i, Flat (strictTransformMap (f i) B.I.blowupMap B.I.support.compl) ∧ ...`. |
| Finitely presented over T | For the same map, the conjunction of `LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated`, exactly as the node expands this condition. |
| Agrees with X_i over V | `IsIso ((strictTransformToSource (f i) B.I.blowupMap B.I.support.compl) ∣_ (f i ⁻¹ᵁ B.I.support.compl))`. Its target is `(X_i)_V`; its domain is the inverse image of this open in the strict transform. The identity `strictTransform_condition` identifies this with the open above V under the map through T, so it is exactly the requested agreement. |
| Schematic closure of (X_i)_V | This is already the definition of the strict transform used in the statement, not an omitted property: `strictTransformOpen` is the open of the fibre product above V, and `strictTransform` is its scheme-theoretic image under its open immersion. Over V the blowup is an isomorphism, so this open is canonically `(X_i)_V`, by `Scheme.IdealSheafData.isPullback_strictTransformOpen_blowupMap`. The ideal is the kernel ideal of this immersion; nilpotents are retained. No redundant definitional-equality conjunct is introduced. |
| Transform of the disjoint union is the union of the transforms | The existential isomorphism `e : (∐ fun i : Fin 2 ↦ strictTransform (f i) ...) ≅ strictTransform (Sigma.desc f) ...` and the two equations for every coprojection. The first equation commutes with `strictTransformToSource` and `Sigma.ι X i`; the second commutes with `strictTransformMap` to T. Thus the isomorphism respects both projections to `(∐ X)` and T, and hence the embedding into their fibre product. It states the equality of schematic closed subschemes under the usual base-change/coproduct identification, not merely an abstract isomorphism of unrelated schemes. |

Dependency declarations read and used:

| Dependency node | Recorded module and declarations |
| --- | --- |
| `def-nagata-admissible-blowup` | `WeilConjectures.Blowup.AdmissibleBlowup`: `AlgebraicGeometry.IsAdmissible`, whose fields `I`, `finiteType`, `disjoint_support` give exactly the centre data required here. The item uses its associated canonical blowup, so the general isomorphic-presentation convention in the dependency does not require another interface. |
| `def-nagata-scheme-theoretic-image` | `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `AlgebraicGeometry.Scheme.Hom.image` and `imageι`; the transform definition uses this very image construction, with its actual quasi-coherent kernel ideal. |
| `def-nagata-strict-transform` | `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`, `strictTransformOpen`, `strictTransformι`, `strictTransformMap`, `strictTransformToSource`, and `strictTransform_condition`. The full definitions and over-complement comparison statements were read. |
| `def-pc-integral-scheme` | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`. |
| `def-sbc-locally-finite-presentation` | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`. |
| `def-weil-flat-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with its documented stalkwise equivalence. |
| `def-weil-pbc-quasi-compact-scheme` | `Mathlib.Topology.Defs.Filter`: `CompactSpace`. |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, extending separatedness, universal closedness and local finite type; universal closedness supplies quasi-compactness. |
| `lem-weil-pbc-scheme-coproduct-family` | Its `mathlib_match` is used directly: `Mathlib.AlgebraicGeometry.Limits`, the discrete-colimit instance, `AlgebraicGeometry.sigmaOpenCover` and `disjoint_opensRange_sigmaι`, together with `CategoryTheory.Limits.Sigma.desc` and `Sigma.ι` for the actual coproduct and its maps. There is no need to invent a Lean record for this Mathlib dependency. |
| `pqf-def-locnoeth` | `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`, equivalent to the recorded affine-cover formulation. |

Proof-only imports retain the already stated dependencies: the Mathlib finite-type,
quasi-separatedness, Noetherian-scheme and Noetherian-topology modules supply the
Mathlib matches of the corresponding proof nodes;
`WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation` supplies
`exists_nonempty_open_flat_finitePresentation_restrict`;
`Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup` supplies
`exists_flat_finitePresentation_strictTransform_admissibleBlowup`;
`WeilConjectures.Blowup.AdmissibleBlowup` supplies
`IsAdmissible.isIso_blowupMap_restrict`. No proof-dependency import is omitted for a cycle.

Edge cases checked before writing:

- Either source, or both, may be empty. No binder excludes these cases; the strict
  transform is the schematic image of an empty open when appropriate. For two empty
  sources one may use the unit centre and any nonempty affine base open.
- The empty base is excluded by the existing integral-scheme definition, just as in
  the node. Integrality is necessary for the nonempty generic open argument.
- If one family is supported only on a proper closed subset, its generic open part
  can be empty and its transform may be empty. No dominance or surjectivity is assumed.
- If both families are already flat and finitely presented, the unit ideal and trivial
  blowup are allowed; a nontrivial or proper centre is not required.
- The open U may be strictly smaller than the centre complement V; every transform
  and every agreement clause uses V, not U.
- Nonreduced sources and their nilpotents are permitted. The closure uses `Hom.image`,
  not topological closure or reduction.
- The two-element index type is small in every scheme universe u. The same arbitrary
  universe u is bound explicitly for all schemes; no test universe or size condition
  can make a hypothesis vacuous. There are no automatic implicit variables.

Searches for an existing exact statement (all performed through the prescribed tools
or read-only searches):

- `msearch.py ... leanfinder "For two proper schemes over an integral Noetherian base a single admissible blowup makes both strict transforms flat and finitely presented"`:
  eight hits, including `AlgebraicGeometry.Flat`, flatness permanence and
  `UniversallyOpen.of_flat`; none states simultaneous blowup flattening.
- `msearch.py ... leansearch "Simultaneous generic flattening of two proper schemes by an admissible blowup"`:
  eight hits on the flatness definition, its affine criterion and permanence; no match.
- `msearch.py ... loogle '"strictTransform"'`: zero hits.
- `msearch.py ... grep 'strictTransform|strict_transform|flatification|flattening' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures/Compactification`,
  `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` found the
  existing strict-transform constructions, single-morphism flattening, and the
  downstream `FlatificationHorizontalCurvePair`; none states this two-proper-family
  result. The latter is a curve-specific consumer with additional geometric outputs,
  so it is not an exact existing match.
- A literal item-id search in `lean/WeilConjectures` returned no result. A full-name
  search of Mathlib, upstream Lean, project Lean and `dag/lean_names_upstream.json`
  found no collision for the new theorem name.

Validation: the prescribed `scompile.py Q18 lem-trf-simultaneous-proper-generic-flattening`
compiled the delivered module against the live published library in both sandbox and
library-module modes, with no errors or warnings (1.9 s and 2.3 s respectively).
The only postponed proof is the named theorem recorded in the item's DAG node.
There are no disputed statements or known node faults.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
