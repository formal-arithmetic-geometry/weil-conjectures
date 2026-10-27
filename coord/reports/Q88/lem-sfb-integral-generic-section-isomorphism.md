## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralGenericSectionIsomorphism` states
`AlgebraicGeometry.section_inverse_of_isIntegral_of_isIso_morphismRestrict`, with
`sorry` as its entire proof. No definitions, helper statements, new nodes, dependency
repairs, or changes to the informal statement are needed.

The hypothesis and conclusion correspondence is:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and Y | `{X Y : Scheme.{u}}`, with explicitly bound `universe u` |
| X and Y integral | `[IsIntegral X] [IsIntegral Y]` |
| f : Y → X separated | `(f : Y ⟶ X) [IsSeparated f]` |
| There is a nonempty open V in X | `(hV : ∃ V : X.Opens, (V : Set X).Nonempty ∧ ...)` |
| The induced f⁻¹(V) → V is an isomorphism | `IsIso (f ∣_ V)`, using Mathlib's canonical `morphismRestrict` |
| s : X → Y is a section | `(s : X ⟶ Y) (hs : s ≫ f = 𝟙 X)` |
| s and f are inverse isomorphisms | `f ≫ s = 𝟙 Y`, together with the given `hs` |
| s takes the generic point of X to that of Y | `s (genericPoint X) = genericPoint Y` |

The inverse equality returned is equality of scheme morphisms, including structure
sheaf maps. Combined with `hs` it gives precisely a scheme isomorphism with hom `s`
and inv `f`. It does not merely assert a bijection on points. The generic points are
Mathlib's canonical generic points; integrality supplies irreducibility and schemes
are sober, so they exist and are unique. The equality is equivalent to saying the
image point is generic, with no additional generic-point hypothesis.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, declaration
  `AlgebraicGeometry.IsIntegral`. Its actual fields require nonemptiness and domains
  of sections on nonempty opens; this agrees with the node's integral-scheme notion.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, whose
  recorded declarations include `AlgebraicGeometry.IsSeparated`. Its definition in
  `Morphisms.Separated` says the diagonal is a closed immersion. Only separatedness
  is assumed here; the node does not require properness or an integral morphism.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, declarations `IsGenericPoint`,
  `genericPoint`, and `genericPoint_spec`. The latter certifies closure of the
  singleton is the whole space.

`Mathlib.AlgebraicGeometry.Restrict` supplies `AlgebraicGeometry.morphismRestrict`:
the source is `(f ⁻¹ᵁ V).toScheme`, the target is `V.toScheme`, and its defining map
is the canonical pullback projection transported to the open subscheme.

The available proof dependencies are imported without `public`. The closed-section
node's Mathlib match is `AlgebraicGeometry.IsClosedImmersion.of_comp` from
`Mathlib.AlgebraicGeometry.Morphisms.Separated` (already publicly imported through
Proper). Closed immersions are from `Morphisms.ClosedImmersion`; irreducible sets
and components are from `Mathlib.Topology.Irreducible`. The reduced-source
factorization node is recorded on
`AlgebraicGeometry.IsClosedImmersion.existsUnique_fac_of_range_subset_range` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, imported as a
proof dependency. Its full signature and reduced-source requirement were read. The
docstring gives all four proof steps of the node, including the reducedness argument
needed to obtain a scheme-theoretic inverse.

Sources read locally: `literature/stacks-project/varieties.tex`,
`lemma-modification-normal-iso-over-codimension-1`, especially the final paragraph
of proof (4), and `literature/stacks-project/schemes.tex`,
`lemma-section-immersion`. The former obtains the isomorphism from a closed section
through the generic point; the node's explicit nonempty isomorphism open justifies
that generic-point step.

Edge cases checked before writing:

- Empty X and Y are excluded by the node's integrality assumption itself.
- Empty V is explicitly excluded; allowing it would make the isomorphism-open
  hypothesis vacuous and the conclusion false in general.
- V may equal X. Identity morphisms, one-point integral spectra, arbitrary fields
  and characteristics are included without additional assumptions.
- No Noetherian, finite-type, normality, properness, finite-fibre or integral-morphism
  assumption is introduced. Irreducibility and reducedness of Y are essential in
  the density and scheme-theoretic factorization steps, respectively.
- No quasi-compactness condition is imposed on V. The single scheme universe `u`
  is the standard universe of the category containing both morphisms; it is not an
  independent test-object universe or a cardinality restriction.

Searches for an existing statement (all via the prescribed tools):

- `msearch.py ... leanfinder`: query "A section of a separated morphism of integral
  schemes that is an isomorphism over a nonempty open is an inverse isomorphism and
  maps generic points". Eight results, including
  `genericPoint_eq_of_isOpenImmersion`, `ext_of_isDominant_of_isSeparated`, and
  normalization isomorphism results. None asserts the present theorem: the first
  assumes an open immersion, extensionality requires additional inputs, and an
  integral morphism is different from a morphism of integral schemes.
- `msearch.py ... loogle`: query
  `AlgebraicGeometry.IsSeparated, CategoryTheory.IsIso`. Two normalization/Zariski
  main theorem results; neither states this section criterion.
- `msearch.py ... leansearch`: query "A section of a separated morphism of integral
  schemes which is an isomorphism over a nonempty open subset is an isomorphism".
  Eight results about restrictions of isomorphisms, open immersions, and separated
  restrictions; no statement with the required section hypothesis and conclusion.
- `msearch.py ... grep`: query
  `section.*[Ii]so|isIso.*[Ss]ection|genericPoint.*section`, subdirectory
  `AlgebraicGeometry`. Twenty-five matches, mostly sections of sheaves and
  restriction APIs; no whole-theorem match.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for section/isomorphism
  and generic/birational section combinations found related statements, including
  closed-immersion criteria and trait-specific section statements, but no exact
  match. The closed-immersion/surjectivity isomorphism criterion requires hypotheses
  that this node must first establish. Searching the item id gives no source-library
  or Sheaf module. The exact new declaration name was also searched in Mathlib,
  both project roots and `dag/lean_names_upstream.json`, with no match.

No statement dispute or node fault was found. The nominal CompactObject example
module has been withdrawn; its node now records the upstream
`WeilConjectures.CategoryTheory.CompactObject` definition. This delivery follows the
required module-mode header, import visibility, public section and docstrings.

## Second reading by Q88

Performed a separate rereading of the original node and completed Lean file in this
worker session; the dispatch brief forbids starting another agent, so this is not
claimed to be an independent reviewer. The maintainer supplies the independent
delivery review.

Checked the direction of both compositions: `hs : s ≫ f = 𝟙 X` is exactly
f composed with s, and the conclusion `f ≫ s = 𝟙 Y` is s composed with f. These
give the requested inverse isomorphisms without repeating the given equality as a
tautological conjunct. Checked the restricted map has precisely the inverse-image
open as source, and that nonemptiness refers to V itself. Both integrality
instances and separatedness are explicit. The final equality states the complete
generic-point clause, not just membership of the image in a dense set. No extra
hypothesis, dropped clause, duplicate notion, or unbound variable was found; no
change was required in this rereading.
