## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineOpenPrincipalComparisonCover` states
`AlgebraicGeometry.Scheme.quasiAffine_open_principal_comparison_cover`. Its only proof
is `sorry`; it introduces no definitions and changes only the item's `lean` field.
The node and the proof in Stacks `properties.tex`, Tag 0ARY,
`lemma-cartesian-diagram-quasi-affine` (lines 2493–2519), were read, together with
Tag 01P9 immediately before it. This is the common-chart subargument of 0ARY;
it does not assert the whole cartesian-square conclusion or require U quasi-compact.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes U and V: `{U V : Scheme.{u}}`, with the universe explicitly declared.
- Open immersion u: `(u : U ⟶ V) [IsOpenImmersion u]`.
- V isomorphic to a quasi-compact open in an affine scheme: `[V.IsQuasiAffine]`.
  The recorded proof leaf explains this equivalence. Mathlib's class includes
  compactness and immersion of the canonical map; its canonical map is open, so
  it also directly realizes V as a quasi-compact open in its affine spectrum.
  Conversely an open embedding in an affine scheme plus compactness supplies
  `Scheme.IsQuasiAffine.of_isImmersion`. No such hypothesis is made on U.
- A and B: the existing bundled global-section rings `Γ(U, ⊤)` and `Γ(V, ⊤)`.
- Restriction r: `u.appTop`. As u is the given open immersion, this is exactly
  pullback/restriction of global functions along its identification with its image.
- j_U and j_V corresponding to identity maps: `U.toSpecΓ` and `V.toSpecΓ`, the
  units of the recorded `ΓSpec.adjunction`; no arbitrary affinization maps occur.
- q: the existing contravariant spectrum map `Spec.map u.appTop`.
- Unit locus X_h: `X.basicOpen h`; `Scheme.mem_basicOpen_top` identifies this
  with invertibility of the germ, including on empty schemes and zero sections.
- j_V open: first conjunct `IsOpenImmersion V.toSpecΓ`.
- Commutativity: `U.toSpecΓ ≫ Spec.map u.appTop = u ≫ V.toSpecΓ`.
- H: `Set.range (u ≫ V.toSpecΓ)`. Its openness is the third conjunct, making
  explicit the node's wording "the open subscheme H".
- Index I: the pair of binders `(g : Γ(V, ⊤))` and proof that
  `(PrimeSpectrum.basicOpen g).carrier ⊆ Set.range (u ≫ V.toSpecΓ)`.
  This quantifies exactly over the subtype specified in the node, without
  defining a duplicate index notion or choosing a smaller covering family.
- D(g) covers H: the displayed equality of H with the union over these binders.
  `PrimeSpectrum.basicOpen` is the actual prime nonvanishing locus; `.carrier`
  merely makes its coercion to a set explicit.
- For every g in I: the universal quantifier and the same subset antecedent.
- V_g contained in u(U): `(V.basicOpen g : Set V) ⊆ Set.range u`.
- V_g affine: `IsAffineOpen (V.basicOpen g)`.
- j_V induces V_g ≅ D(g): an isomorphism between the existing open subschemes,
  with `e.hom ≫ D(g).ι = (V.basicOpen g).ι ≫ V.toSpecΓ` (the D(g) inclusion
  and scheme restriction are explicitly qualified as `Scheme.Opens.ι` and
  `Scheme.Opens.toScheme` to fix the ambient scheme).
- f = r(g): the term `u.appTop g` throughout.
- U_f = u⁻¹(V_g): `U.basicOpen (u.appTop g) = u ⁻¹ᵁ V.basicOpen g`.
- q⁻¹(D(g)) = D(f): the displayed equality of opens under `Spec.map u.appTop`.
- u restricts to U_f ≅ V_g: the second existential isomorphism, with
  `e.hom ≫ (V.basicOpen g).ι = (U.basicOpen (u.appTop g)).ι ≫ u`.
  Both compatibility equations specify the induced maps, rather than merely
  unrelated isomorphisms of the underlying schemes.
- The U_f are affine: `IsAffineOpen (U.basicOpen (u.appTop g))`.
- They cover U: `∀ x : U, ∃ g : Γ(V, ⊤), ... ∧ x ∈ U.basicOpen (u.appTop g)`.

Dependency declarations used, with their actual sources and signatures read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme.basicOpen`,
  `Scheme.mem_basicOpen_top`, `Scheme.preimage_basicOpen` and its top variant.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the localization-away open-immersion instance is also a proof input.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `AlgebraicGeometry.ΓSpec.adjunction`
  (the recorded mathlib_match for morphisms into affine schemes),
  `Scheme.toSpecΓ`, `Scheme.toSpecΓ_naturality`, and its basic-open preimage lemma.
- `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`,
  `Scheme.IsQuasiAffine.of_isImmersion`, the canonical-map open-immersion and
  separatedness instances, and the basic-open basis. This module publicly
  supplies all four recorded statement dependencies and all proof inputs.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: the recorded basis and
  localization-away range/open-embedding declarations, read in full.
- `Mathlib.AlgebraicGeometry.Restrict`: the existing `Scheme.Opens.toScheme`
  and `Scheme.Opens.ι`, used to express each induced isomorphism.

All statement dependencies are reused through their recorded Lean declarations
or Mathlib matches. The sole public import is
`Mathlib.AlgebraicGeometry.QuasiAffine`, which exposes these modules and proof
leaves transitively. No dependency repair, new node, or statement correction is
needed. No STATEMENT-DISPUTED finding.

Edge cases checked before writing: U empty (H empty; nilpotent g still index
empty charts); V empty (all schemes and covers empty); g zero or nilpotent
(D(g) and both chart domains empty, and the empty scheme is affine); g a unit
(which is an index precisely when H is the whole spectrum); U=V; V affine;
V quasi-affine but non-affine, e.g. the punctured affine plane; and a
non-quasi-compact open U in an affine V. Nothing restricts I to a finite set,
requires a nonempty chart, or adds compactness of U. In particular, the final
coverage quantifier permits vacuous coverage of the empty source.

Searches (through prescribed msearch.py, Q147/item; no existing declaration
states the full conjunction):

- LeanFinder: "Open immersion into a quasi-affine scheme admits a common cover
  by principal affine opens from global sections of the target". Eight hits:
  canonical open immersion, openCoverBasicOpenTop, basis and general affine-open
  results. Those cover a quasi-affine scheme, not all target sections adapted
  to this open immersion with both comparison identities.
- LeanSearch: "open immersion quasi affine common principal affine cover
  comparison canonical affinization map". Eight hits, including the same
  canonical open immersion and affine-opens equivalence; none states this item.
- Loogle: "AlgebraicGeometry.QuasiAffine, AlgebraicGeometry.Scheme.toSpecΓ,
  AlgebraicGeometry.Scheme.basicOpen". No hits, unknown first identifier;
  the actual class was located and read by grep/LeanFinder as above.
- msearch grep: `toSpecΓ|IsQuasiAffine|basicOpen.*[Ii]so|iso.*[Bb]asicOpen`,
  Mathlib AlgebraicGeometry. Hits on restriction, spectra and canonical maps;
  existing constructions reused. Direct reading also checked QuasiAffine.lean
  and the complete relevant GammaSpecAdjunction/Scheme/OpenImmersion signatures.
- rg in project `lean/WeilConjectures` and `lean/Sheaf`: searched canonical-map,
  quasi-affine, principal comparison and common-principal-cover names/concepts;
  searched the literal item id in WeilConjectures. No matching item declaration.
  `QuasiAffineOpenAffinizationSquare.lean` is a different result (a pullback with
  both schemes quasi-affine) and is downstream of this common-chart statement.
  CanonicalAffineChartsQcOpenImmersion and other nearby files also state
  different results. The proposed theorem name is absent from Mathlib, both
  project roots and dag/lean_names_upstream.json.
- No matching released repair-note filename was found.

Validation: prescribed scompile.py compiled the sandbox probe and the actual
library module cleanly. Early probes corrected only coercion notation for the
prime distinguished open: its explicit `.carrier` avoids a coercion failure
against the definitionally equal underlying scheme. No mathematical clause
was changed. Every variable is explicit; autoImplicit is false. All lines
are at most 100 characters.

## Second reading by Q147

I reopened the node and final module for a separate self-review. No independent
worker was started, as the dispatcher explicitly prohibits subagents; the
maintainer's independent delivery review is still required.

The binders impose exactly schemes, an open immersion, and quasi-affineness of
V. I specifically checked that the source U does not acquire quasi-affineness
or compactness. The global-section restriction, canonical maps, and Spec r
are Mathlib's actual constructions. Both occurrences of the indexing predicate
and the coverage predicate agree with D(g) ⊆ H. The union is equality, not
merely a one-sided cover. Each g has containment, affineness, an isomorphism
induced by j_V, both preimage identities, an isomorphism induced by u, and
source-chart affineness. The final pointwise coverage uses exactly those g.
The added explicit openness of H spells out the node's open-subscheme clause.
The existential isomorphisms include the compatibility equations that rule out
arbitrary replacements of the canonical restriction maps. The only changes
found necessary during reading/compilation were elaboration of D(g)'s carrier
and explicitly qualifying the two scheme-open constructions. No node wording
or dependency field was changed.
