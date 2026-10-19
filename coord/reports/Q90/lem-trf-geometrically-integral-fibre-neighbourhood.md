## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.GeometricallyIntegralFibreNeighbourhood`
states `AlgebraicGeometry.exists_geometricallyIntegral_fibre_neighbourhood`, with its
whole proof `sorry`. No definitions, additional nodes, dependency repairs, or statement
corrections are needed. The node changes only in `lean`.

Source checked: `literature/stacks-project/more-morphisms.tex`,
`lemma-normal-morphism-irreducible` (Tag 057J),
`lemma-smooth-normal` (Tag 056W), and its application in Tag 057K.
The node is precisely the smooth finite-presentation specialization of 057J.
Tag 055W was also read to check the intermediate spreading result.

Hypotheses and conclusions, clause by clause:

- Schemes Y and S and the morphism h: `{Y S : Scheme.{u}} (h : Y ⟶ S)`.
- Smoothness: `[Smooth h]`.
- Finite presentation: `[LocallyOfFinitePresentation h] [QuasiCompact h]
  [QuasiSeparated h]`, exactly the node's explicit three conditions.
  Smoothness already supplies the first condition, which is displayed to retain
  the stated finite-presentation convention.
- A point of S: `(s : S)`; it need not be a closed point.
- T is an open subscheme of the scheme-theoretic fibre:
  `(T : (h.fiber s).Opens)`. Its canonical embedding is `T.ι`.
- Geometric irreducibility over κ(s):
  `[GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)]`.
- The new scheme and map: `∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S)`.
- Its affineness and étaleness: `IsAffine S₁ ∧ Etale a`.
- A lift of the specified point: `(s₁ : S₁) (hs : a s₁ = s)`.
- The induced residue-field map is an isomorphism:
  `IsIso (a.residueFieldMap s₁)`. Its domain is κ(a(s₁)); `hs` identifies
  this with κ(s). Isomorphism is invariant under that equality transport.
- An open V in the base change: `∃ V : (pullback h a).Opens`.
- Absolute quasi-compactness of the open: `IsCompact (V : Set ↥(pullback h a))`.
  This is not merely quasi-compactness relative to its ambient scheme.
- Every fibre of V → S₁ is geometrically integral:
  `GeometricallyIntegral (V.ι ≫ pullback.snd h a)`.
  The precise equivalence is Mathlib's
  `GeometricallyIntegral.iff_geometricallyIntegral_fiber`; thus this uses the
  node's definition after every field extension, including nonemptiness.
- Equality of the embedded prescribed fibres: the left side is
  `(pullback.snd h a).fiberι s₁ ⁻¹ᵁ V`, the open V cut out on the new
  ambient fibre. The right side is the inverse image of T under the canonical
  comparison from that fibre to `h.fiber s`. This comparison is explicitly
  `pullback.map`, with component maps `pullback.fst h a` to Y,
  `Spec.map (a.residueFieldMap s₁)` to Spec κ(a(s₁)), and `a` on the bases.
  Its two commutativities are the existing pullback condition and naturality
  of `fromSpecResidueField`, in the appropriate orientations. The final
  `eqToHom (congrArg h.fiber hs)` transports the target to `h.fiber s`.
  By pullback pasting, the new ambient fibre is canonically
  `Y_s ×_{Spec κ(s)} Spec κ(s₁)`. Consequently the right side is precisely
  `T ×_{Spec κ(s)} Spec κ(s₁)` as an open subscheme. Equality in the lattice
  of opens retains the embeddings and the induced structure sheaves. No
  arbitrary comparison or existential abstract isomorphism replaces this map.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`,
  `Spec`, and `Spec.map` (scheme and affine-spectrum nodes).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (the recorded smoothness dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- The conventions node intentionally has no declaration; its recorded
  `QuasiCompact` and `QuasiSeparated` classes are written explicitly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its two projections, `pullback.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`, and
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the actual open subschemes are Mathlib `Scheme.Opens`, with canonical `.ι`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `GeometricallyIntegral`, and its imported `GeometricallyIrreducible`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `IsAffine` is the existing Mathlib class; the spectrum definition and
  `IsAffine` docstring/signature were read. It means being isomorphic to Spec
  of a commutative ring, equivalently the canonical map to Spec Γ is invertible.

The declared proof plan is preserved in the theorem docstring. The proof-only
imports include the recorded modules for smooth-geometrically-reduced,
proper/smooth base change, base-change conventions, and the smooth connected
normal integral geometry core. `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
was read using `scompile.py --source`, since it is absent from the older local
upstream source. Its scheme base changes are explicitly the Mathlib pullbacks,
not its module-sheaf base-change functor. The other named proof dependencies
that are Mathlib leaves are available through these imports. The spreading
node `lem-trf-geometrically-connected-fibre-open-spreading` currently has no Lean
record, so there is no recorded module to import for it. It is used only by
stage 3's proof, not by the signature, and is named in the proof docstring.

Edge cases checked:

- Empty S has no s, so the statement has no instance to assert there. Empty Y
  or empty T fails the geometric-irreducibility hypothesis, as intended.
- Integral fibres are nonempty. The conclusion therefore requires V to meet
  every point of S₁, not only s₁; `GeometricallyIntegral` enforces this.
- No quasi-compactness of T was added: the finite-type fibre over a field is
  Noetherian, so its arbitrary open already is quasi-compact. The output V
  is explicitly absolutely quasi-compact.
- No closedness of s, separation of S or Y, Noetherian assumption on the base,
  characteristic restriction, relative-dimension restriction, or field
  perfection hypothesis is present.
- Schemes, residue fields, and pullbacks all use the same arbitrary universe u;
  there is no independent smaller universe restricting field extensions.
- Identity base change has identity residue-field and fibre comparison maps.
  For general a, both component maps of the canonical comparison are fixed
  by h, a, and s₁. The equality is never interpreted through a freely chosen
  automorphism of the ambient fibre.

Searches for an existing statement (all via the prescribed wrappers unless
specified; the full wrapper results remain in sandbox `searches.jsonl`):

- LeanFinder: “A smooth finitely presented family and a geometrically irreducible
  open in a fibre admit an elementary etale neighbourhood with geometrically
  integral fibres”: 8 hits, smooth charts and étale loci only; no spreading.
- Loogle: `"GeometricallyIntegral", "Smooth"`: 0 hits.
- LeanSearch: “Spread a geometrically irreducible open of a smooth fibre to
  geometrically integral fibres over an elementary etale neighbourhood”: 8
  hits, spreading of germ morphisms and open-subscheme integrality, no match.
- Mathlib grep: `geometrically.*[Ii]ntegral|[Gg]eometrically[Ii]ntegral` in
  `AlgebraicGeometry/Geometrically`: 7 hits, the existing definition and its
  elementary equivalences, not the spreading theorem.
- Direct rg of the upstream `WeilConjectures` and project `lean/Sheaf` trees:
  geometric-integrality, fibre-neighbourhood, normal-irreducible, and
  elementary-étale terms. The existing slicing theorems give charts or
  connected fibres; none gives this exact prescribed-open spreading result.
- Direct grep of the upstream tree for the node id: no hits. The upstream
  declaration-name index was also searched with geometric-fibre spreading
  terms; no declaration realizing this statement was found.

No STATEMENT-DISPUTED issue or other node fault was found.

Validation: `scompile.py Q90 lem-trf-geometrically-integral-fibre-neighbourhood`
compiled both sandbox and final library-path checks cleanly, within 60 seconds
per file. One expected named theorem proof is postponed; no data is postponed.
The first compile exposed a coercion ambiguity in the compactness expression
and implicit arguments to `pullback.condition`; both were repaired explicitly.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
