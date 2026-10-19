## Worker report

Existing declaration delivery: `AlgebraicGeometry.isPunctuallyPureOfWeight_artinSchreier`
in `WeilConjectures.WeilSheaf.ArtinSchreierPurity`, read in full through
`scompile.py --source`. No Lean module or new declaration is written. The upstream
module itself identifies this theorem with blueprint `lem-fd-as-purity`.
The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The finite field k0 = Fq is `{k₀ : Type u} [Field k₀] [Finite k₀]`, with arbitrary
  explicit universe `u` in the upstream module. Its characteristic is `ringChar k₀`.
- The coefficient prime is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`;
  these are the coefficient conventions inherited from punctual weights.
  `PadicAlgCl l` is the chosen algebraic closure of the l-adic coefficient field.
- The fixed nondegenerate character is the input `ψ : AddChar k₀ (PadicAlgCl l)`
  specialized to the character in the node. For a fixed nontrivial prime-field
  character `Ψ`, this is `Ψ.compTrace k₀`; the character dependency's closed
  upstream audit records `AddChar.compTrace` and `AddChar.isPrimitive_compTrace`.
  The theorem does not require nondegeneracy, so accepts this particular character.
- The specified `a ∈ k₀ˣ` is supplied to `(a : k₀)` by coercing the specified unit.
  The theorem includes zero as well, but the node's nonzero hypothesis is retained
  verbatim in the DAG. No new stronger node statement is introduced.
- The isomorphism `iota : PadicAlgCl l ≃+* ℂ` is passed as `iota.toRingHom` to
  `(ι : PadicAlgCl l →+* ℂ)`. Its action on coefficient elements is unchanged.
- The scheme is exactly `affineLine k₀`. The conclusion's `artinSchreier ψ a`
  is the pullback by `affineLine.smul k₀ a` of the image of the canonical projector
  `q⁻¹ ∑ c, ψ(-c) σ_c` on the Artin–Schreier pushforward of the constant adic
  Weil sheaf. Thus it is the Weil version of L_{ψ,ax}, with its canonical
  Frobenius structure, not an arbitrary rank-one object.
- The entire conclusion is `(artinSchreier ψ a).IsPunctuallyPureOfWeight ι 0`.
  Unfolding the upstream predicate quantifies over all finite-residue points
  (exactly the closed points on this finite-type finite-field scheme), and
  says every local geometric-Frobenius eigenvalue has norm q_x^(0/2) = 1.
  It asserts purity, not merely an upper weight bound or mixedness.

Dependency declarations read:

1. `def-fd-additive-character`: `AddChar.FiniteField.primitiveChar` in
   `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`, full construction read
   at local lines 212ff; and its closed upstream audit's `AddChar.compTrace`
   and `AddChar.isPrimitive_compTrace` in
   `WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter`, read
   through `scompile.py --source` with full signatures and docstrings.
2. `def-fd-artin-schreier-sheaf`: `AlgebraicGeometry.Etale.artinSchreierSheaf`
   and `artinSchreierSheafOf` in
   `WeilConjectures.FourierTransform.ArtinSchreier`, local lines 437–472.
   Read the current `blueprint_update`: it uses the q-power cover and the
   k0-character projector. The purity theorem uses the adic Weil realization
   `AlgebraicGeometry.artinSchreier` in `WeilConjectures.WeilSheaf.Fourier`
   (lines 817–823), whose projector and scalar pullback were also read in full.
   Both constructions use this same q-power cover, character and projector;
   the latter additionally retains the Weil structure needed for purity.
3. `def-weil-punctual-weights`: read the recorded
   `WeilConjectures.SfIsPunctuallyPureOfWeight` and `SfPunctualEigenvalue`
   in `Sheaf.Paper.AdicPunctualWeights` in full. Also read the closed upstream
   audit's `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` in
   `WeilConjectures.WeilSheaf.Stalk` through `scompile.py --source`.
   Both express the same local geometric-Frobenius eigenvalue norm equality.
   They have different Lean heart types: the Sf definition computes at finite
   presentations in the common-stage heart, while this existing theorem uses
   upstream adic Weil sheaves. No formal identification of the heart types is
   claimed here; subsequent Sf consumers require the stage-3 comparison.
   This is an existing source theorem binding, not a new theorem on the Sf heart.

The existing theorem's proof follows the node's argument: rank-one stalks identify
Frobenius with its trace; the trace theorem gives ψ(Tr(ax)); finite-field character
values are roots of unity, whose images have norm one; the exponent at weight
zero is zero. All its helper proofs are already upstream and are not duplicated.

Edge cases checked: q = 2; closed points of every positive residue degree; zero
trace (eigenvalue 1); p dividing [k0:Fp] (use the full trace-induced character,
not its restriction to Fp); every nonzero scalar; the larger upstream theorem's
zero scalar and trivial character cases (constant rank-one sheaves, also pure).
No empty-point argument or universe restriction makes the conclusion vacuous.

Searches performed (results retained in sandbox searches.jsonl):

- LeanFinder: "Artin Schreier sheaf punctually pure weight zero": eight
  unrelated Witt-vector and condensed-module hits, no Mathlib match.
- Loogle: "IsPunctuallyPureOfWeight, artinSchreierSheaf": no hits; the first
  identifier is absent from Mathlib's index.
- Mathlib grep via msearch: "ArtinSchreier|artinSchreier|PunctuallyPure": no hits.
- LeanSearch: "Artin Schreier sheaf pure weight zero": eight unrelated
  inseparability/Lie-weight/structure-sheaf hits, no match.
- `rg` on upstream WeilConjectures and project lean/Sheaf for
  `isPunctuallyPureOfWeight_artinSchreier|artinSchreier.*[Pp]ur|lem-fd-as-purity`:
  the local Fourier module mentions weight zero; no local purity module.
- `rg` on dag/lean_names_upstream.json for purity names: upstream weight
  definitions and lemmas present. The item's own audit names precisely the
  existing purity theorem and its module. The current live source obtained
  by `scompile.py --source WeilConjectures.WeilSheaf.ArtinSchreierPurity`
  contains the full theorem, its canonical sheaf and the blueprint marker.

No statement correction, new node or dependency repair is needed for this
existing upstream declaration binding. No disputed mathematical assertion.
The delivery wrapper checks the live existing declaration with an import and
`#check`; no module is added or compiled as a new statement.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
