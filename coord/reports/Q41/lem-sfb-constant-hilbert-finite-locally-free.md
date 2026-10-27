## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantHilbertFiniteLocallyFree` states
`AlgebraicGeometry.constant_hilbertPolynomial_iff_finiteLocallyFree` with its only
proof `sorry`. No definition or additional node is introduced. The accepted stage-1
split and every field of the node except `lean` are preserved.

The inherited ending was a stage-1 unchanged-split refusal. The live node is split,
reviewed by Q90, has no Lean binding, and appears at stage 2 in `coord/queue.tsv`.
The stage-handoff paragraph of `coord/brief-stage2.md` explicitly authorizes this
stage-2 statement without reopening the stage-1 split. No repair note exists.

Hypothesis and clause correspondence:

- Any base and source schemes: `{Z T : Scheme.{u}}`, with an explicit arbitrary
  universe `u`. There is no Noetherian, reducedness, connectedness, nonemptiness,
  characteristic or field hypothesis.
- Nonnegative integers n and d: `(n d : ℕ)`.
- The specified embedding: `i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); T)` and
  `[IsClosedImmersion i]`. The ULift places the finite coordinate set in the
  scheme universe; it still has exactly n+1 coordinates, including when n=0.
- The map p is definitionally the composite of i and the structural projection,
  written `i ≫ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T)` throughout. Thus there is no
  arbitrary unrelated p and no extra factorization hypothesis.
- Flatness: `[Flat (i ≫ ...)]` uses the node's recorded Mathlib flatness class.
- Finite presentation: all three stated components are present, as
  `[LocallyOfFinitePresentation (i ≫ ...)]`, `[QuasiCompact (i ≫ ...)]` and
  `[QuasiSeparated (i ≫ ...)]`.
- Every fibre polynomial equals the constant d: the first conjunct uses
  `HasProjectiveFibreHilbertPolynomial p i (Over.mk (𝟙 T)) ⊥
  (Polynomial.C (d : ℚ))`. This is the dependency's exact predicate. With W=Z,
  B=S=T, f=p, identity base change, and the zero ideal, its closed family is
  canonically Z itself: pullback p (identity T) is canonically Z, and quotient
  by the zero ideal is canonically that pullback. Its induced polarization is i.
  Unfolding the predicate gives every t, some natural threshold, all subsequent
  m, with the fibre Euler characteristic equal to the constant d. On these
  projective closed fibres, its dependency explicitly identifies this with the
  geometric homogeneous-coordinate Hilbert polynomial; residue extension
  preserves the dimensions. This neither introduces a choice of polynomial nor
  repeats the predicate in a private definition.
- The first iff concludes `p.IsFiniteLocallyFreeOfDegree d`, exactly the recorded
  class extending finiteness, flatness, local finite presentation, and
  `∀ t, p.fiberDegree t = d`.
- The second iff renders the node's equivalent pushforward description:
  `p.IsFiniteLocallyFreeOfDegree d ↔ IsFinite p ∧
  SheafOfModules.IsFiniteLocallyFreeOfRank ... d`. The sheaf is precisely
  `(Scheme.Modules.pushforward p).obj (SheafOfModules.unit Z.ringCatSheaf)`.
  The recorded finite locally free sheaf class asks for a local free presentation
  with each basis indexed by a type equivalent to `Fin d`, hence locally
  isomorphic to O_T^{⊕d}. No tensor comparison or choice of trivialization is
  asserted beyond the node.
- The final implication renders the node's d=0 interpretation:
  `d = 0 → (p.IsFiniteLocallyFreeOfDegree d ↔ IsEmpty Z)`.
  Coupled with the two preceding equivalences this covers each condition.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalks).
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective:
  `AlgebraicGeometry.IsHProjective`; its public projective-space API gives
  `ProjectiveSpace` and its structural projection. Read the complete class
  signature and docstring; the theorem specifies the embedding itself rather
  than assuming another projectivity witness.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` expressing the node's stalkwise convention.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; its module includes the
  quasi-compact and quasi-separated classes also used in the signature.
- Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial:
  `AlgebraicGeometry.HasProjectiveFibreHilbertPolynomial`, read with its full
  signature and docstring and its body. The identity-base-change specialization
  is available directly, so no dependency repair or replacement predicate is
  needed.
- WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:
  `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`,
  and `Scheme.Hom.fiberDegree`.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, whose full class signature and
  docstring were read. This is the same sheaf-rank class used in the recorded
  proof dependency `finiteLocallyFree_structureSheaf_properties`.

All modules of recorded proof dependencies are imported without public exposure
unless already needed publicly for the signature. Mathlib-match files are also
imported. The three proof dependencies with no current Lean or Mathlib binding
(`lem-sfb-coherent-zero-dimensional-support`,
`lem-sfb-projective-field-coordinate-euler-polynomial`,
`lem-sfb-projective-hilbert-polynomial-dimension`) have no import yet and are
named in the proof docstring. They are proof prerequisites, not missing notions
needed to type this statement. No import cycle was observed by compilation.

Edge cases checked before writing:

- Empty T forces Z empty. The universal fibre predicate and fibre-degree
  conditions are vacuous for every d, and the empty open cover makes every
  local rank condition hold. In particular the theorem never claims d=0 merely
  from Z being empty when d is arbitrary.
- When d=0, a nonempty projective fibre has nonzero Hilbert polynomial and cannot
  satisfy the predicate. All fibres empty implies Z empty. The zero sheaf is
  locally free of rank zero, including over the empty base.
- n=0 is retained (one coordinate). A closed flat finitely presented subscheme
  of P^0_T may have empty fibres; no surjectivity is assumed.
- A nonreduced double point in P^1 over a field has d=2 and is included. The
  rank is section dimension, not cardinality of the topological fibre.
- A positive-dimensional projective fibre has nonconstant nonzero polynomial
  and fails the first condition. A disconnected base with different nonempty
  fibre lengths fails the single fixed-degree condition on both sides.
- Nonreduced and non-Noetherian bases are allowed. Flatness and all three
  finite-presentation components are explicitly retained, so the theorem does
  not use a reduced-base constant-length flatness criterion.

Searches:

- msearch.py leanfinder: "A flat finitely presented closed subscheme of projective
  space has constant fibre Hilbert polynomial d if and only if it is finite
  locally free of degree d" returned eight hits, including
  Module.Flat.projective_of_finitePresentation, Proj properness, and
  Module.freeLocus_eq_univ_iff. None states the geometric equivalence.
- msearch.py loogle: `"Hilbert", "Flat"` returned zero hits.
- msearch.py leansearch: "A projective flat finitely presented family has constant
  Hilbert polynomial d exactly when it is finite locally free of degree d"
  returned eight hits, including Polynomial.hilbertPoly and module flatness,
  projectivity and free-locus results. No match.
- msearch.py grep: `hilbertPolynomial|hilbert_polynomial|HasProjectiveFibreHilbertPolynomial`
  in Mathlib/AlgebraicGeometry found no equivalent declaration.
- rg in lean/WeilConjectures and lean/Sheaf for constant Hilbert polynomials,
  HasProjectiveFibreHilbertPolynomial, and IsFiniteLocallyFreeOfDegree found
  the existing polynomial predicate and unrelated finite-degree results, but
  no theorem equating the two. Searching the exact node id upstream found no
  declaration. In particular `flat_of_fiberDegree_eq` requires reducedness and
  already assumes finiteness; it is not this statement.

Sources opened locally: Stacks more-morphisms.tex
`lemma-characterize-finite` (02LS); morphisms.tex `definition-finite-locally-free`
and `lemma-finite-flat` (02KB); varieties.tex `lemma-hilbert-polynomial-H0`
(08AE); coherent.tex `lemma-coherent-support-dimension-0` (0B3J).
The theorem docstring retains the accepted eight-step proof, including the
reviewer's projective-space scalar-extension repair. No statement fault or
STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the sandbox and actual library module separately
on the server (6.9 s and 8.8 s), with no errors or unexpected warnings.

## Second reading by Q41

I reread the final node and final signature after the first clean compile. This
is a second pass by the dispatched worker, not a claim of independent-agent
review; the brief forbids starting other agents and assigns independent review
to the maintainer. I checked the binders, three finite-presentation components,
the actual composition defining p, and the identity-base-change/zero-ideal
specialization of the recorded fibre predicate. The two iff clauses and final
zero-degree implication render all conclusions. No assumption on the base or
on nonemptiness was introduced. The zero-degree implication is one-way in d,
so the empty-base case permits every degree as required. The rank class uses
exactly d local generators in a local free presentation, not a bound on rank.
No mismatch was found and no statement correction or dependency module was
needed. Every variable and universe is explicit (`set_option autoImplicit false`).
