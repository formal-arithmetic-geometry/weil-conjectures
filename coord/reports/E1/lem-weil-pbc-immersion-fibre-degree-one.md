## Worker report

The module `Sheaf.AlgebraicGeometry.ImmersionFiberDegreeOne` states
`AlgebraicGeometry.Scheme.Hom.immersion_fiber_degree_one`, with its only proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypotheses and clauses, checked against the node:

- Arbitrary schemes and their morphism: `{Z X : Scheme.{u}} (j : Z ⟶ X)`;
  `u` is explicitly declared and unrestricted.
- Immersion, a closed immersion followed by an open immersion: `[IsImmersion j]`.
  Mathlib's `IsImmersion.isImmersion_iff_exists` states exactly this factorization,
  with `IsClosedImmersion g₁`, `IsOpenImmersion g₂`, and `g₁ ≫ g₂ = j`.
- The integer one bounds all fibre degrees: `BoundsFiberDegrees j 1`. Unfolding the
  recorded dependency gives `∀ x, IsFinite (j.fiberToSpecResidueField x) ∧
  (j.fiberToSpecResidueField x).finrankΓ ≤ 1`, rendering BOTH finiteness over κ(x)
  and the dimension bound on global sections. Upstream `finrankΓ` uses the algebra
  on global sections induced by the specified projection, not an arbitrary algebra.
- Every point x: `∀ x : X`.
- Outside j(Z) the fibre is empty: `x ∉ Set.range j → IsEmpty (j.fiber x)`.
  `IsEmpty` means no underlying points, which is precisely an empty scheme.
- On j(Z) it is Spec κ(x) over κ(x): `x ∈ Set.range j →
  IsIso (j.fiberToSpecResidueField x)`. This is an isomorphism of the actual
  structure morphism, so includes compatibility with the base.
- In particular universally bounded: `HasUniversallyBoundedFibers j`, the recorded
  existential degree-bound predicate. The witness in the natural-language proof is one.

Dependency declarations read and used:

- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; the immersion notion is
  `AlgebraicGeometry.IsImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
  related by `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`. Both immersion constituents are used
  through the existing `IsImmersion` notion, rather than redefining factorization.
- `def-weil-pbc-fibre-degree-bound`: `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegrees`
  and `AlgebraicGeometry.Scheme.Hom.HasUniversallyBoundedFibers`,
  `Sheaf.AlgebraicGeometry.FiberDegreeBound`, imported directly.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`, `Mathlib.AlgebraicGeometry.Fiber`.
  Their definitions are the specified pullback and second projection. Read also `fiberHomeo`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`,
  `Mathlib.AlgebraicGeometry.ResidueField`, used inside the canonical fibre projection;
  this is literally the stalk modulo its maximal ideal.
- Read upstream `Scheme.Hom.ΓAlgebra` and `Scheme.Hom.finrankΓ` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, imported transitively by
  the recorded degree-bound module, to verify the dimension and scalar structure.

Edge cases checked before writing: empty Z gives empty fibres of dimension zero;
empty X has no points (and any scheme mapping to it is empty), so the universal
quantifiers are vacuous and one remains a bound; an identity or nonempty fibre gives
an isomorphism and dimension one. Nonreduced ambient schemes and all characteristics
are allowed. No finiteness, affine, quasi-compact, or nonemptiness hypothesis is added.
The residue field is a genuine field even for nonreduced schemes. No independent
universe of test schemes is introduced.

Source read: [Stacks Tag 03J9](https://stacks.math.columbia.edu/tag/03J9), Lemma 29.58.7,
says an immersion has universally bounded fibres and its proof supplies n = 1.
The local `literature/stacks-project/morphisms.tex` is absent on this machine, so the
source was read on the official Stacks page. The node expands the source into the
five elementary steps preserved in the theorem docstring. No node fault or
STATEMENT-DISPUTED issue was found.

Searches performed through the prescribed `msearch.py` (actual records in searches.jsonl):

- LeanSearch: “An immersion of schemes has finite fibres of degree at most one”.
  Service unavailable (Internal Server Error); no mathematical verdict asserted.
- LeanFinder: “An immersion of schemes has fibres empty or isomorphic to the spectrum
  of the residue field”. Eight ingredient hits: residue-field preimmersions,
  fibre inclusion preimmersion, IsImmersion, embedding facts; no matching theorem.
- Loogle: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`.
  Successful query, zero hits.
- Mathlib grep, AlgebraicGeometry: `BoundsFiberDegrees|HasUniversallyBoundedFibers|finrank|isIso.*fiber`.
  Ten hits on residue degrees, flat rank, and elliptic curves, none stating this node.
- Project and source rg: `BoundsFiberDegrees|HasUniversallyBoundedFibers|immersion.*fiber|fiber.*immersion`.
  Found the recorded degree predicates and composition/base-change/field-point lemmas;
  upstream mentions invariance under open base change, not this immersion theorem.
- Source grep for the exact blueprint id found nothing.
- Full signatures/docstrings of every recorded dependency were opened; there is no
  private copy of any notion and no exact existing declaration to reuse.

Validation: server single-file compilation and delivery dry run are run as the final checks.
The independent second reader will supply their own section and deliver.

## Second reading by E1

I independently read the sandbox node and module, each of the five statement-dependency
nodes, their actual declarations, and the source. The local Stacks .tex checkout is
absent, so I read the official upstream
[morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex),
section `section-universally-bounded`, definition `definition-universally-bounded`,
and lemma `lemma-immersion-universally-bounded`, together with
[Tag 03J9](https://stacks.math.columbia.edu/tag/03J9).
The section has no Noetherian, quasi-compact, separated, characteristic, or base-field
standing assumption on the morphisms; its initial finite scheme over a field explains
the degree notion, rather than restricting the later schemes. The source asserts the
bound one; the node explicitly supplies its elementary empty-or-isomorphism explanation.

My statement inventory and correspondence:

1. Objects: schemes Z and X, and a morphism j : Z → X. Lean:
   `{Z X : Scheme.{u}} (j : Z ⟶ X)`. Exact; `universe u` is explicit.
2. Hypothesis: j is an immersion, a closed immersion followed by an open immersion.
   Lean: `[IsImmersion j]`. Exact: I opened
   `IsImmersion.isImmersion_iff_exists`, whose signature is the existential
   factorization with `IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = j`.
   I also read `IsClosedImmersion` (closed embedding and surjective stalk maps)
   and `IsOpenImmersion` (the locally ringed space open immersion). These are
   the dependency nodes' recorded Mathlib notions, with no additional hypothesis.
3. Objects: each x ∈ X, κ(x), and Z_x = Z ×_X Spec κ(x), over κ(x) by the second
   projection. Lean: `x : X`, `X.residueField x`, `j.fiber x`, and
   `j.fiberToSpecResidueField x`. Exact: the actual definitions are respectively
   the residue field of the local stalk, the pullback along `X.fromSpecResidueField x`,
   and `pullback.snd`. I also opened `fiberHomeo` onto the inverse image of {x}.
4. Conclusion: every fibre is finite over κ(x). Lean: the `IsFinite
   (j.fiberToSpecResidueField x)` conjunct of `BoundsFiberDegrees j 1`.
   Exact: I opened the imported `FiberDegreeBound.lean`, rather than relying on its name.
5. Conclusion: dim over κ(x) of global sections is at most one. Lean: the
   `(j.fiberToSpecResidueField x).finrankΓ ≤ 1` conjunct of that same predicate.
   Exact: upstream `finrankΓ` is `Module.finrank` with the `ΓAlgebra` induced by
   `(Scheme.ΓSpecIso _).inv ≫ h.appTop`; it uses precisely this projection's scalars.
   Finiteness is retained as a separate conjunct, so finrank's infinite-dimensional
   default cannot weaken the assertion.
6. Conclusion: outside j(Z) the fibre is empty. Lean:
   `∀ x : X, ... (x ∉ Set.range j → IsEmpty (j.fiber x)) ...`.
   Exact: `Set.range j` uses the underlying map on points; an empty underlying
   scheme space is precisely the empty scheme, including its zero structure sheaf.
7. Conclusion: on j(Z) the fibre is Spec κ(x) over κ(x). Lean:
   `x ∈ Set.range j → IsIso (j.fiberToSpecResidueField x)`.
   Exact: asserting the actual structure projection is an isomorphism ensures
   compatibility with κ(x), not merely an abstract isomorphism of schemes.
8. Conclusion: in particular the fibres are universally bounded. Lean:
   `HasUniversallyBoundedFibers j`. Exact: its recorded definition is
   `∃ n : ℕ, BoundsFiberDegrees j n`, with witness one supplied by the first clause.
   All clauses have the node's quantifier order and scope; the separate universal
   degree and case assertions are equivalent to putting them under one ∀ x.

Edge cases: empty Z gives empty fibres with zero global sections and degree zero;
empty X makes the point quantifiers vacuous and still permits bound one. The
identity gives degree one and the required projection isomorphism. Nonreduced
ambient schemes and arbitrary characteristics are included; there is no hidden
field choice for X or Z. There is no index set or variable n in this theorem:
zero degree is admitted by its natural-number bound predicate. The single arbitrary
scheme universe u also covers any pair after a common universe lift and introduces
no restricted test-scheme universe. No nonemptiness or global finiteness is required.

Independent searches (different queries from the worker; recorded in searches.jsonl):

- LeanFinder: "locally closed embedding of schemes residue field fiber is an
  isomorphism when nonempty". Eight hits, checked as ingredients only: fibre
  projection definitions, residue-field preimmersions, closed immersion of the
  residue map, and the residue-field isomorphism for an open immersion. None is
  this degree-bound theorem.
- Loogle: `AlgebraicGeometry.IsImmersion, CategoryTheory.IsIso`. One hit,
  `AlgebraicGeometry.isIso_of_comp_eq_sigmaSpec`; I opened its full signature.
  It concerns a compact locally closed subscheme of Spec of a product containing
  the coproduct of spectra, not arbitrary fibres of an immersion.
- LeanSearch: "The scheme theoretic fibers of a locally closed immersion are
  finite schemes with global sections dimension zero or one". The service returned
  Internal Server Error, recorded unavailable; no no-match claim is made for it.
- Direct rg over Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf: `immersion.*(degree|finrank|fiber|fibre)` and reversed word order,
  plus `isIso.*fiberToSpec|fiberToSpec.*isIso`. I opened the nearby
  `LocallyQuasiFinite` instance for preimmersions, `isEmpty_pullback_of_disjoint_range`,
  and `fiberDegree_of_isIso`; these are respectively a finiteness ingredient,
  an emptiness lemma with a different hypothesis, and a special case for global
  isomorphisms. None states the item.
- Direct rg for `immersion_fiber_degree_one`, `HasUniversallyBoundedFibers`, and
  `BoundsFiberDegrees`, including dag/lean_names_upstream.json, found the recorded
  predicates and the composition, base-change, and field-point lemmas, with no
  matching immersion statement. No duplicate notion or declaration was found.

H5–H9: no definitions, hollow or otherwise; the only theorem is named and its proof
is `sorry`. The module and declaration docstrings give the source and blueprint id;
the declaration lists all five proof steps with their dependency ids. Imports are
used, the namespace is upstream-compatible, all variables and universes are bound,
and all lines are at most 100 characters. I verified programmatically that the
node's `lean.statement` equals the module signature verbatim.

No mismatches found. No Lean or node changes were needed; this second-reading section
is the only addition. There are no new nodes, dependency modules, or statement
corrections in the delivery, so H12/H13 and correction-citer checks do not arise.
