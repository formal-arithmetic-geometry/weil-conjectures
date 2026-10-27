## Worker report

States `lem-sfb-two-term-cofactor-naturality` in
`Sheaf.LinearAlgebra.TwoTermCofactorNaturality`. No statement correction, new node,
or dependency repair is made. The only added statement dependency is the already
landed `lem-trf-surjective-two-term-determinant-calculus`, previously a proof
dependency: its two-term complexes and canonical normalized maps occur in the
signature. The natural-language statement and all proof fields remain unchanged.

The previous stale-assignment diagnosis was mistaken: the Q06 report explicitly
says **Stage-1 delivery**, and the current node has `reviewed`, not a Lean record.
Its eight-step proof split is retained. This delivery supplies the still-missing
stage-2 statement rather than splitting the node again.

The module contains real definitions and two postponed theorems, each with a
source and complete proof description. `existsUnique_twoTermCofactorPresentation`
asserts existence and uniqueness of the cofactor construction, including its
canonical exterior identifications. `TwoTermComplex.cofactorPresentation` selects
from this uniqueness theorem, not from an undetermined existence theorem.
`twoTermCofactor_naturality` supplies the uniquely normalized determinant and
zeroth-cohomology comparisons and their naturality equation for every derived
isomorphism. All proofs remain `sorry` as required for this stage.

### Hypothesis and clause correspondence

| Node | Lean |
| --- | --- |
| Arbitrary commutative ring A | `{R : Type u} [CommRing R]`; neither nontriviality nor a field assumption appears. |
| E = [P -> Q] in degrees -1,0 | Recorded `Module.TwoTermComplex` with `neg`, `zero`, `differential`; `cofactorComplex` is Mathlib's actual `HomologicalComplex.double` at the integer indices -1 and 0. |
| Finite projective terms | Separate `Module.Finite` and `Module.Projective` instances on each term. No freeness is assumed. |
| Ranks c,c+1 at every prime, c >= 0 | `c : ℕ`, `hneg` and `hzero`, universally over `PrimeSpectrum R`, with Mathlib's `Module.rankAtStalk`. |
| D(E) = dual(top exterior P) tensor top exterior Q | `E.cofactorLine c` is literally `Dual R (⋀[R]^c E.neg) ⊗[R] (⋀[R]^(c+1) E.zero)`, in the specified order. |
| Dual means Hom(-,R) | Recorded Mathlib `Module.Dual`. |
| coker(u), identified with H^0(E) | `E.cofactorCokernel` is `E.zero ⧸ LinearMap.range E.differential.hom`. |
| Map w_E is A-linear | `TwoTermCofactorPresentation.map : E.cofactorCokernel →ₗ[R] E.cofactorLine c`. |
| Local wedge formula for every basis and lift | `TwoTermCofactorPresentation.formula` contracts the dual factor against every `x : ⋀[R]^c E.neg`, and gives `(ExteriorAlgebra.map u x.val) * ExteriorAlgebra.ι R v` for every lift `v`. On a local basis take x to be its full wedge: evaluation of the dual basis generator is 1, giving exactly the node's formula. Conversely this local formula gives the contraction identity for every x by linearity. |
| Independence of basis, lift, and cover | The map is on the actual quotient, so all representatives of the same class have the same value. The contraction identity is basis-free. `Nonempty (Unique (TwoTermCofactorPresentation E c))` asserts existence and uniqueness of the entire normalized construction; the docstring gives the basis-change cancellation and cover-gluing argument. |
| E' of ranks c',c'+1 | Independent `F`, `c'`, four finiteness/projectivity instances, `hneg'`, `hzero'`; no equality c=c' is imposed. The same construction theorem applies to F. |
| Arbitrary isomorphism a in D(A-Mod) | `a : DerivedCategory.Q.obj E.cofactorComplex ≅ DerivedCategory.Q.obj F.cofactorComplex`, with the recorded `DerivedCategory` and explicit chosen localization universe w. |
| Determinant comparison normalized by kernel-first exact sequences and differential trivialization | `TwoTermCofactorGoodDiagram.determinant` is `C.lineIso` inverse, followed by the inverse normalized left-leg comparison, the normalized right-leg comparison, and `C'.lineIso`. Both leg maps are the existing `kernelNormalizedDeterminantMap`, whose defining predicate uses the kernel-first exact-sequence maps and the exterior map of the kernel differential. |
| D(a) is the stipulated comparison, not an arbitrary map | The theorem constructs a **unique** pair p, and requires `p.1 = d.determinant C C'` for **every** good diagram d representing a. It also asserts that at least one such diagram exists, so this characterization is not vacuous. This is precisely the comparison definition in Stacks 0FJM, also the affine normalization stipulated for the scheme determinant in the node. |
| H^0(a) under the cokernel identifications | The second component p.2 is a linear equivalence on the actual cokernels, uniquely characterized for every good diagram by `p.2([b^0 x]) = [t^0 x]`. Since b is a surjective quasi-isomorphism, this is exactly `H^0(a) H^0(b) = H^0(t)`, and determines H^0(a) on every cokernel element. |
| D(a) composed with w_E = w_E' composed with H^0(a) | The final clause is literally `p.1.toLinearMap.comp C.map = C'.map.comp p.2.toLinearMap`. |
| No injectivity, regularity, or reducedness assumptions | None occur. The existing `TwoTermMap.QuasiIso` checks both kernel and cokernel cohomology, rather than requiring either differential to be injective. |

The good-diagram presentation is an equivalent concrete characterization of the
node's two canonical comparison maps, not a restriction to surjective derived
isomorphisms: **every** derived isomorphism a is quantified, and existence of the
diagram is a conclusion. Its middle complex is finite projective but is not
required to have globally constant ranks. Both legs have actual chain-map
realizations, their components are identified with the two-term maps, and the
relation `Q.map leftChain ≫ a.hom = Q.map rightChain` specifies exactly a.

The canonical `negIso` and `zeroIso` bridge the existing socle determinant model
to the node's literal top exterior powers. Their equations preserve the inclusion
into the exterior algebra, so neither is an arbitrary choice of a line
isomorphism. `lineIso` uses ordinary tensor symmetry, with no graded sign. No
second determinant functor, alternative exterior algebra, or alternative derived
category is introduced. The scheme determinant theorem is imported as the
recorded statement dependency; its stipulated affine normalization is expressed
by the existing algebraic kernel-first maps and the good-diagram prescription.

### Dependency declarations read and used

- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, including its
  direct-summand/lifting interpretation.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra`,
  `ExteriorAlgebra.ι`, `exteriorPower`; `Mathlib.LinearAlgebra.ExteriorPower.Basic`
  supplies the precise exterior-power types used by the construction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and its localization interface.
- `Sheaf.TraceFormula.TwoTermPerfectDeterminant`:
  `AlgebraicGeometry.exists_twoTermPerfectDeterminantData`; read the theorem and
  `TwoTermPerfectDeterminantData`, including `modelIso`, `acyclic`, and
  `twoTermDeterminantIso`, in the public data module. The item's extra kernel-first
  normalization is implemented by the following already recorded interface.
- `Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus`:
  `Module.TwoTermComplex`, `Module.TwoTermMap`, `TwoTermMap.QuasiIso`,
  `IsKernelNormalizedDeterminantMap`, `kernelNormalizedDeterminantMap`, and
  `surjective_two_term_determinant_calculus`. Read their full signatures,
  normalization and proof docstrings.
- `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`:
  `Module.determinantModule`, the existing exterior socle; its exact-sequence
  module provides `IsDeterminantExactSequenceMap` and exterior-inclusion formulas.

Proof-only imports retain every stated proof dependency: exterior free bases,
finite-projective standard covers, exterior localization, tensor localization,
cover exactness, surjective determinant calculus, bounded-projective
K-projectivity, K-projective derived Hom bijectivity and the scheme determinant.
The proof docstrings spell out all eight DAG proof steps, including dual
localization, basis/lift independence, gluing, the surjective kernel-first
calculation, the good enlargement, and cancellation of H^0(b).

### Edge cases

- Zero ring: `PrimeSpectrum R` is empty, so rank assertions are vacuous as in the
  node. All R-modules, maps and relevant equivalences are unique. No
  `[Nontrivial R]` excludes this case.
- c=0 or c'=0: the zeroth exterior power and its dual are retained, and the
  contraction formula becomes the canonical identity on the rank-one term.
- u=0 with c>0: the positive cofactor wedge is zero; the definition still gives
  the zero map. No injectivity condition has slipped into the cokernel.
- Nonreduced A=k[epsilon]/(epsilon^2), u(a)=(epsilon*a,0): the formula is
  w([x,y])=epsilon*y and is well-defined even though u has a kernel. No step
  cancels epsilon.
- Characteristic two: alternation means v wedge v=0; no division by 2 appears.
- Nonfree projectives and varying rank of the middle good complex: global bases
  are not required anywhere. The endpoint ranks are stalk ranks; socle/exterior
  identifications are normalized by their actual inclusions.
- Arbitrary derived isomorphisms: existence of a good diagram is proved as a
  conclusion, rather than imposed as an extra hypothesis. All site-free module
  universes u,v and the localization universe w are explicitly bound.

### Searches and source checks

Actual searches run with `msearch.py NI lem-sfb-two-term-cofactor-naturality`:

- LeanFinder: `cofactor map from cokernel of two term finite projective complex
  to determinant natural under derived isomorphisms` — eight results about
  projective resolutions, their cokernel coforks and derived-zero maps; no match.
- Loogle: `ExteriorAlgebra.ιMulti, Module.Dual` — zero results.
- Mathlib grep: `cofactor|Cofactor|determinant.*coker|coker.*determinant` — nine
  results, about square-matrix adjugates and the free-complement extraction maps
  `exteriorPower.cofactorLinear`/`cofactorToLeft`; none states this compatibility.
- LeanSearch: `cofactor map of two term finite projective complexes invariant
  under quasi-isomorphisms` — eight results about quasi-isomorphisms and derived
  localization; no cofactor/determinant compatibility theorem.

Repository `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for
`cofactor`, `Cofactor`, `TwoTermComplex`, `kernelNormalizedDeterminantMap`,
`cofactor.*complex`, `cofactor.*cokernel` and the exact node id found the recorded
surjective determinant calculus but no cofactor map or this naturality theorem.
The new names have no collisions in those sources or `dag/lean_names_upstream.json`.
`tools/blueprint_refs.py search cofactor` returned zero blueprint nodes. No repair
note exists for this item. The example `CompactObject.lean` has been withdrawn
and contains no declarations; its recorded node and the current module headers
were read for the delivery conventions.

Read local source `literature/stacks-project/duality.tex` at `lemma-determinant`
(Tag 0E9Y), including the displayed formula and omitted well-definedness, and
`more-algebra.tex` at `lemma-determinant-two-term-complexes` (Tag 0FJM), including
its explicit good diagram. The first source's separate isomorphism-locus claim
and sequence injectivity are not imported: this agent-formulated node expressly
extends the formula to noninjective differentials and asserts its naturality.
No statement dispute was found.

Validation: the prescribed `scompile.py` compiled the sandbox and actual library
module cleanly, with 9.9 s and 6.5 s reported respectively. No warnings or errors
remain. No live repository files or launcher tools were modified; no Git command
or global build was run by the worker.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
