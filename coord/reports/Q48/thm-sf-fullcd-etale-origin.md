## Worker report

The first packet was already landed on `newtargets-dag` by Q19 with the source-based
statement correction and no Lean declaration. This second-reader delivery adds the
missing statement module `Sheaf.Paper.SfFullCdEtaleOrigin` and records its declaration
on the item. The module only states the theorem with `sorry`; no proof or hollow data
is introduced. It uses the canonical finite-coefficient realization and derived direct
image, with the supplied comparison isomorphism from an étale sheaf to the given
pro-étale sheaf. The relative clause quantifies over every scheme morphism `V ⟶ Y`,
so it imposes no finite-type or dimension condition on `V`.

The existing corrected node was read against the current blueprint source and the
Stacks proper-base-change route recorded by Q19. Its hypotheses are: the fixed
algebraically closed finite-field datum, `l ≠ p₀`, finite extension `E/ℚ_l`, positive
level `n`, `d : ℕ`, finite-type `k`-schemes `X̄,Y`, proper finite-type `p`, and
`dim X̄ ≤ d`; its conclusion has the absolute and arbitrary scheme-base-change
cohomology-sheaf vanishings above `2d` for the specified étale-origin coefficient
sheaf. The module renders these through `FiniteCoefficientModules`, the canonical
`finiteCoefficientRealization`, `finiteCoefficientDerivedDirectImage`, and the
canonical finite-coefficient pullback. `G` and `hF` explicitly witness étale origin;
`F` is the pro-étale sheaf whose degree-zero image is tested.

The coefficient quotient is supplied with its finite instance as a binder because the
canonical positive-level finiteness theorem is not registered as a typeclass instance;
this is the same finite-ring datum asserted by the node and does not add a mathematical
hypothesis. The quotient's canonical discrete topology is supplied by module-local
instances, as required by the finite-coefficient site encoding. The scheme structure
maps and `p.IsOver` express “k-schemes”; `IsProper p` supplies properness and finite
type. No Noetherian, separated, constructibility, or universes-equality assumptions
were added.

## Searches

I ran the required semantic search with `msearch.py` (LeanFinder: only ordinary
étale/proper morphism declarations; no cohomological-dimension theorem) and Loogle
(the query returned no matching `rightDerivedFunctor` declaration). Grep over the
slopmaster2 source and the project's `lean/Sheaf` found the existing class-restricted
predicate `AlgebraicGeometry.ProEtale.sfClassFullCohomologicalDimension` and related
FullCD modules, but no theorem for this node. The upstream candidate in
`ExceptionalAdjoint.lean` is sorry-only and has a stronger quantifier, so it is not
attached. I used the existing finite-coefficient interfaces rather than redefining a
site or direct image.

## Second reading by Q48

- Objects and hypotheses — PASS. `D`, `l`, `E`, `n`, `d`, `Xbar`, `Y`, and `p` are
  explicit. The `Over` and `IsOver` instances identify the schemes and morphism over
  `Spec D.k`; the two structure maps each carry `LocallyOfFiniteType` and
  `QuasiCompact`; `IsProper p` gives the proper finite-type morphism; and `hd` is the
  exact topological Krull dimension bound. `hl`, `hn`, and the finite quotient ring
  are present. The coefficient is `Padic.coefficientExtensionRing l E n`, i.e.
  `A = A_{E,n}`.
- Origin sheaf — PASS. `F` is a pro-étale module sheaf over the canonical finite
  coefficient ring, `G` is an étale module sheaf over the same quotient, and `hF`
  identifies the canonical realization of the comparison pullback of `G` with the
  realization of `F`. This is the source's étale-origin witness, with no
  constructibility or finiteness restriction on `G`.
- Absolute conclusion — PASS. For every integer `r` above `2*d`, the module takes
  `F` in degree zero, applies `finiteCoefficientDerivedDirectImage p`, and states
  `IsZero` of the `r`-th homology object. This is the cohomology-sheaf vanishing
  clause in the canonical finite-coefficient presentation.
- Relative conclusion — PASS. For every scheme map `v : V ⟶ Y`, the file uses the
  chosen fibre product and its projections, applies canonical finite-coefficient
  pullback along `pullback.fst p v`, then direct image along `pullback.snd p v`, and
  states the same bound. `V` has no finite-type, dimension, or étaleness hypothesis.
  The quantifier order is `v`, then the integer degree and bound.
- Edge cases — PASS. `d = 0`, `n = 1`, zero and empty sheaves/schemes, empty index
  phenomena (none are introduced), arbitrary positive-dimensional or non-finite-type
  `V`, and nonconstructible étale-origin sheaves remain covered. The bound uses the
  original `Xbar` only and therefore does not accidentally impose a dimension bound
  after base change. The characteristic condition is exactly `l ≠ D.p`.
- Existing-notion audit — PASS. The class predicate, site comparison, finite-level
  coefficient modules, realization, pullback, and derived direct image were read in
  their existing modules. No second site, coefficient ring, or arbitrary base-change
  map was defined. The upstream sorry candidate was rejected as an attachment because
  it is stronger and unproved.
- Repair — the first landed packet had no Lean statement module. I added the single
  module and item `lean` record, retaining its corrected node statement and proof
  split. I also supplied the canonical finite quotient topology instances needed by
  the existing finite-coefficient encoding. Compilation via `scompile.py` is clean
  except for the permitted declaration-uses-`sorry` warning.

## Maintainer review fix

The delivered statement was right in substance but used the continuous-function
`FiniteCoefficientModules` encoding (node def-weil-pbc-proetale-modules, not cited)
with `E : Type (u + 1)` and module-local topology instances, instead of the recorded
declarations of the cited nodes (H4). The fix states the same two clauses with
`proEtaleConstantDerivedDirectImage` (def-weil-derived-direct-image),
`proEtaleConstantModulePullback` (def-weil-proetale-inverse-image) and modules over
`proEtaleConstantRing` (def-weil-pbc-proetale-site), with `E : Type u`, exactly the
clauses of `sfFullCohomologicalDimension` (def-weil-full-cohomological-dimension).
The étale-origin witness is `F ≅` the canonical realization
`sfIntrinsicModuleEquivalence` of `comparisonUpperStar` (def-weil-pbc-site-comparison-morphism)
of an étale `ModuleCat (ULift A)`-sheaf `G`. Hypotheses, quantifiers and the bound
`2 * d` are unchanged; the file compiles cleanly through `nt_compile.py`.
