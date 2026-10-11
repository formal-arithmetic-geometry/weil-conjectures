## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralDimOneAmple` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one`.
It binds a scheme `Y : Scheme`, with `[IsIntegral Y]` for integrality,
`[IsLocallyNoetherian Y]` and `[CompactSpace Y]` for the Noetherian
(quasi-compact locally Noetherian) hypothesis, and `[IsSeparated (terminal.from Y)]`
for separatedness over `Spec ℤ`. The dimension clause is
`hY : topologicalKrullDim Y = (1 : WithBot ℕ∞)`. Its conclusion
`∃ L : Y.Modules, ∃ hL : L.IsInvertible, @IsAmple Y L hL` says that an
invertible module exists and is ample. The proof is `sorry`, as required;
its docstring records the three proof steps and their DAG dependencies
`lem-sc-affine-complement-finite-on-integral-curve`,
`lem-sc-find-globally-generated`, and `lem-sc-enough-globally-generated-ample`.

Dependency declarations used are `AlgebraicGeometry.IsIntegral` from
`Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsLocallyNoetherian`
and its characterization from `Mathlib.AlgebraicGeometry.Noetherian`,
`CompactSpace` from `Mathlib.Topology.Defs.Filter`,
`AlgebraicGeometry.IsSeparated`/`terminal.from` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`topologicalKrullDim` from `Mathlib.Topology.KrullDimension`,
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and
`AlgebraicGeometry.Scheme.Modules.IsAmple` from
`Sheaf.AlgebraicGeometry.Ample`.

Edge cases checked: the dimension type is `WithBot ℕ∞`, so equality to one
excludes the empty scheme; `IsIntegral` supplies nonemptiness; compactness is
explicit; and the existential conclusion binds the invertibility instance
explicitly so `IsAmple` is well-typed.

Searches made: `rg` over `lean/Sheaf` and `WeilConjectures` found no existing
statement of the integral dimension-one ample result; Mathlib search/grep for
integral Noetherian separated curves and ample modules found only the generic
`IsIntegral`, `IsLocallyNoetherian`, `IsSeparated`, and Krull-dimension APIs,
with no matching theorem. The existing `Sheaf.AlgebraicGeometry.Ample` module
was used for the ample predicate.

## Second reading by H1

I read the node and every statement dependency, then the declarations behind their
records. Source checked: Stacks Varieties Lemma 09ND, label
`varieties-lemma-dim-1-noetherian-integral-separated-has-ample`, in the local
Stacks source `/home/ubuntu/c1-stacks-review/varieties.tex:7927`; the tags table
confirms 09ND. The repository does not contain the untracked Stacks checkout.
The surrounding section “One dimensional Noetherian schemes” imposes no field,
finite-type, properness, smoothness, or characteristic assumption on this lemma.
I also read 09NB and 09NC and their proofs (lines 7856 and 7894).

Node-to-Lean checklist:

- Object: an arbitrary scheme Y — `(Y : Scheme.{u})`. Verdict: exact.
  Mathlib's `Scheme` is a locally ringed space locally isomorphic to spectra,
  matching `def-pc-scheme`; no base scheme is supplied or required.
- Integrality — `[IsIntegral Y]`. Verdict: exact. The recorded declaration
  in `Mathlib.AlgebraicGeometry.Properties` requires nonemptiness and domain
  sections on every nonempty open; this agrees with the dependency's affine
  formulation and its reduced/irreducible equivalence.
- Noetherian — `[IsLocallyNoetherian Y] [CompactSpace Y]`. Verdict: exact.
  I read `IsLocallyNoetherian.component_noetherian` and the affine-cover
  equivalence in `Mathlib.AlgebraicGeometry.Noetherian`. Its `IsNoetherian`
  class at line 280 extends precisely these two classes. `CompactSpace`
  has no Hausdorff axiom, and renders the quasi-compact dependency.
- Separated — `[IsSeparated (terminal.from Y)]`. Verdict: exact absolute
  separatedness. I read the morphism class (closed immersion of the diagonal)
  and `Scheme.IsSeparated` (separated over the terminal scheme) in Mathlib's
  `Morphisms.Separated`; the latter packages precisely this hypothesis.
  The proper-morphism dependency records `IsSeparated` as well as `IsProper`;
  only the former is used here. No properness or finite-type hypothesis is added.
- Dimension exactly one —
  `(hY : topologicalKrullDim Y = (1 : WithBot ℕ∞))`. Verdict: exact.
  The recorded definition is `Order.krullDim (IrreducibleCloseds Y)`, the
  supremum of strict-chain lengths of nonempty irreducible closed subsets.
- Conclusion object — `∃ L : Y.Modules`. Verdict: exact O_Y-module.
  Mathlib `Scheme.Modules` is `SheafOfModules Y.ringCatSheaf`.
- Conclusion invertibility — `∃ hL : L.IsInvertible`. Verdict: exact.
  I read the recorded upstream `Scheme.Modules.IsInvertible.exists_isoUnit`:
  each point has an open neighbourhood on which the module is the structure
  sheaf. For open immersions its pullback is restriction, giving locally free
  rank one; such modules are quasi-coherent. No alternate predicate is introduced.
- Conclusion ampleness — `@IsAmple Y L hL`. Verdict: exact absolute ampleness,
  using the recorded `Sheaf.AlgebraicGeometry.Ample` declaration. I read its
  body: compactness and, at every point, a positive tensor-power section with
  affine nonvanishing open containing that point; nonvanishing is membership
  outside the maximal ideal times the stalk module. The same L and its
  invertibility witness feed this predicate, in the required quantifier order.

Edge cases: the empty scheme is excluded by integrality and dimension one,
just as in 09ND. Dimension zero and Spec of a field are excluded by the equality,
not inadvertently by a field assumption. The zero module on a nonempty scheme
is not locally the structure sheaf, so is not a spurious existential witness.
No index set is quantified in the statement; the finite affine cover in the
proof is nonempty because Y is integral. Empty complements (affine Y itself)
are allowed. Within ampleness n = 0 is excluded by `0 < n`, exactly as 01PS;
tensor power zero remains the structure sheaf in the upstream definition.
No characteristic is restricted. `u` is arbitrary; invertible sheaves locally
of rank one are represented in `Y.Modules` at the scheme's universe, so this
adds no size restriction on the geometric objects. All variables and the
universe are explicitly bound.

Independent searches (different wording from the worker):

- LeanFinder via `msearch.py`: “A separated one-dimensional integral noetherian
  scheme admits an ample line bundle”. Eight hits, including
  `isIntegral_of_isAffine_of_isDomain`, `IsLocallyNoetherian`, and
  `isNoetherian_iff_of_finite_iSup_eq_top`; no exact theorem.
- LeanSearch via `msearch.py`: “Integral separated Noetherian scheme of Krull
  dimension one has an ample invertible module”. HTTP Internal Server Error;
  recorded as unavailable, with no mathematical verdict inferred.
- Loogle via `msearch.py`, query `"IsAmple"`: zero hits.
- `rg` over Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  `lean/Sheaf/AlgebraicGeometry`, using “ample”, “projective.*curve”,
  “curve.*projective”, “dim.one.*ample”, declaration-name patterns, and finally
  “09ND”, “dim.one.noetherian.integral.separated”, and the proposed full name.
  No exact declaration. I opened upstream `Modules/Ample.lean`: its
  `AlgebraicGeometry.IsAmple` requires a morphism to Spec of a field and a
  positive very ample power with a closed immersion, so it is not this absolute
  predicate. I also opened the project's `exists_isAmple_of_dim_le_one`, whose
  field and finite-type hypotheses prevent using it as this node's statement.
  The recorded absolute ample predicate is used, with no private copy.

No new nodes, dependency modules, or statement correction are needed.
No hypothesis or conclusion mismatch was found. The sole substantive repair
is to the proof docstring: step 2 now explicitly retains global generation
from 09NB and explains why complement points have Noetherian local rings of
dimension one (non-generic points of an integral one-dimensional scheme).
The three proof steps and dependency ids otherwise remain in place. The node's
`lean.statement` is now the literal multiline signature from the file; its
mathematical content is unchanged. All imports serve the recorded notions;
lines are within 100 characters. The sole theorem remains `:= by sorry`;
there are no definitions, auxiliary proofs, or hollow data in this delivery.

Validation: the original and edited files both compiled cleanly on the server
with the prescribed `scompile.py` single-file command (exit 0, 1.7 s each),
with no warnings. The node signature matches the file verbatim.
