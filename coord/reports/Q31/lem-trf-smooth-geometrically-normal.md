## Worker report

Repair of returned head `60e49af8e77c`, addressing H13/H3, H11 and H8. The retained
module states `AlgebraicGeometry.smooth_geometrically_normal`, with `sorry` as its
only theorem proof. The node's mathematical statement and dependencies are unchanged.

Hypothesis/clause correspondence:

- The base field is `(k : Type u) [Field k]`.
- The scheme and named structure morphism are `(X : Scheme.{u})` and
  `(f : X ⟶ Spec (.of k))`; `[Smooth f]` supplies exactly smoothness.
- Every finite purely inseparable extension is quantified by `(K' : Type u)
  `[Field K'] [Algebra k K'] [Module.Finite k K'] [IsPurelyInseparable k K']`.
  `Module.Finite` means finite dimension over the field. The algebra structure
  supplies the specified field embedding `algebraMap k K'`.
- Its scheme-theoretic base change is `Limits.pullback f
  (Spec.map (CommRingCat.ofHom (algebraMap k K')))` in `Scheme.{u}`. The contravariant
  `Spec.map` has precisely the required direction `Spec K' ⟶ Spec k`.
- Regularity of this base change is `IsRegularScheme`. The **current recorded**
  dependency defines this as `IsLocallyNoetherian X ∧ IsRegular X`. The first
  conjunct requires Noetherian affine section rings; the second requires every
  stalk to be a regular local ring. These are both parts of the node's equivalent
  formulation in Stacks Tag 02IT, not just its stalkwise part.
- The second outer conjunct quantifies over every `(K : Type u) [Field K]
  [Algebra k K]`, with no finiteness, inseparability or perfection assumption.
- For every point `x` of that base change, `IsDomain (Y.presheaf.stalk x) ∧
  IsIntegrallyClosed (Y.presheaf.stalk x)` says exactly that the local ring is a
  normal domain. `IsIntegrallyClosed` uses its fraction ring, which is a fraction
  field under `IsDomain`.
- The final `IsReduced Y` conjunct says the same base change is reduced. Mathlib
  gives the sectionwise definition, equivalent to the node's stalkwise condition
  by `isReduced_of_isReduced_stalk` and `isReduced_stalk_of_isReduced`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme-base-change convention is `Limits.pullback f T.hom`; the node explicitly
  distinguishes this from `Scheme.Modules.moduleBaseChange`, which concerns modules.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
  Its body uses `IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`
  and `IsRegular` from `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed` and
  the normal-domain inline convention `IsDomain R ∧ IsIntegrallyClosed R`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.

The module now imports the stated proof-dependency modules, including
`Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion` and
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`. Their actual signatures and
proof docstrings were read. The latter's first clause uses regular affine
neighbourhoods; Stacks 02IT converts the recorded regularity predicate to that
form. The six-step proof docstring includes local Noetherianity before this use.
The finite-type-over-Noetherian proof node has no recorded Lean module, so none
is invented or imported for it.

Edge cases checked against the node and Stacks 056T/056S/02IT: the empty scheme
requires no points and is locally Noetherian; the identity extensions `K=k` and
`K'=k` are included; characteristic zero and positive characteristic are both
allowed; no perfectness, fixed relative dimension, nonemptiness or global
quasi-compactness is assumed. Affine finite-type neighbourhoods establish local
Noetherianity even for a non-quasi-compact smooth scheme. Universe `u` is arbitrary
and all scheme and extension data use the standard common `Scheme.{u}` universe;
there is no lower, independent test-field universe making the quantifier vacuous.

Retained search evidence: `msearch.py` LeanFinder query "smooth scheme over field
geometrically normal regular reduced" found generic smoothness predicates but no
exact theorem; Loogle query "IsRegular, IsReduced, IsIntegrallyClosed,
IsPurelyInseparable" returned no hits (saved in `searches.jsonl`). Repair search:
`msearch.py ... grep 'smooth_geometrically_normal|IsRegularScheme'
AlgebraicGeometry` returned zero Mathlib hits. Direct `rg` in the named upstream
and side-library geometry directories found the current landed
`Sheaf.AlgebraicGeometry.IsRegularScheme` and no exact theorem; searching the
upstream source for this item's id found none. The canonical dependency is
therefore reused, with no second definition. The current source of
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions` was read using
`scompile.py --source` because it is absent from the older local source checkout.

No statement correction, new node, or disputed statement is needed.

## Second reading by Q31

This repair worker reread the retained packet independently of its original
worker, opening both node JSON statements, both retained Lean files, the current
recorded regular-scheme source and Stacks `properties.tex`/`varieties.tex`.

H13/H3: the retained alias had body `IsRegular X`. Its upstream class has only
`isRegularLocalRing_stalk`; local Noetherianity is not a field. Thus the retained
report's claimed equivalence with the full regular-scheme definition was wrong.
The shared branch has since landed the exact predicate in
`Sheaf.AlgebraicGeometry.IsRegularScheme`, with body
`IsLocallyNoetherian X ∧ IsRegular X`. I removed the retained alias module and its
stale dependency-node override and changed the theorem's import to that current
recorded module. The regularity clause now demands both conditions, while the
other clauses retain their original signatures.

For the item, I matched the field and smooth morphism to its first sentence;
matched the finite, purely inseparable extension and actual fibre product to its
first conclusion; unfolded the imported `IsRegularScheme` to check both regularity
conditions; matched the unrestricted field-extension quantifier and every stalk
to its normal-domain conclusion; and checked that `IsReduced` applies to the
same pullback, outside the stalk quantifier. No extra assumptions or clauses were
found. In particular, local Noetherianity is a conclusion inside regularity,
not an added hypothesis, and arbitrary extensions remain unrestricted.

H8: the obsolete dependency module used the malformed text
`blueprint: def-weil-regular-scheme.` without parentheses. Removing that redundant
module removes the defect; the imported landed module has the exact marker
`(blueprint: def-weil-regular-scheme)`. Both module and theorem docstrings in the
item have `(blueprint: lem-trf-smooth-geometrically-normal)`. The theorem docstring
now follows all six DAG proof steps and names their dependency nodes.

This comparison supersedes the retained report's incorrect assertion that
regular stalks alone suffice. The item node was refreshed from the shared branch
while preserving only its Lean record; the delivery wrapper rebases onto current
`newtargets-dag`. Per-file compilation and delivery preflight are recorded below.

Validation: `scompile.py Q31 lem-trf-smooth-geometrically-normal
lean/Sheaf/TraceFormula/SmoothGeometricallyNormal.lean` exited 0, with no Lean
errors or warnings; the wrapper checked both sandbox and library presentations.
The static self-check confirmed one theorem/one `sorry`, no lines over 100
characters, verbatim `lean.statement`, and only `lean` changed in the item node.
The initial saved-packet dry run raced with removal of the obsolete dependency
file at packaging and is superseded by the finalized-packet dry run.
