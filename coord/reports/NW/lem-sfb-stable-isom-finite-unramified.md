## Worker report

The module `Sheaf.AlgebraicGeometry.StableIsomFiniteUnramified` states
`AlgebraicGeometry.StablePointedModuli.finite_type_finite_unramified_isom`.
Its only theorem proof is `sorry`. The helper `fiberCurve` is a real construction:
it composes the original curve projection with the equality identifying its
base with the specified functor-fibre base. It never chooses a curve from a
coarse point or quotients by automorphisms.

The live node was stage-1 reviewed by L/Q66, but had no `lean` field or
`reviewed_lean`. The previous worker's stale-stage-1 refusal does not prevent
this requested stage-2 statement. No splitting or source statement was changed.

Hypotheses and clauses, matched individually:

* A field k: `(k : Type u) [Field k]`, using Mathlib's field.
* An integer genus g at least two: `(g : ℕ) (hg : 2 ≤ g)`. Genus is
  nonnegative by definition; this retains every genus in the source.
* The specific stable unpointed moduli groupoid: throughout the atlas clause,
  `BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0)`.
  This is the recorded category of actual families with their automorphisms.
* Finite type over k: existence of `U : Over (Spec (.of k))` and a scheme
  atlas `a`, with `LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom`.
  Every scheme base change has the specified algebraic-space presentation
  `HasSpaceBaseChange a T t Z p`, and its projection satisfies
  `SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p`. This is a
  finite-type etale atlas, not a finite-type coarse scheme. For this already
  known DM stack it is equivalent to local finite type and quasi-compactness:
  such an atlas implies both; conversely, choose finitely many affine opens
  in an etale atlas covering the quasi-compact stack, each locally of finite
  type over k. Their finite disjoint union is of finite type over k.
  Etale is smooth of relative dimension zero, so it is also a smooth atlas.
* Every k-scheme T and two stable families over it: unrestricted
  `(T : Over (Spec (.of k))) (C D : StablePointedModuli.Fiber ... g 0 T)`.
  `Fiber` is the recorded core of Mathlib's functor fibre. The `0` is exactly
  zero labelled sections. The helper only removes the base equality transport.
* Represented by a T-scheme: `∃ I : Over T.left`. The universal element is
  an actual isomorphism `e` in `Over I.left` between the two canonical
  `Over.pullback I.hom` curve base changes.
* Finite: `IsFinite I.hom`.
* Unramified in the node's precise sense: `IsUnramified I.hom`, the recorded
  conjunction of `LocallyOfFiniteType I.hom` and
  `IsOpenImmersion (pullback.diagonal I.hom)`, not etaleness or smoothness.
* The full Isom functor on every T-scheme T': `∀ (V : Over T.left) (eV : ... ≅ ...)`.
  For every test isomorphism there is `∃! b : V ⟶ I` such that its composite
  with the projection to the original D equals `parameterMap C b`, then the
  universal isomorphism, then the same projection. Together with equality of
  the structure maps, this is exactly `eV = b^*e` by the fibre-product universal
  property. Pulling back the universal element supplies existence in the
  opposite direction for every b. Thus it specifies the canonical representing
  bijections, and their naturality follows from composition of parameter maps.
  It does not assert merely an arbitrary pointwise bijection.
* Finite diagonal with the 2-fibre convention: a scheme base change by a pair
  of objects of this groupoid is precisely this Isom functor, regarded as a
  discrete groupoid, since an arrow compatible with the fixed pair is unique.
  Accordingly the universal Isom assertion is the finite unramified diagonal
  assertion, with the same groupoid and its canonical pullbacks.
* Inertia finite and its fibre Aut: specialize the unrestricted pair to `D = C`.
  The very same universal property then represents all automorphisms. No
  triviality, constant group scheme, order prime to the characteristic, or
  reducedness hypothesis is inserted.

Dependency declarations used:

* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.StablePointedModuli`, its `forget`, `Fiber`, and recorded
  `CategoryTheory.discreteModuli`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`. The fibre and total-category signatures/docstrings
  and the stack/2-fibre definitions were read in full.
* `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified` (exact conjunction stated above).
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms; `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.Algebra.Field.Defs`: `Field`. Their class/structure signatures
  and defining fields were read, rather than replaced by private predicates.
* `Sheaf.AlgebraicGeometry.UnorderedPointedIsom`:
  `AlgebraicGeometry.MultipointedPair.parameterMap`, exactly the canonical
  fibre-product map for a parameter morphism. Its already landed owning node
  `def-sfb-unordered-pointed-isom` is added to `stmt_deps`; its statement,
  declaration and universal-property docstring were read.
* Mathlib `Over.pullback` and the scheme pullback projections implement actual
  base changes. Mathlib `Core` and `Functor.Fiber` implement the recorded fibre.

Plain proof imports include the recorded stable pointed Isom theorem, the
unpointed coarse-projective theorem (only its smooth/DM clause is needed),
unramified base change, scheme finiteness/properness, Noetherianity, finite type,
closed immersions and scheme/morphism gluing. The proof-only ten-canonical
Hilbert-parameter node currently has no usable Lean record, so no module for
that future proof input is imported; the theorem's statement needs none of its
data. No statement dependency is missing. The eight-step proof plan is carried
in the theorem docstring, including the arbitrary-base and local-diagonal
arguments rather than assuming the test base is finite type.

Edge cases checked before writing: empty base T and empty test V; arbitrary
nonreduced, non-Noetherian and disconnected bases; no finiteness hypothesis on
T/k; `g = 2`; all field characteristics including those dividing an automorphism
group's order; C equal to D; nonisomorphic C,D with empty Isom scheme. Empty
schemes are permitted for I and atlas charts. All schemes and test schemes use
the recorded universe u, with no independent smaller test universe. The fibre
base equality is transported, not assumed definitionally equal.

Searches:

* `msearch.py ... leansearch "finite type Deligne Mumford stack finite
  unramified diagonal stable curves"`: eight scheme/ring unramified hits,
  notably `FormallyUnramified.isOpenImmersion_diagonal`, but no moduli theorem.
* `msearch.py ... leanfinder "The stack of stable genus at least two curves
  has finite unramified diagonal and is of finite type"`: eight scheme
  unramified/diagonal hits, no stable-moduli statement.
* `msearch.py ... loogle "AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.LocallyOfFiniteType"`: six scheme-finiteness results;
  these supply existing notions, not the present theorem.
* `msearch.py ... grep "moduli|[Ss]table[Cc]urve|[Ii]s[Ff]inite[Tt]ype.*[Ss]tack"
  AlgebraicGeometry`: one bibliographical elliptic-curve moduli hit.
* `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `Moduli.*FiniteType`, `IsModuli.*Finite`, `HasFinite.*Diagonal`,
  `isomFunctor`, `isomPresheaf`, and stable/unramified combinations: the
  pointed-Isom theorem exists, but requires a finite-type base and also
  contains an unrelated generic-extension conclusion; it does not match this
  arbitrary-base stack statement. No exact theorem exists upstream.
* `rg` for `fiberCurve|finite_type_finite_unramified_isom` in both libraries
  and `dag/lean_names_upstream.json`: no declaration-name collision.

Read the source in `literature/stacks-project/moduli-curves.tex` at
`lemma-stable-curves-deligne-mumford`, `lemma-stable-separated`,
`lemma-stable-quasi-compact`, and `theorem-stable-smooth-proper`; also
`stacks-morphisms.tex` at `definition-locally-finite-type`.
No statement fault or disputed statement was found. No new independent notion
or dependency repair is introduced; the one helper is the canonical
curve-forgetful construction belonging to this node's Isom statement.

## Second reading by NW

A separate agent was explicitly prohibited by the dispatch brief. This section
records a second pass by this worker, not a claimed independent agent review;
the maintainer's independent review is still required.

I reread the full node and module. The first conjunct is a finite-type atlas of
the stable groupoid itself, not of its coarse scheme. Both curves lie over the
same arbitrary T through the recorded fibre; `fiberCurve` correctly transports
each projection to that T. The isomorphisms are in Over of the parameter base,
not absolute scheme isomorphisms. The universal-property equation uses the
canonical map on C and projection to D, so it neither reverses isomorphisms nor
forgets their base compatibility. The unrestricted tests and unique parameter
map make this representability of the whole functor. The same-family case
retains all automorphisms and is exactly the inertia clause. Unramified is the
recorded open-diagonal conjunction. There are no added normality, finite-type
base, characteristic, or frame-preservation hypotheses. No mismatch was found
on this second pass.

## Validation

Compilation and prescribed delivery preflight results are recorded below.

`scompile.py NW lem-sfb-stable-isom-finite-unramified` compiled the delivered
file cleanly in sandbox mode (17.3 s) and library mode (12.5 s), with no
errors or warnings. `deliver2.py ... --no-push` printed
`OK (dry run): commit 35e19ea0a5f passes the preflight and compiles; nothing pushed`.
The final delivery wrapper repeats the prescribed checks with this report.
