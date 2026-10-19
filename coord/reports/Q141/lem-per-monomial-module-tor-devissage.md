## Worker report

This is the stage-2 statement of `lem-per-monomial-module-tor-devissage`, in
`Sheaf.RingTheory.MonomialModuleTorDevissage`, declaration
`AddMonoidAlgebra.monomialModule_tor_vanishes`. Its sole proof is `sorry`.
The separate definition module `Sheaf.RingTheory.MonomialSubsetSpan` has real data
and no postponed proofs. The Q84 stage-1 split, its eight proof steps, and its
passing maintainer review are preserved. The previous stale-assignment objection
concerned splitting an already split node; this delivery adds its missing Lean
statement and does not repeat stage 1.

Hypothesis and conclusion correspondence:

- The commutative additive monoid is `{Q : Type u} [AddCommMonoid Q]`.
  The abelian group is `{G : Type v} [AddCommGroup G]`.
- The homomorphism is `(h : Q →+ G)` and its required injectivity is
  `(_hh : Function.Injective h)`. No finite generation, sharpness, or
  torsion-freeness hypothesis is imposed.
- The ring D is Mathlib's `AddMonoidAlgebra ℤ Q`, with basis `single q 1` and
  its convolution multiplication, so `z^q z^q' = z^(q+q')`.
- The arbitrary D-module is `(M : Type w) [AddCommGroup M]
  [Module (AddMonoidAlgebra ℤ Q) M]`; it is not assumed flat or projective.
- A monoid ideal is any `(I : Set Q)` with
  `∀ q ∈ I, ∀ q' : Q, q + q' ∈ I`. This allows the empty ideal.
  Its monomial ideal is `Ideal.span ((fun q : Q ↦ single q (1 : ℤ)) '' I)`.
  Stability makes this ring ideal equal to the integer span Z[I]: multiplying
  a basis vector in I by any basis monomial stays in I. Conversely every
  integer multiple of a generator belongs to the ring ideal.
- `_hM` asserts `IsZero` of degree-one `CategoryTheory.Tor'` of M with
  D modulo that ideal, for every I satisfying this stability condition.
- The pair of subsets is `(U T : Set G)`, with `_hUT : U ⊆ T`.
  `_hT` and `_hU` are exactly `∀ t ∈ T, ∀ q, t + h q ∈ T` and its U version.
- `monomialAmbient h` is Z[G] restricted along `mapDomainRingHom ℤ h`.
  A basis monomial therefore acts as `z^q [t] = [h q + t] = [t + h q]`.
  `monomialSubsetSpan h T` is the D-span of its basis vectors indexed by T.
  For stable T, expanding a scalar as a finite sum of monomials shows every
  resulting exponent is still in T. Hence this is exactly the integer span
  of T. Conversely integer multiples come from constant scalars. The group
  algebra's basis is independent, so the span is the required free abelian
  group Z[T], with precisely the node's action, not a free D-module on T.
- The quotient V is the module quotient of `monomialSubsetSpan h T` by
  `(monomialSubsetSpan h U).comap (monomialSubsetSpan h T).subtype`.
  Monotonicity of span and U ⊆ T identify the denominator with the included
  copy of Z[U]. This construction uses an actual inclusion and quotient;
  no arbitrary map, chosen object, or additional exactness assumption appears.
- `(i : ℕ) (_hi : 0 < i)` and the final `IsZero` state precisely vanishing
  of all positive-degree Tor with V. Degree zero is not asserted to vanish.

Universe transport: Q, G, and M have independent universes u, v, w. Put
k = max u v w. Mathlib's monoidal module category uses a coefficient ring
and module carriers in the same universe. The theorem therefore computes in
`ModuleCat.{k} (ULift.{k} D)` with the canonical `ULift.{k}` copies of M,
D/Z[I], and V. The standard `ULift` scalar instances are
`up d • up m = up (d • m)`. Thus `ULift.ringEquiv` and
`ULift.moduleEquiv` canonically identify this with the original D-module
problem. Transporting a projective resolution and its tensor complex along
these equivalences preserves its homology and zero objects. This is only
size transport; there is no equality imposed between u, v, w, no exclusion
of larger modules or groups, and no mathematical change to the node.

Dependency declarations used:

- `def-weil-pbc-tor-modules`: `Mathlib.CategoryTheory.Monoidal.Tor`,
  `CategoryTheory.Tor'`. Its definition and docstring were opened: it derives
  the first variable, exactly as the node requires. The ModuleCat monoidal,
  abelian, and projective-resolution instances are imported publicly.
- New `def-per-monomial-subset-span`:
  `Sheaf.RingTheory.MonomialSubsetSpan`,
  `AddMonoidAlgebra.monomialAmbient` and
  `AddMonoidAlgebra.monomialSubsetSpan`.
- Mathlib constructions are used directly: `AddMonoidAlgebra.mapDomainRingHom`,
  `ModuleCat.restrictScalars`, `Submodule.span`, `Submodule.comap`,
  `Submodule.subtype`, the module quotient, and `Ideal.span`.
- The stated proof dependencies are imported privately:
  `Mathlib.RingTheory.Flat.Basic` (projective implies flat and flat tensor
  exactness), `Mathlib.Algebra.Homology.HomologySequence` (the full exact
  homology sequence), `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`
  (tensor preserves colimits), and `Mathlib.Algebra.Category.Grp.AB`
  (exactness of filtered abelian-group colimits).
- The two recorded upstream proof dependencies are imported privately:
  `WeilConjectures.Algebra.TorDimensionShiftNatural`,
  `CategoryTheory.tor_dimension_shift_natural`, and
  `WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry`,
  `CategoryTheory.nonempty_tor'_flip_iso`. Their current source signatures
  and docstrings were read through `scompile.py --source`, since the older
  source checkout lacks these two published files.

The theorem docstring carries all eight proof steps: the resolution complex;
extension closure from the full long exact sequence; filtered-colimit closure;
the finite monomial filtration and its kernel computation; passage to all V;
Tor_2 ideal tests using symmetry and a free presentation; propagation of tests
to explicit successive free syzygies; and the final dimension shift.
The source passages in `literature/stacks-project/algebra.tex` for Tags 00LY,
00M0, and 0BNF were opened. The item itself correctly describes its additional
monomial algebra argument as agent-supplied, rather than attributing the whole
criterion to one of those Stacks lemmas.

Edge cases checked before and after writing:

- T empty forces U empty. The empty span is bottom and the numerator is zero.
- U empty gives denominator zero. No nonemptiness hypothesis is present.
- U = T makes the comap of the span under its subtype top, hence V = 0.
- I empty gives the zero ideal and test quotient D; I = Q contains the unit
  monomial and gives quotient zero. Both are quantified over.
- For the trivial monoid Q, D is Z and V is free abelian on T minus U;
  positive Tor vanishes for every M, as the statement predicts.
- For Q = N and M = Z[x]/(x-1), every monomial ideal test holds although M
  is not Z[x]-flat. No accidental ordinary flatness assumption was added.
- G may have torsion, and Q need not be sharp, finite, or finitely generated.
- All universe variables and term variables are explicitly bound. The
  definitions contain no `sorry`, local instance, private copy, or notation.

Searches for an existing theorem and the missing notion:

- `msearch.py ... leanfinder` with "Tor vanishing on monomial ideal quotients
  implies higher Tor vanishing on invariant subsets of an abelian group":
  eight hits, including projective Tor vanishing and unrelated torsion
  predicates; none states the theorem for an arbitrary tested module M.
- `msearch.py ... loogle 'AddMonoidAlgebra, Tor'`: no hits; Tor was not
  recognized as a bare identifier. No claimed match is based on this search.
- `msearch.py ... grep 'monomial.*Tor|Tor.*monomial|monomialModule'`:
  nineteen unrelated monomial/tactic/polynomial hits, no such theorem.
- LeanSearch query "Free abelian module on a monoid stable subset of an
  abelian group with translation action over the monoid algebra": eight
  hits, including `FreeAbelianGroup`, `AddMonoidAlgebra.instFree`, and free
  representations. None supplies this D-module on a stable subset of G.
- LeanFinder query "Submodule spanned by single monomials after restricting
  scalars along a monoid homomorphism and its quotient for nested subsets":
  eight hits for general span/restrictScalars results and polynomial
  coefficients; their signatures do not define this monomial subset module.
- `msearch.py ... grep 'monomialSubsetSpan|monomialAmbient|stable.{0,40}subset'
  Algebra/MonoidAlgebra`: no hits. Mathlib's underlying span and scalar
  restriction definitions are reused, rather than reimplemented.
- `rg` in the source project's WeilConjectures and side library lean/Sheaf
  found no `monomialSubsetSpan`, `monomialAmbient`, or theorem declaration.
  The existing `LogRegularChartMonomialTor` mentions this lemma only in its
  proof docstring and has no construction of Z[T]. Its full statement was read.
- DAG text searches found this statement and unrelated invariant-group-set
  arguments, not an existing module definition. `blueprint_refs.py search`
  gives zero nodes for "monomial module" and "stable subset"; `ancestor`
  identifies `lem-per-artin-gabber-affine-curve` as required.
- Names were also searched in `dag/lean_names_upstream.json`, with no match.
  Raw service results for the new definition searches are retained verbatim
  in its `mathlib_searches`.

No statement dispute or correction is needed. The item's original statement,
source, proof, proof dependencies, status, and stage-1 review are unchanged;
only its Lean record and the new definition dependency are added.

## New nodes

`def-per-monomial-subset-span` introduces the canonical monomial ambient module
and subset span in `Sheaf.RingTheory.MonomialSubsetSpan`. Its source is the
basis construction in Step 4 of this item, for the algebra used in ILO Exposé X
1.3(vii) and Lemma 1.5. It takes the D-span inside the group algebra after the
specified scalar restriction. Searches of Mathlib, the source repository,
side library, DAG, and blueprint found only general span/scalar-restriction
primitives, not this monomial subset module. These primitives are reused.
The item's `stmt_deps` now cites this node. All its data is constructed, with
no theorem assumption or choice of an unspecified object.

Validation: both delivered modules compile cleanly through `scompile.py`,
including their canonical library module names. The `deliver2.py --no-push`
dry run reports OK: the packet passes server stage-2 preflight and compilation.
The initial preflight's sole metadata finding was repaired by recording the
signature starting at `def`, excluding its `noncomputable` modifier, exactly
as the preflight's declaration reader requires.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
