## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift` states
`AlgebraicGeometry.Scheme.exists_boundedAbove_finiteFree_lift`, with its sole proof `sorry`.
There are no new definitions, new nodes, dependency replacements, or statement corrections.

Source read: Stacks Tag 08EE, lemma-lift-pseudo-coherent, in
`/home/ubuntu/c1-stacks-review/perfect.tex`, lines 3103–3200. The repository's named
`literature/stacks-project/perfect.tex` is absent on this machine. The available Stacks
checkout states the same affine-scheme, quasi-compact-open lifting assertion verbatim.
The docstring records all five DAG proof steps, including the descending induction
invariant, cone finiteness, clearing denominators, and termwise association of sheaves.

Hypotheses and conclusions, clause by clause:

- Scheme X: `(X : Scheme.{u})`, using Mathlib's category of locally ringed spaces
  locally isomorphic to spectra; no choice of coordinate ring is imposed.
- Affineness: `[IsAffine X]`, the canonical map to Spec of global sections being an
  isomorphism. This is the usual affine-scheme condition.
- Open subscheme: `(U : X.Opens)`, with the associated scheme `U.toScheme`.
- Quasi-compactness: `(hU : IsCompact (U : Set X))`; Mathlib compactness here does
  not assume Hausdorffness and is exactly quasi-compactness of the open subspace.
- Every object of D(O_U): `(E : schemeDerivedCategory U.toScheme)`. The explicitly
  bound `HasDerivedCategory.{w}` instances on X, U, and the localized open sites of U
  supply the category constructions used by the recorded definitions; they impose no
  finiteness, coherence, separation, or boundedness condition on E.
- Pseudo-coherence: `(hE : IsPseudoCoherent U.toScheme E)`, exactly the dependency's
  pointwise local bounded-above finite-free characterization, with its existing instances.
- A complex on X exists: `∃ P : CochainComplex (SheafOfModules.{u}
  (moduleRings X.toRingedSpace)) ℤ`. These are sheaves of O_X-modules with integer grading.
- Bounded above: `∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)`. No lower bound is added.
- Finite free in every degree: `∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅
  SheafOfModules.free (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r)))`.
  `free` is Mathlib's coproduct of r copies of the structure module; r varies with i.
- Restriction is isomorphic to E in D(O_U): `Nonempty (...mapDerivedCategory.obj
  (DerivedCategory.Q.obj P) ≅ E)`. The functor inside is `overFunctor` followed by
  `Equivalence.functor (Modules.overEquiv U)` with both module category instances
  explicitly identified as `SheafOfModules`. It is canonical open restriction,
  transported from the localized site to the open subscheme. Mathlib's
  `Scheme.Modules.overFunctorEquiv` identifies it with scheme restriction.
  Since both functors are exact, its derived action on Q(P) represents the termwise
  restricted complex, rather than a different derived operation.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; full structure signatures
  and docstrings read in the pinned Mathlib. `Mathlib.AlgebraicGeometry.AffineScheme`
  supplies `AlgebraicGeometry.IsAffine`.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`; its complete signature and docstring read.
  This uses the shared SheafOfModules carrier and Mathlib's abelian instance.
- `def-pur-pseudo-coherent-complex`: `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`,
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`; full definition and docstring read.
  Its finite-free and bounded-above formulas are reused literally as clauses, with no
  second predicate definition. This import also supplies Mathlib's `SheafOfModules.free`.
- Existing bridge read: `Mathlib.AlgebraicGeometry.Modules.Sheaf`,
  `Scheme.Modules.overEquiv` and `overFunctorEquiv` (through the dependency imports).
  The statement follows the already landed `QcOpenDerivedLift` restriction encoding.

Edge cases checked against the source before writing:

- U empty and X empty remain allowed. P can be the zero complex, r = 0; on the empty
  scheme every module and derived object is zero. No Nonempty or nonzero-ring assumption.
- U = X remains allowed and gives a global finite-free representative on an affine scheme.
- E = 0 remains allowed with the zero complex, in all degrees and with any upper bound.
- Negative upper bounds and unbounded-below representatives remain allowed because
  both degrees and N range over ℤ; no uniform rank bound or finite amplitude is imposed.
- There is no characteristic, reducedness, Noetherian, or separated-open hypothesis.
  Arbitrary u and w are explicitly bound; ULift only places the finite basis in the
  sheaf's section universe, without restricting ranks or schemes.

Searches run (all on 2026-10-11):

- msearch leansearch, `pseudo coherent complex lifting quasi compact open affine scheme`:
  service unavailable, Internal Server Error; this was not treated as a negative result.
- msearch leanfinder, `bounded above finite free complex extends a pseudo-coherent object
  from a quasi-compact open of an affine scheme`: eight hits, affine-transition-limit
  and quasi-finite declarations; none state this lifting theorem.
- msearch loogle, `AlgebraicGeometry.Scheme.IsPseudoCoherent, SheafOfModules.overFunctor`:
  zero hits, unknown identifier `AlgebraicGeometry.Scheme.IsPseudoCoherent` (project-only
  name absent from the public Mathlib index).
- msearch grep, `pseudo.?coherent|PseudoCoherent|lift.*finite.*free`: zero Mathlib hits.
- rg of WeilConjectures for `pseudo.?coherent|PseudoCoherent|finiteFree|FiniteFree`:
  `Cohomology/DirectImage.lean` has a bounded finite-free complex predicate and proper
  higher-direct-image results, not this unbounded-below open lifting assertion.
- rg of WeilConjectures for the node id: no hits. rg of `dag/lean_names_upstream.json`
  for the node id: no hits.
- rg of `lean/Sheaf` for pseudo-coherence and finite-free terms: the existing scheme
  definition, ring definitions, and related ring cone/cohomology results; no identical
  lifting statement. `QcOpenDerivedLift` concerns only a quasi-coherent derived lift,
  with no bounded-above finite-free representative conclusion.
- The new full declaration name was searched alongside pseudo-coherence in the source:
  no collision. The only scheme pseudo-coherence definition found is the dependency used.

Validation: scompile.py compiled the module on the server in 3.4 seconds, exit code 0,
with no errors or warnings. `autoImplicit false` explicitly disables automatic binders.

## Second reading by G1

Independent source reading: `/home/ubuntu/c1-stacks-review/perfect.tex`,
lemma-lift-pseudo-coherent (Tag 08EE), lines 3103–3200, together with the
preceding lifting section and pseudo-coherence section. There is no standing
Noetherian, characteristic, or finiteness hypothesis on the scheme. The node
reproduces the source statement exactly; no statement correction is needed.

Object/hypothesis/conclusion checklist (each verdict: matches):

1. An arbitrary scheme X: `(X : Scheme.{u})`. Opened Mathlib's Scheme structure
   and Hom signature: locally affine locally ringed spaces and their morphisms.
2. X affine: `[IsAffine X]`. Opened its definition, `IsIso X.toSpecΓ`, which is
   equivalent to being isomorphic to Spec of a commutative ring.
3. An open subscheme U of X: `(U : X.Opens)` and `U.toScheme`; Mathlib's
   `Scheme.Opens` is `TopologicalSpace.Opens X`, with the canonical restricted scheme.
4. U quasi-compact: `(hU : IsCompact (U : Set X))`. Compactness means finite
   subcovers, without a Hausdorff assumption; it is precisely quasi-compactness here.
5. Every E in D(O_U): `(E : schemeDerivedCategory U.toScheme)`. Read
   `Sheaf.AlgebraicGeometry.DerivedCategory`: the carrier is exactly Mathlib's
   derived category of the shared `SheafOfModules` category, not a second Modules
   category instance. The HasDerivedCategory binders on X, U and opens of U
   are the shared localization infrastructure required by these definitions,
   not geometric assumptions or boundedness hypotheses on E.
6. E pseudo-coherent: `(hE : IsPseudoCoherent U.toScheme E)`. Read the entire
   recorded dependency definition in PseudoCoherentComplex: each point admits
   a neighbourhood with a bounded-above finite-free representative; this is the
   node's scheme-local characterization. Bounds and ranks are allowed to vary.
7. A complex on all of X exists: `∃ P : CochainComplex
   (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ`. The object P comes
   after E and hE, so it may depend on them, as in the source.
8. P bounded above: `∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)`.
   This bounds terms, not merely cohomology, and imposes no lower bound.
9. P has finite free terms: `∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅
   SheafOfModules.free (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r)))`.
   Opened Mathlib free: the coproduct of copies of the unit module. Thus this
   specifies globally free terms, with finite rank allowed to depend on degree.
10. Restriction represents E: the final `Nonempty (... ≅ E)` applies derived
    open restriction to `DerivedCategory.Q.obj P`. Opened Mathlib's
    `Modules.overEquiv` and `overFunctorEquiv`: overFunctor composed with that
    equivalence is canonical restriction to U. The explicit C and D parameters
    keep the shared SheafOfModules category structures. Restriction is exact,
    so mapping Q(P) is the class of the termwise restricted complex.

Edge cases: X and U may be empty; U may be X; E may be zero. Rank zero is
allowed by `r : ℕ` and `Fin 0`. Any integer upper bound is permitted, including
zero and negative bounds; no bounded-below condition, uniform rank bound or
finite amplitude was introduced. Empty principal-open covers are allowed in
the source proof (choose the zero complex for an empty U). Arbitrary
characteristics and non-Noetherian/nonreduced rings are included. Explicit u
and w are bound, with ULift only matching the basis universe to the section
universe; there are no unbound variables or independent test-object universes.

Independent searches (2026-10-11), using different terms from the first reader:

- msearch leanfinder: `extend finite rank free resolution from open subscheme
  to spectrum`: eight hits about free loci/localized modules and unrelated
  scheme properties; no derived lifting statement.
- msearch loogle: `IsAffine, CochainComplex`: the public index reports unknown
  identifier IsAffine, so it supplies no evidence of absence.
- msearch leansearch: `extension of a pseudocoherent derived object over an
  affine scheme from a quasicompact open`: Internal Server Error, recorded as
  unavailable, not as a negative mathematical result.
- msearch grep across Mathlib: `pseudo.?coherent|boundedAbove_finiteFree_lift|
  lift.*free.*complex`: no hits.
- Independent rg across all WeilConjectures for pseudo-coherence, finite-free
  complexes and 08EE. Opened AlgebraicGeometry/Cohomology/DirectImage.lean
  lines 512–519: IsFiniteFreeComplex requires support in [0,d], so it is not
  the unbounded-below notion here; its higher-direct-image assertions are not
  this lifting statement. Other hits concern free modules or perfect complexes.
  The worker report abbreviated this source path as Cohomology/DirectImage.lean;
  the actual path includes AlgebraicGeometry, verified independently.
- Independent rg across all lean/Sheaf: the scheme pseudo-coherence definition,
  ring pseudo-coherence definitions, cone/cohomology results, and the distinct
  quasi-coherent derived lift; none gives this finite-free open lifting result.
  No new definition is needed and no recorded dependency requires replacement.

H5–H9: there are no new definitions or hollow data, and the only proof is the
named theorem's sorry. Module and theorem docstrings have the source and exact
blueprint id. All five proof steps are present, including the localized
induction invariant, cone finiteness, clearing denominators, and sheafification.
Both imports are used. All lines are at most 100 characters, and the declaration
has the upstream namespace. The node's lean.statement matches the file signature
verbatim after whitespace layout normalization.

Mismatches and changes: no mathematical or Lean mismatch found; retained the
module and node as written. Added this independent reading and search evidence
only. No new nodes, dependency modules, or statement changes.

Validation: scompile.py with the sandbox file's absolute path compiled cleanly
on the server in 3.4 seconds, exit code 0, no warnings or errors. An initial
relative-path invocation was resolved locally against the read-only repository
and could not find the file; corrected to the actual absolute sandbox path.
