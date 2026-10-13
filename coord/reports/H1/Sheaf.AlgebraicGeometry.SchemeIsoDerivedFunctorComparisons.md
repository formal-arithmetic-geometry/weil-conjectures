## What changed

Proved `AlgebraicGeometry.schemeIso_derived_functor_comparisons` in
`Sheaf.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons`, with its statement and
visibility unchanged. Added proved private helpers `moduleIsoEquivalence`,
`iso_directImage`, `iso_tensor`, and `pullback_comparison`.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`,
`Sheaf.AlgebraicGeometry.DerivedAdjoint`,
`Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction`, and
`Mathlib.CategoryTheory.Adjunction.Mates`. Existing public imports are unchanged.
Updated the original node's proof, proof dependencies and proof origin to the implemented route.

The supplied localization comparisons identify each supplied equivalence with direct image
along the scheme isomorphism. A monoidal pullback/direct-image adjunction supplies the inverse
monoidal equivalence and hence both tensor comparisons. Direct-image composition and hcomm give
the direct-image square. Conjugating this square through the two derived adjunctions, then
cancelling the equivalence unit and counit, gives the pullback square.

The existing monoidal-adjunction tool carries the K-flat tensor construction; the existing
direct-image composition tool carries the K-injective composition construction. No unit
statement or realized unit step is bypassed: this node is not in the unit's realized fields.
The exact-functor factorization is an existing Mathlib leaf used as a generic tool.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.schemeIso_derived_functor_comparisons`
(node `lem-pc-scheme-iso-derived-functor-comparisons`). No sorry remains in the delivered
module. No holes were added or split off. The existing imported results may depend on their
own existing holes; those dependencies are not newly stated or changed in this delivery.

The single-file compilation passed. The construction uses arbitrary given scheme
isomorphisms and equivalences, with independently chosen localization universes. It makes
no nonemptiness, quasi-coherence or scheme finiteness assumption, and applies to identity
isomorphisms, empty schemes and zero complexes through the same categorical comparisons.

## No longer needed

The planned dependency `lem-pc-scheme-iso-derived-equivalence` and its module
`Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence` are unnecessary for this proof:
localization uniqueness identifies the already supplied equivalences directly with derived
direct image. Removed that proof-dependency edge. This does not assert that other callers
of that module are gone.

No original Lean import was removed: the three existing public imports are required by the
unchanged statement. Removed an experimental proof-only import of
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` after compiling successfully without it.
No additional planned node or module is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The previous plan expanded tensor transport
and pullback transport separately on resolutions. The existing monoidal-adjunction and
direct-image composition declarations already supply the needed geometric input, so the
remaining transport can be proved categorically, without adding intermediate statements.
The existing theorem docstring describes the original longer resolution argument; the DAG
proof record and Lean proof now give the shorter route.

## Second reading by H1

1. I compared the delivered module with the repository version. The theorem signature and all
existing declaration interfaces are byte-for-byte unchanged; only proof-only imports, private
helpers, and the target proof differ. The DAG node records the revised proof route and dependencies.
Verdict: pass.

2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings. The target's
axioms include `sorryAx` only through existing imported declarations still open elsewhere; this
delivery introduces no `sorry`, axiom, unsafe, opaque, extern, or hollow definition. The target
proof closes its sole local hole. Verdict: pass.

3. The supplied equivalences are arbitrary but their localization isomorphisms determine the
localized functor up to the natural isomorphism used by the proof. The private helpers construct
only the required comparisons, and no split-off statement or new node is introduced. The identity,
empty-scheme, and zero-complex cases are covered by the same categorical constructions. Verdict:
pass.

4. The proof follows the shortest available route through exact localization factorization,
the existing monoidal pullback/direct-image adjunction, direct-image composition, and Mathlib's
conjugate adjunction isomorphism. The stated unit route is preserved; this node is not a realized
unit step. The obsolete scheme-isomorphism-equivalence dependency is removed because the local
helper proves the needed comparison directly. Verdict: pass.

5. The Lean proof, DAG `proof`, `proof_deps`, and `proof_origin` agree: each imported declaration
used by the proof is listed, and the removed dependency is no longer referenced. Imports used only
for proofs are plain imports. Verdict: pass.

I changed only the proof implementation and its proof-only imports, updated the node's proof
metadata to match, and added this second-reading record. No statement, definition, or public
interface was changed.
