## What changed

Replaced the single sorry in
`AlgebraicGeometry.smooth_proper_diagonal_tensor_formula` by a complete Lean reduction
following Stacks Tag 0A9U. The theorem's signature and existing docstrings are unchanged.

The proof obtains both stalkwise Tor conventions from perfection of the closed-immersion
pushforward. It applies `smoothProper_tensor_perfect_case` for the three bookkeeping
witnesses, the monoidal and pullback-adjunction witnesses, and the comparison on perfect
objects. For every monoidal structure and specified adjunctions, it supplies coproducts
with `derivedQCohDirectSums` and obtains preservation by the right adjoint using
`properPerfect_rightAdjoint_preservesCoproducts`. Its restriction is identified with the
ambient pushforward by the actual `liftCompιIso`, not an unrelated functor.

The property P is the exact existential projection isomorphism and its counit-pinned
mate from the conclusion. The new closure lemma gives the five closure operations.
The perfect-case theorem supplies perfect-object membership. Together these make P an
element of the set defining `perfectLocalizingClosure`; `sInf_le` gives closure ≤ P.
Rewriting by `derivedQCohPerfectGeneration` gives top ≤ P, which is applied to K.
This combination is proved in Lean, rather than moved into a new sorry.

Added proof-only imports of `PerfectImmersionStalkwiseTorBounds` and
`RightAdjointTensorLocusLocalizing`. Removed the proof-only import of
`NoetherianDerivedDirectImageRightAdjoint`. Updated the original node's proof,
proof_deps and proof_origin, and supplied matching nodes for the two new modules.
No statement or definition was changed; no change record is needed.

All three delivered modules compile together through lcompile.py without warnings.
The item's module also compiles separately against the sandbox overlay. Import-direction
checks confirm neither new module reaches the item. Every Lean line has at most
100 characters. The original theorem's signature was checked textually unchanged.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.smooth_proper_diagonal_tensor_formula`
(node `lem-sc-smooth-proper-diagonal-tensor-formula`). No sorry remains in the item.

Added two holes, each in a new module, each a public theorem with exactly `:= by sorry`:

- `AlgebraicGeometry.perfectImmersion_stalkwiseTorBounds`
  (`lem-sc-perfect-immersion-stalkwise-tor-bounds`, module
  `Sheaf.AlgebraicGeometry.PerfectImmersionStalkwiseTorBounds`).
- `AlgebraicGeometry.rightAdjointTensorLocus_localizing`
  (`lem-sc-right-adjoint-tensor-locus-localizing`, module
  `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing`).

This is a decomposition: one original hole closed, two strictly smaller glue statements
added; not a sorry-free proof of the geometric result. Existing imported statements
`AlgebraicGeometry.smoothProper_tensor_perfect_case`,
`AlgebraicGeometry.properPerfect_rightAdjoint_preservesCoproducts`, and
`AlgebraicGeometry.derivedQCohPerfectGeneration` also remain unproved in the base and are
used as intended by stage 3; they were not changed or duplicated. Both new declarations
have detailed natural-language proofs and source places in their docstrings and nodes.
No data is selected from an arbitrary unproved existence theorem: the bookkeeping
witnesses are propositions and the local property P is explicitly defined.

## No longer needed

Removed direct proof import:
`Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint`.
Removed proof dependency:
`lem-pc-noetherian-derived-direct-image-right-adjoint`.
The perfect-case lemma already provides every witness needed by the theorem; its
conclusion is for every right adjoint supplied to the proof. Thus no independently
chosen right adjoint is needed here. The node remains a statement dependency describing
the right-adjoint setting. This is pruning of this item's direct proof dependency;
it does not assert that the module is unreachable from every target.

All four other original proof imports remain used. No other original nodes or modules
are bypassed. The unit's realized arrays are empty and no unit statement or route is
changed; the five argument steps remain represented by the reduction and its glue.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies alone do not expose the two necessary glue statements:

1. Perfection of `Ri_* 𝟙_` is not definitionally either stalkwise Tor-bound hypothesis.
   Moreover the perfect-case lemma uses Mathlib `Tor'` (derived in the first variable),
   whereas coproduct preservation uses `Tor` (derived in the second). Mathlib's Tor
   file explicitly says their comparison needs further theory. The new stalk lemma
   states both bounds, with the restriction along the actual stalk map, and explains
   the bounded projective resolution and double-complex comparison. It does not
   restate any right-adjoint tensor formula.
2. Perfect generation concludes equality for the concrete infimum
   `perfectLocalizingClosure`. There was no theorem establishing the five closure
   properties for the exact existential pf predicate in this item. The new locus
   lemma asserts only those closure properties, assuming coproduct preservation; it
   supplies neither perfect-object membership nor any generation conclusion.

The referenced duality.tex was absent from this local repository. The upstream Stacks
source was fetched read-only into the item's scratchpad and the proof of
`lemma-compare-with-pullback-flat-proper-noetherian` (Tag 0A9U) was read there. It is
precisely the coproduct/localizing/perfect-generation argument implemented here.
LeanFinder found only ordinary sheaf adjunctions; the qualified Loogle search found
no match. LeanSearch returned an internal server error, recorded as unavailable,
not as evidence of absence. Grep found triangle isomorphism tools and the explicit
missing Tor/Tor' comparison note, but no complete theorem replacing either glue lemma.
Repository searches found `closedImmersion_pushforward_stalks` (used in the new stalk
node's proof plan), but no finite-Tor translation for this derived pushforward.
No open change record naming the item was found.

Edge checks for the new statements: the identity immersion gives the free rank-one
stalk module and bound zero; an empty source makes the stalk condition vacuous;
a zero ring makes all Tor groups zero. The bounds depend on the source point, as
required. For the locus lemma, object isomorphisms and retracts are ambient/full-category
ones as appropriate; the empty coproduct is included, shifts may be any integer,
and the cone clause is only for distinguished triangles. No assertion of closure for
an arbitrary nonexact functor or non-coproduct-preserving right adjoint is made.

## New nodes

`lem-sc-perfect-immersion-stalkwise-tor-bounds`: finite Tor bounds in both Mathlib
conventions for the restricted source stalk, deduced from perfection of closed
pushforward of the unit. This is step 1's missing hypothesis translation, with
closed-pushforward stalks, bounded projective resolution, and the balanced double
complex as its proof. The source is the Tag 0A9U hypothesis translation in the original
node, and its proof plan cites the existing closed-stalk node. Its statement is
independent of c, K, projection isomorphisms, and the conclusion of this item.

`lem-sc-right-adjoint-tensor-locus-localizing`: isomorphism, shift, cone, retract and
coproduct closure of the exact counit-pinned comparison locus. The source is the first
two sentences of the Tag 0A9U proof. The named theorem is the argument's closure step;
perfect membership and generation are separate existing theorems combined in the item.
Both new nodes carry actual logged LeanFinder, qualified Loogle and Mathlib grep
searches, with component tools found but no exact replacement. LeanSearch was also
attempted for each statement and is recorded as unavailable.

## Second reading by N3

1. **Statements and unchanged interface.** I diffed the delivered item against the repository
version. The theorem signature is byte-for-byte unchanged; the two added declarations are
strictly smaller glue statements. Their hypotheses and conclusions match the uses in the
proof, and the edge cases recorded in the worker report (identity immersion, empty source,
zero ring, empty coproduct and zero triangle) do not expose a false strengthening.

2. **Proof and axioms.** I compiled all three delivered modules together with
`lcompile.py --all`; compilation succeeds. A probe with `#print axioms` reports only the
allowed axioms plus `sorryAx` for the two intentionally split public theorems. There are no
sorries in definitions and no forbidden declarations. The main theorem itself has no direct
sorry.

3. **Search and source check.** I checked the cited Tag 0A9U proof in the scratchpad and
confirmed that the localizing-subcategory route and the perfect-object reduction are the
same argument. Fresh searches found `CategoryTheory.Tor'`, its projective vanishing lemma,
`Pretriangulated.isIso₃_of_isIso₁₂`, and retract/localizing infrastructure; no existing
single theorem replaces either new glue statement. The Mathlib Tor source explicitly notes
that a general Tor/Tor-prime comparison needs additional theory, supporting the split.

4. **Pruning and imports.** The removed proof-only import of
`NoetherianDerivedDirectImageRightAdjoint` is unused by the proof; the two new proof imports
are required. Public imports remain those needed by the declarations. The original node's
proof, proof dependencies, and proof origin follow the proof text. The unit record has no
realized route entries, so no unit step was bypassed.

5. **Nodes and documentation.** Both new node records contain matching Lean statements,
source places, proof plans, search records, and `status: split`; each theorem has a complete
natural-language docstring and a blueprint tag. The item report lists the one closed hole,
the two added holes, and the pruned dependency. I replaced copied, irrelevant search records in the new nodes with fresh, relevant
LeanFinder, Loogle and grep searches, recorded the unavailable LeanSearch attempts,
added the projection-formula dependency explicitly used by the locus proof plan,
and appended this review. No Lean statement,
definition or proof needed repair. The two glue statements require substantial derived
category infrastructure and could not be closed in a short review pass.
