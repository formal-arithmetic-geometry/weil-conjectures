## What changed

Drafted a reduction of `comparisonIntoPullback_naturality` into two independent arguments:

- `Sheaf.Algebra.Homology.BaseDerivedTensorLocalizedNaturality` states algebraic
  naturality for arbitrary base-derived tensor cohomology models and an arbitrary
  universal derived scalar extension. Its localization-factor identifications are
  actual compositions of existing isomorphisms.
- `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison` states the natural
  derived pullback-stalk identification, including its computation through the
  specified tensor-stalk isomorphism and universal counits. It contains neither
  the localized comparison nor the source tensor-algebra transport.

The item imports the geometric module privately. Its proposed proof identifies
its canonical source transport with the algebraic transport, applies the algebraic
square, applies naturality of the geometric identification, and substitutes the
counit computations. Existing signatures, definitions and visibility are unchanged.
The node proof plan follows this reduction.

Validation: all three delivered modules compile locally. The missing source-transport
cache is now published; no sandbox replacement of it is retained or delivered.
The algebraic helper now permits the derived-category universe w, so it applies
to the standard module derived categories (whose object universe is u+1).
The geometric computation pins the scalar-extension rings explicitly. The
combining proof cancels the exact-stalk localization factors using L.map_comp_assoc
and L.map_id. It elaborates in about 14 seconds within the 60-second file limit;
a declaration-local heartbeat option accommodates the nested localization factors.
Existing signatures and visibility remain identical.

## Proved and sorry left

Hole closed in the item (by decomposition):
`AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality`
(node `lem-pc-stalk-comparison-pullback-naturality`). Its combining proof compiles and has no sorry.

Two holes added, constituting a decomposition rather than a completed mathematical proof:

- `ModuleCat.baseDerivedTensor_localized_naturality`
  (`lem-pc-base-derived-tensor-localized-naturality`).
- `AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparison`
  (`lem-pc-stalk-derived-extension-comparison`).

No sorry occurs in any definition. The algebra lemma contains no scheme or
pullback-stalk comparison. The geometric lemma contains no base-derived tensor
comparison, source transport, or final naturality square. Both are strictly parts
of the original argument. No base flatness, Tor-independence, or comparison
invertibility was added. Edge cases reviewed: identities, zero complexes and zero
coefficient rings satisfy the same constructions; the empty scheme has no point z
and does not introduce an extra condition.

## No longer needed

No existing import was removed and no existing module is claimed pruned. The
K-flat stalk criterion is no longer a direct proof dependency of the item; it is
still needed by the geometric intermediate theorem. The base-derived tensor model,
derived pullback and single-complex stalk-condition nodes similarly remain needed
through the new intermediate nodes and the unchanged statement import. The unique
source lift existence theorem is not applied: the item already supplies its lift e.
The source-transport module remains necessary for its public definitions.

For completeness, the old direct proof dependencies removed are
`def-pc-base-derived-tensor-cohomology-model`, `def-pc-derived-pullback`,
`def-pc-single-complex-base-change-stalk-condition`, and
`lem-pc-kflat-stalk-criterion`. All remain used below the two new nodes;
none is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned module and its source-transport dependency were landed after the
compiled cache's last published version. The latter's .olean is missing even though
its source is available. The cache has now caught up, and the delivery uses the shared dependency.

The algebra model cites Tag 08IB, which is a Tor-independent scheme base-change
lemma. The new algebra statement instead uses More on Algebra's derived change of
rings (06Y6) and the canonical comparison preceding equation-bc (0DJ7). No existing
source citation or interface was changed. The relevant source pages were read at
https://stacks.math.columbia.edu/tag/06Y5 and
https://stacks.math.columbia.edu/tag/0DJ6, with the stalk criterion at 06YB and derived
pullback computation at 0D5S. The repository contains the source citation lists but
not its stacks-project .tex checkout.

The blueprint ancestor helper cannot follow `created.item` values that are module
names. The new nodes' ancestor was recovered from the coordinate-invariance node's
existing blueprint record: `lem-pc-rf-perfect-base-change`. Whole-blueprint searches
for derived scalar extension, pullback stalk, tensor cohomology and stalk comparison
found no matching existing blueprint statements (the scalar-extension hit concerns
finite coefficient field extensions).

LeanFinder, Loogle and grep searches ran and found relevant localization-factor and
derived-transformation APIs but no exact statement. LeanSearch returned HTTP 500;
this is recorded as unavailable, not as absence of a match.

## New nodes

`lem-pc-base-derived-tensor-localized-naturality` isolates the algebraic square
between base-derived cohomology and derived A-to-D extension, for arbitrary
counit-compatible models. Its theorem permits arbitrary derived A-linear
isomorphisms and does not require a geometric representative.

`lem-pc-stalk-derived-extension-comparison` isolates the natural identification of
an exact derived stalk followed by scalar extension with derived sheaf pullback
followed by an exact derived stalk, with its fixed K-flat counit computation.

No change record is needed: no existing interface or definition was changed.


## Second reading by K4

1. Interface preservation: compared the delivered item with the repository using
   diff. The complete `comparisonIntoPullback` definition, the existing theorem
   signature (including all local algebra and derived-category instances), and
   both existing docstrings are byte-for-byte unchanged. Only a private import,
   a declaration-local heartbeat option and the theorem proof were added. There
   are no adaptations or existing-interface changes requiring a change record.
   Verdict: pass.
2. Proof and axioms: compiled all three modules in import order with lcompile.py
   (2.1, 4.5 and 13.3 seconds), without errors or warnings. Read the combining
   proof: `he'` unfolds the two input transports; `hk` uses naturality of j after
   cancelling the exact-stalk factors; `hkH` applies homology; `hcompP` and
   `hcompQ` substitute the specified counit computations; postcomposing `hn`
   then gives precisely the original square. Separate scratch-copy #print axioms
   checks covered all seven delivered declarations: only propext, Classical.choice,
   Quot.sound, and sorryAx from the two explicitly open new theorems and existing
   dependencies. The three new data definitions use actual isomorphism composition,
   not choice from an unproved existence theorem. L and j are eliminated only
   within a proposition proof. No forbidden declaration or hollow definition was
   introduced. Verdict: pass as a decomposition, not a sorry-free proof.
3. New statements: read both Lean signatures, node statements and proof docstrings
   against Stacks 06Y6, 0DJ7, 06YB and 0D5S. The algebraic lemma retains arbitrary
   counit-compatible models and universal A-to-D extension, requires invertible
   counits only on the two inputs, and asserts no flatness or invertibility of
   localizedComparison. The model's comparison_eq, localized_eq and pure-tensor
   equations fix its maps, so arbitrary model choices do not permit arbitrary
   comparison maps. The geometric lemma uses the actual A-to-C stalk map,
   K-flat stalks (06YB), and precisely the tensorStalkIso specified degreewise in
   SingleComplexBaseChangeStalkCondition. Tag 0D5S supports the computation and
   composition of derived pullback on K-flat representatives; the exact interface
   and its counit computation are the agent's specialization, not a verbatim
   Stacks lemma. Neither new theorem states the original final square: one has
   no schemes, the other no model comparison or source cohomology transport.
   Identity maps give the identity square; zero complexes have zero homology;
   zero coefficient rings have zero target modules; an empty X' provides no z.
   No excluded edge case or extra geometric hypothesis was found. Independent
   LeanFinder search for derived change-of-rings natural comparison returned Ext
   and exact-functor APIs, not either statement. Loogle with the shortened name
   Functor.leftDerivedNatTrans found no identifier; direct inspection of Mathlib's
   LeftDerived.lean located CategoryTheory.Functor.leftDerivedNatTrans and its
   counit equation, which provide ingredients rather than the required composite
   derived comparison. Grep with stalk/derived and scalar-extension naturality
   terms found no exact existing statement; PullbackStalkTensorComparison records
   objectwise comparison invertibility, not this natural identification.
   Verdict: both holes are true, needed, strictly partial arguments; neither can
   be closed by a short application of an existing theorem.
4. Route and pruning: read the original proof_deps, both new plans and
   dag/units/sk-thm-picard-semicon.json. Its realized statement and step entries
   are empty, and no recorded unit step was bypassed or changed. The original
   base-model, derived-pullback, single-complex stalk-condition and K-flat stalk
   dependencies remain under the new reduction. The source-transport import is
   public because existing definitions and signatures use it; the new geometric
   import in the item is private. Both imports of the geometric module and both
   imports of the algebra module supply names appearing in their public data or
   theorem signatures. No import or globally unreachable module is pruned.
   Verdict: pass; expanded No longer needed to name every removed direct node.
5. DAG agreement: compared the existing node against its repository version;
   only proof, proof_deps and proof_origin changed. The new nodes have matching
   Lean declarations/statements, source, complete proof steps, their dependency
   unions, searches, created records and the parent's chapter and unit. The new
   geometric statement uses scalarExtensionHomologyIso from the algebraic module;
   its stmt_deps omitted the node carrying that definition. Added
   lem-pc-base-derived-tensor-localized-naturality to that stmt_deps. This is a
   signature dependency, not an application of its still-open naturality theorem.
   Verdict: pass after this metadata repair.

Second reading changed the geometric node's missing statement dependency and
made the removed direct proof-dependency list explicit in the report. The Lean
proofs were retained. One original hole is closed by combination, two lower holes
are added (net minus one); no mathematical completion or pruning is claimed.
