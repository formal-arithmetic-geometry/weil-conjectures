## What changed

Proved AlgebraicGeometry.finite_affine_adjoint_counit_comparison with its original
signature. The module now imports FiniteAffineDerivedFactorization and
FiniteScalarRightAdjointQCoh privately, together with the existing
FiniteAffineDerivedEquivalence. All original public imports remain unchanged.

The two private, fully proved categorical helpers establish the actual comparison:
the geometric adjunction and the fully faithful affine functor give bijectivity of
postcomposition by the ambient mate of the geometric counit. Essential surjectivity
at the specified scalar right-adjoint value constructs an inverse. The ambient
adjunction gives the counit equation, and the final proof cancels the global
pushforward comparison. This handles the specified comparison and adjunctions,
including arbitrary automorphisms of them.

Two new modules isolate the geometry; the factorization is now proved and
only scalar right-adjoint membership remains open. The existing DAG node now
records precisely this proof route. No existing definition, statement, or target
signature was changed. The unit's realized statement and steps are not bypassed;
its realized lists are empty, and the existing affine derived equivalence remains used.

## Proved and sorry left

Proved (1 of the item's 1 original sorry):
AlgebraicGeometry.finite_affine_adjoint_counit_comparison,
node lem-sc-finite-affine-adjoint-counit-comparison.
The item's module contains no sorry.

The first reading split two statements. The second reading proved
AlgebraicGeometry.finite_affine_derived_factorization using upstream exact-functor
composition. The delivery now adds exactly one named sorry:

- AlgebraicGeometry.finite_scalar_right_adjoint_qcoh,
  node lem-sc-finite-scalar-right-adjoint-qcoh,
  module Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh.

The remaining statement asserts only quasi-coherence, not an isomorphism of the
two right-adjoint values or the geometric counit identity.
This is a decomposition: one original hole closed, one new hole added, net zero;
the new factorization module is fully proved relative to imported declarations. The existing
finite_affine_derived_equivalence remains an imported unproved dependency; no copy
of its statement or proof was added here.

All three delivered modules compiled cleanly with lcompile.py --all. The generic
categorical helper also compiled independently during development. Identity finite
morphisms, zero objects, empty schemes, and shifted inputs were checked against the
new statements: exact restriction and natural pushforward comparisons apply in all
these cases, and quasi-coherence is invariant under the isomorphisms arising from
any specified right adjoint. No boundedness of a(K) is needed by the proof, although
its binder is preserved and explicitly acknowledged in the proof.

## No longer needed

Removed the following direct proof imports from the item's module:

- Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent
  (lem-sc-finite-pushforward-derived-hom-qcoherent).
- Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
  (lem-sc-finite-sheafhom-affine-adjoint).
- Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule
  (def-pc-derived-rhom-algebra-module).
- Sheaf.AlgebraicGeometry.AffineDerivedCohomology
  (lem-sc-affine-derived-cohomology).
- Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
  (def-pc-ringed-spaces-derived-direct-image), available through SchemeDerivedDirectImage.

The old proof dependency def-pc-derived-direct-image also leaves the explicit
proof_deps list; its definitions remain used in the statement and factorization.
All old proof_deps except lem-sc-finite-affine-derived-equivalence leave the
main node's direct proof dependency list; none is claimed unreachable globally.

The first three remain dependencies of the new geometric statements; affine derived
cohomology remains a dependency of the existing affine equivalence. Therefore this
is direct-import pruning, not a claim that these modules disappear from the entire
target closure. The extra lower-bound-preservation argument and restriction to
D+_QCoh(A) in the original Step 3 are unnecessary: the existing equivalence is
unbounded, and the generic argument tests all quasi-coherent objects. No additional
whole module or node can be declared unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier route unnecessarily demanded lower-bound preservation by the affine
equivalence. Quasi-coherence of the ambient scalar right-adjoint value suffices for
pointwise representability in the unbounded full subcategory, so the bound haK is
not used mathematically. This does not alter any statement.

The affine-equivalence statement only supplies pushforward/scalar comparison on the
quasi-coherent subcategory, whereas this item's first existential requires a
comparison on the whole derived category. The new factorization theorem isolates
this missing global assertion. The affine sheaf-Hom adjunction supplies a separately
chosen derived right adjoint, while finite derived-Hom quasi-coherence is stated for
its explicit algebra-valued Hom construction and includes extra local derived
category instances. The new scalar-right-adjoint membership theorem isolates that
identification and transport; those interfaces do not directly give membership of
an arbitrary specified rhoR by a single application.

Sources checked: Stacks Project Tags 0AVW and 0AX2, statement and proof
(https://stacks.math.columbia.edu/tag/0AVW and
https://stacks.math.columbia.edu/tag/0AX2). The local literature source files are absent
on this machine. Searches used msearch LeanSearch (unavailable: Internal Server Error), leanfinder,
loogle, and grep, together with
local rg over both library roots and the DAG and blueprint_refs searches. They found
underived pushforward formulas and generic adjoint uniqueness, with no exact match
for either new geometric statement. No compilation-tool failure or disputed statement was found.

## New nodes

lem-sc-finite-affine-derived-factorization isolates original Step 1, the natural
comparison on the whole derived category. Its proof uses exact scalar restriction
and the canonical K-injective pushforward comparisons, including their natural
localization maps. Its module now proves the named theorem by exact-functor composition.

lem-sc-finite-scalar-right-adjoint-qcoh isolates original Step 3, membership of the
specified scalar right-adjoint value in the algebra quasi-coherent full subcategory.
Its proof identifies the explicit Hom right adjoint, applies finite pseudo-coherence
and derived-Hom quasi-coherence, and transports membership by right-adjoint
uniqueness. Its module contains only the named theorem and its sorry.

No change records are needed, since no existing statements or definitions changed.


## Second reading by T1

1. Compared the delivered main module with the repository by diff and compared the
   complete existing theorem signature byte for byte: identical. Its docstring,
   universes, finite/Noetherian assumptions, three derived-category instances,
   specified comparison and adjunctions, both boundedness binders, and the displayed
   counit equality are unchanged. No definition or target statement changed.
2. Compiled all three delivered modules through lcompile.py in dependency order.
   Explicit scratch #print axioms showed the first categorical helper uses propext;
   the second uses propext, Classical.choice and Quot.sound. The main theorem uses
   those plus sorryAx from open imported statements. There are no forbidden trust
   constructs or hollow definitions. The only delivered sorry now is
   AlgebraicGeometry.finite_scalar_right_adjoint_qcoh. The delivery axiom probe also
   checks the final factorization proof.
3. Read Stacks Tags [0AVW](https://stacks.math.columbia.edu/tag/0AVW),
   [0AX2](https://stacks.math.columbia.edu/tag/0AX2), and
   [0BV0](https://stacks.math.columbia.edu/tag/0BV0), and the complete statements of
   finite_affine_derived_equivalence, exists_affine_derivedSheafHom_adjunction,
   finite_pushforward_derivedHom_qcoherent and the algebra-valued Hom construction.
   Finite plus Noetherian gives the pseudo-coherence needed in 0AX2; bounded-below
   K supplies its D+ input. Right-adjoint uniqueness transports membership for any
   specified adjunction. The auxiliary local derived-category instances required
   by the existing Hom membership theorem must be chosen when its eventual proof
   is written; their absence here does not restrict or invalidate this statement.
   Identity maps reduce to the identity scalar functor; zero and empty cases have
   zero Hom values; shifts change only lower bounds. Both new statements are true
   strict parts of the argument, and neither restates the counit comparison.
   Independently searched leanfinder for exact forgetful functors commuting with
   derived pushforward, Loogle for rightDerivedFunctor (identifier unavailable in
   its Mathlib index), grep for quasi-coherent right adjoints and derived
   composition, and rg over both Lean roots and the upstream checkout. The search
   found upstream exact-functor composition and natural-isomorphism tools, used to
   close the factorization, but no duplicate scalar-membership theorem.
4. Checked the categorical reduction top downward: the mate g of the geometric
   counit induces bijections from the fully faithful image; the equivalence provides
   a test object N representing its codomain. Surjectivity constructs a right
   inverse and injectivity proves the other inverse equation. Naturality of beta
   gives the counit formula, and cancellation of c gives exactly the original
   equality. This handles automorphisms of all specified comparisons. The unit
   sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]]; no
   realized node is bypassed, and the existing affine equivalence is used. All
   removed direct imports and old proof dependencies are now listed above; this
   is direct pruning only, not an unreachable-module claim. The remaining geometry
   does not admit a one-line application of the existing interfaces.
5. Compared all three nodes with their Lean declarations. Main proof_deps are the
   affine equivalence, factorization and scalar membership, exactly as used. The
   factorization proof uses scalar exactness from DerivedRHomAlgebraModule and the
   direct-image definitions plus upstream categorical composition; its proof and
   proof_origin now record that route. The scalar-membership node retains its
   source, complete prose argument and dependencies. New nodes have separate
   modules, verbatim signatures, source/blueprint/created/search records. Existing
   node edits are confined to stage-3-owned proof fields.

Changes made in the second reading: proved finite_affine_derived_factorization;
added its private upstream proof import and an explained local heartbeat budget
for unfolding the ring-sheaf presentations; updated its node proof/proof_origin;
corrected the report's hole accounting and omitted direct pruning entries.
The main categorical proof and all existing public signatures were retained.
