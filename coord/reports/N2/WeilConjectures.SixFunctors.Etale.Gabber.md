## What changed

`WeilConjectures.SixFunctors.Etale.Gabber` now proves
`AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing` by a genuine
reduction: filtered continuity supplies a bounded module sheaf G and a representative;
bounded abelian surjectivity lifts the representative to the source; the injection into
an injective module sheaf factors through its n-annihilator E; acyclicity of E kills the
lift; a pushout along G → F gives the required monomorphism. Private proved helpers
establish bounded representability, torsion of E and torsion of the pushout. Every surviving signature and visibility is unchanged. In repair E2, the false
`exists_isFinite_cohomologyMap_eq_zero_of_henselianRing` declaration and its
Main statements entry are removed completely; its node has no active Lean attachment.
The removal is recorded in
`coord/changes/exists_isFinite_cohomologyMap_eq_zero_of_henselianRing.md`.
The downstream inventory finds no external user, so no adaptation is required. The target comparison's long-exact-sequence
induction is unchanged. The auxiliary exactness proof now uses the existing colimit
preservation theorem, while the finite-limit instance is unchanged.

The earlier attempt was not compiled and had no nodes or report. Its colimit universes
and identity-map rewrite were repaired. Explicit inverse-image adjunction avoids an
expensive instance search; transparency options are scoped to the new proofs. Two new
public theorem modules isolate independent arguments, each with its source, proof
in words, and node; the second reader proves annihilator acyclicity. No data is defined using an arbitrary unproved witness.
The injective presentation and kernels are existing genuine constructions; all new data
chosen in the proof is local to a theorem.

Added proof imports:
- `Mathlib.Algebra.Category.ModuleCat.Biproducts`
- `Mathlib.CategoryTheory.Abelian.CommSq`
- `Mathlib.CategoryTheory.Category.ULift`
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
- `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity`
- `Sheaf.AlgebraicGeometry.InjectiveModuleAnnihilatorAcyclic`

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing`
(node `lemma-weil-pbc-gabber-effacement`) by a genuine bounded-representative,
injective-annihilator and pushout reduction. All three new private helpers are proved.
The second reader also closed
`AlgebraicGeometry.Etale.subsingleton_H_kernel_nsmul_injective_module`
(node `lem-weil-pbc-injective-module-annihilator-acyclic`) using the existing
restriction/coextension adjunction, quotient counit exactness and injective module
acyclicity. This auxiliary theorem contains no sorry; its dependencies remain open
and #print axioms includes sorryAx from them.

One new hole remains, as the entire proof of its public theorem:
`AlgebraicGeometry.Etale.surjective_cohomologyMap_of_henselianRing_of_nsmul_eq_zero`
(node `lem-weil-pbc-henselian-bounded-abelian-surjectivity`). It concerns only bounded
abelian coefficients and surjectivity and has an independent finite Z/n proof plan.
No original hole remains in Gabber.lean.

The second original hole,
`AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing`
(node `lemma-weil-pbc-finite-cover-killing`), is retired as false, not proved.
Thus 1 of 2 original holes is decomposed with 1 new hole left; the other is removed
as false. Retirement is not a proof. There is no claim of positive ledger progress:
net progress in the target import closure, including added proof imports, is measured
by the maintainer's pinned sorry ledger. No nonstandard axiom other than sorryAx
through open dependencies is introduced. The unit route is kept.

Edge cases checked: n=1 kills both bounded G and its annihilator envelope; q=0 is
included in bounded surjectivity but excluded from annihilator acyclicity; zero rings
and empty schemes satisfy both statements. Annihilator acyclicity needs no regularity
of n and its new proof even works for n=0, while retaining the positive-n hypothesis.

## No longer needed

Retired node: `lemma-weil-pbc-finite-cover-killing`; its false Lean theorem is
removed, not weakened or retained as a sorry. Its former proof dependencies are
not needed for any finite-cover-killing proof; no such proof is asserted.


Removed direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `WeilConjectures.SixFunctors.Finite.Stalk`

Their recorded nodes (removed as direct proof dependencies of this item's new effacement
route where present):
- `def-constructible-constructible`
- `def-constructible-finite`
- `def-constructible-finite-locally-constant`
- `def-constructible-locally-constant`
- `def-weil-pbc-cartesian-square`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-etale-constructible-sheaf`
- `def-weil-pbc-etale-sheaves`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-underived-exchange`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-constructible-module-finite-pushforward-embedding`
- `lem-weil-pbc-counit-stalk-germ-restriction`
- `lem-weil-pbc-direct-image-left-exact`
- `lem-weil-pbc-etale-base-change-continuous`
- `lem-weil-pbc-finite-pushforward-cohomology`
- `lem-weil-pbc-finite-pushforward-unit-edge-compatibility`
- `lem-weil-pbc-finite-stalk-formula-restriction`
- `lem-weil-pbc-finite-surjective-unit-mono`
- `lem-weil-pbc-integral-cover-kills-constant-cohomology`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-inverse-image-preserves-colimits`
- `lem-weil-pbc-module-sheaf-colimit-constructible`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-surjective-module-pullback-faithful`
- `lemma-constructible-pullback-constant`
- `lemma-weil-pbc-finite-exchange`
- `lemma-weil-pbc-finite-stalk-formula`
- `lemma-weil-pbc-underived-exchange-naturality`
- `prop-weil-pbc-finite-morphism`
- `prop-weil-pbc-inverse-image-exact`

Complete old `proof_deps` removed by the new route (including foundational nodes
whose notions still occur in signatures, but are not separate proof steps):
- `def-pc-fibre-product`
- `def-weil-additive-category`
- `def-weil-finite-integral-morphism`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-cartesian-square`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-etale-constructible-sheaf`
- `def-weil-pbc-etale-sheaves`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-underived-exchange`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-abelian-sheaf-epi-locally-surjective`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-constant-module-sheaf-underlying`
- `lem-weil-pbc-constructible-module-finite-pushforward-embedding`
- `lem-weil-pbc-finite-composition`
- `lem-weil-pbc-finite-morphism-permanence`
- `lem-weil-pbc-finite-pushforward-cohomology`
- `lem-weil-pbc-finite-pushforward-unit-edge-compatibility`
- `lem-weil-pbc-finite-surjective-unit-mono`
- `lem-weil-pbc-integral-cover-kills-constant-cohomology`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-module-sheaf-colimit-constructible`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-qcqs-over-affine`
- `lem-weil-pbc-torsion-sheaf-characterizations`
- `lemma-constructible-pullback-constant`
- `lemma-weil-pbc-finite-exchange`
- `prop-weil-pbc-inverse-image-exact`

These are removals from this module, not claims that every listed module leaves the
whole target closure. `TorsionEtaleSheaf` and `TorsionSheafCharacterizations`
are retained because the delivery classifier identifies them as unit-route modules.
In particular finite-pushforward embeddings, finite exchange,
finite constant cover killing and unit/edge compatibility remain needed by the bounded
abelian lemma's independent finite-coefficient proof plan. The original finite-cover
killing theorem is neither imported nor invoked by that plan: 09ZD for finite constant
coefficients is used instead. All five original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The finite-cover killing statement for arbitrary constructible C is false. Take
A = C[t], I = 0 (a henselian pair), Λ = Z/2, X = A¹_C, Z = {0,1},
and j:U=X\Z → X. Let Csheaf=j!Λ. It is constructible. The exact sequence
0 → j!Λ → Λ_X → Λ_Z → 0 shows that the boundary c of (0,1) in H⁰(Z,Λ)
is a nonzero element of H¹(X,j!Λ): global sections of Λ_X are constant and cannot
restrict to (0,1). Suppose h:V→X were finite with a monic unit for j!Λ.
At a geometric generic point j!Λ has stalk Λ. An empty generic fibre would make the
stalk of h_*h^*(j!Λ) zero, contradicting monicity, so h has a nonempty generic fibre.
Choose the closure W in V of a generic point above the generic point of X. W is an
irreducible closed subscheme, finite and surjective over X (its closed image contains
the generic point). In particular W is connected and has nonempty fibres above both
0 and 1. Exact inverse image and the constant-sheaf pullback isomorphism pull back the
boundary sequence to W. A global section of Λ_W is constant on connected W and cannot
restrict to 0 on the fibre over 0 and to 1 on the fibre over 1. Thus the boundary is
still nonzero on W. If it died on V, functorial pullback would make it zero on W, a
contradiction. No finite h with the asserted monic unit kills c. The I=0 case alone
refutes the old declaration. Repair E2 removes that declaration completely,
rather than retaining a false axiom; the node's active Lean attachment is null.
Its proof and proof dependencies are retired and its proof_origin records why.

Stacks [09ZD](https://stacks.math.columbia.edu/tag/09ZD) concerns finite constant
coefficients; [09ZE](https://stacks.math.columbia.edu/tag/09ZE) changes constructible
coefficients by a monomorphism. The source library's broader finite-cover statement
confuses these. Neither its original DAG proof nor this delivery proves it.

The effacement DAG states the stronger non-henselian abelian result of 09ZE, while
its existing Lean declaration has a henselian hypothesis and Λ-module coefficients.
This delivery preserves that declaration and records the route actually proving it.
The unit's realized statement and steps are unchanged: Gabber remains the affine
comparison used by the projective-line calculation. No unit-level route is bypassed.

The local Stacks TeX files are absent on this machine. The source proofs were read
at the linked Stacks tags 09ZE, [09ZI](https://stacks.math.columbia.edu/tag/09ZI),
and [03FD](https://stacks.math.columbia.edu/tag/03FD). LeanFinder, Loogle and local
Mathlib/library grep found no direct theorem for these gaps. LeanSearch returned
Internal Server Error on both new searches; its unavailability is recorded rather
than treated as a negative mathematical search result. The existing
`InjectiveModuleSheafHCohomology` is recorded in the annihilator lemma's proof plan.

## New nodes

`lem-weil-pbc-henselian-bounded-abelian-surjectivity`, in
`Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity`: the surjective,
bounded-abelian part of henselian comparison, independently obtained by the finite-ring
09ZE effacement and long-exact-sequence induction of 09ZI. Its node explains how degree
zero is established without importing Gabber.lean, so the future proof has no import cycle.

`lem-weil-pbc-injective-module-annihilator-acyclic`, in
`Sheaf.AlgebraicGeometry.InjectiveModuleAnnihilatorAcyclic`: change coefficients to
Λ/(n), observe that the annihilator is the right adjoint of exact restriction of
scalars and hence injective over Λ/(n), then apply the existing 03FD acyclicity theorem.
It is strictly the acyclicity step of the general-module effacement construction.

Repair change record:
`coord/changes/exists_isFinite_cohomologyMap_eq_zero_of_henselianRing.md`.
It records removal of the false public declaration, the counterexample and every
one of the 147 downstream modules, with current holders. No external module
mentions the removed name; no forced adaptation is needed. Surviving signatures,
visibility, public imports, target statements and definitions are unchanged.

Repair B9 whole-blueprint search, 2026-10-13: ran
`tools/blueprint_refs.py search` for `henselian` (26 hits), `09ZI` (1 hit),
`annihilator` (0 hits), `injective cohomology` (25 hits), `03FD` (0 hits),
and `bounded abelian` (33 hits), across all chapters, not just target reach.
Also searched dag/nodes with rg for annihilator, 09ZI, 03FD and henselian
surjectivity. Read the related affine-comparison and injective-restriction
statements: the former is broader (and its relative form is disputed), the
latter concerns restriction to a closed fibre with a cover bound, not the
annihilator of an injective. None states either new lemma in another form.
Both new nodes therefore record `same_as: []`; each now records exactly the
`from.place` requested in B9.

Repair C1: the fourth bounded-surjectivity proof step and proof_deps now cite
`lemma-weil-pbc-stein-connectedness`. The Lean docstring explicitly explains
that henselian Stein connectedness supplies the nonempty connected closed-fibre
intersections, followed by the abelian global-sections criterion and the
degree-zero cohomology comparison. No Lean signature changes in this step.

The earlier second-reading section below is the earlier reader's historical report,
which predates the E2/B9/C1 repair; its remarks about the finite-cover theorem
remaining and absence of an interface change no longer describe this delivery.
A fresh independent reading is required.

## Earlier second reading (a previous round; superseded)

1. Compared Gabber.lean with the repository using diff and the declaration parser:
   every existing signature and visibility is unchanged, and all five public imports
   are identical. Only proofs, private helpers, proof imports and explanatory comments
   change. No interface change record is needed.
2. Read the entire delivered module and both new modules. The two new modules compile;
   Gabber.lean compiles in 52.3 seconds. The first set compile timed out at 60 seconds;
   a single-file retry succeeded without a code change. No forbidden declaration or
   data-level hole occurs. Exactly the reported original disputed theorem and the two
   public split-off theorems retain sorry. The delivery probe checks every declaration;
   the explicit axiom scratch check is recorded below.
3. Verified the two new statements against Stacks 09ZE, 09ZI, 09ZD and 03FD. The
   bounded comparison argument works independently over Z/n, including n=1 and q=0.
   The annihilator argument uses exact restriction of scalars and its right adjoint,
   so does not assume that n is regular or that forgetting coefficients preserves
   injectives. Empty schemes and the zero coefficient ring cause no exception.
   Independent LeanFinder, Loogle and grep searches found no direct replacement.
   Loogle found vanishing for injective abelian sheaves, which does not apply to this
   underlying abelian sheaf without a new injectivity hypothesis. The existing proved
   InjectiveModuleSheafHCohomology is the acyclicity endpoint already in the new node.
   LeanFinder also found `Injective.injective_of_adjoint`, which implements the
   abstract preservation step, but not the quotient-ring sheaf adjunction.
   Constructing that adjunction is substantial work, so neither
   new hole was closed during this reading. Neither is a renaming of effacement.
4. Checked the representative, kernel factorization, torsion proof, naturality and
   pushout equation from the top downward. The short-exactness simplification uses
   the proved coefficient-forgetful colimit theorem. Added imports are proof-only;
   removed imports match the report. Completed the list of removed old proof_deps.
   The unit sk-thm-p1 realized statement and all four realized step lists are intact;
   the affine comparison remains in the projective-line route. This is one hole
   closed by two strictly narrower holes, hence decomposition with net -1.
5. Checked both new node signatures against Lean, required fields, sources and proof
   dependency unions. The existing effacement node still states the stronger
   non-henselian abelian result, while its pre-existing Lean attachment is henselian
   and module-valued. This delivery proves that attachment only, not the full node
   statement; the mismatch is reported, never concealed by changing a signature.
   Clarified that scope in its new proof plan.

Changes in this reading: completed the pruning inventory, clarified the existing
node's proof scope, removed two stray blank lines, and added this independent review.
No mathematical statement or proof was rewritten.

Explicit axiom scratch check: all 14 declarations in Gabber.lean were checked with
#print axioms and compiled in 54.5 seconds. The three private helpers and the
short-exactness lemma use only propext, Classical.choice and Quot.sound. The
effacement/comparison and older reductions also use sorryAx through their reported
open dependencies. No additional axiom appears.

## Earlier second reading (a previous round; superseded)

1. Compared all delivered modules with the repository. The only removed existing
   declaration is the false finite-cover-killing theorem, explicitly declared in
   the E2 change record; rg finds no external user. Every surviving declaration's
   signature and visibility is unchanged, and all five original public imports
   are identical. The target statements and definitions are untouched. New module
   imports used solely by proofs are plain imports. Verdict: pass.
2. Compiled all three delivered modules through lcompile.py, with Gabber taking
   49.5 seconds in the initial set. Read the entire proofs and scanned for forbidden
   declarations and data holes. The sole direct sorry is the reported public bounded
   surjectivity theorem. Explicit scratch #print axioms checks and the delivery's
   all-declaration probe allow only propext, Classical.choice, Quot.sound and sorryAx
   through the documented open dependencies. Verdict: pass; dependency proofs remain
   open, so this is not an axiom-free target proof.
3. Checked the split statements and docstrings against Stacks 09ZE, 09ZH, 09ZI and
   03FD. The finite Z/n route is independent of Gabber.lean; its induction requires
   simultaneous bijectivity, as the docstring states. The quotient counit identifies
   coextension with the annihilator even when n is a zero divisor. Tested n=1, q=0,
   empty schemes and zero rings. Independent LeanFinder searches used quotient-ring
   coextension and bounded-exponent restriction wording; Loogle found
   Injective.injective_of_adjoint. Library rg found the abelian-injective annihilator
   theorem, whose injectivity hypothesis does not follow by forgetting module
   coefficients. A wider search found the existing sheaf coextension adjunction and
   quotient counit exactness lemmas, which now close the new annihilator theorem.
   Bounded surjectivity has no direct independent replacement. Verdict: pass.
4. Read downward through representative continuity, the monic kernel factorization,
   annihilation, naturality, pushout vanishing and the unchanged comparison induction.
   The pruning list records every old effacement proof dependency no longer used;
   it claims direct-import removal, not disappearance from the entire target closure.
   The sk-thm-p1 realized statement and all four step lists remain unchanged; affine
   comparison stays in the projective-line route. The finite-cover counterexample is
   valid: a dominating connected component of any finite cover forced by monicity
   meets both endpoints, where the pulled-back boundary has incompatible values.
   Verdict: pass; one-hole decomposition and false-theorem retirement are separate.
5. Checked new node signatures, fields, sources, proof/dependency unions and existing
   node diffs. Existing node edits are only proof, proof_deps, proof_origin and lean.
   The effacement node's stronger non-henselian abelian statement still exceeds its
   pre-existing Lean attachment; the new plan explicitly records that scope mismatch.
   The retired node has no active Lean declaration. Updated the annihilator node's
   steps to describe the actual proved coextension/kernel-isomorphism argument.
   Verdict: pass for the attached Lean declaration; the stronger node remains open.

Changes in this reading: proved annihilator acyclicity from existing declarations,
added its three proof imports, named its unused positive-n binder _hn, updated its
node proof and signature record, and corrected the current hole accounting. Pruned the broader Derived.CoextendScalars proof import from the new theorem,
using the smaller RestrictScalars and module ChangeOfRings modules and constructing
the counit short complex locally. Updated the module overview to record that only
bounded surjectivity remains open. No
surviving repository statement, definition, public import or unit route changed.

Final second-reading checks: the narrowed-import annihilator proof compiles in
6.8 seconds with no warnings. Its explicit #print axioms shows only propext,
Classical.choice, Quot.sound and sorryAx through open imported results. The Gabber
scratch axiom check compiled in 56.9 seconds and checked all 13 declarations;
all three private helpers have only the standard axioms. The full delivery dry run
also compiles each module and probes every declaration before preflight.

The new annihilator node also cites the existing Mathlib leaf
lem-sp-right-adjoint-preserves-injectives for the adjoint preservation step.
Repair H10 validation: removed the four scoped
`backward.isDefEq.respectTransparency` options from Gabber.lean, which reduced
elaboration overhead without changing any declaration or proof statement. The
prescribed module-set compile completed successfully for all three delivered
modules, and the all-declaration axiom probe completed successfully for
Gabber.lean. The final `deliver3.py N2 WeilConjectures.SixFunctors.Etale.Gabber
--no-push` dry run reported OK and preflight passed.

## Second reading by N2

1. Compared the delivered `Gabber.lean` with the repository version. All surviving
   declarations retain their original signatures and visibility; the only removed
   declaration is the explicitly retired false finite-cover theorem, covered by its
   change record. Target statements, definitions, and unit realized steps are unchanged.
   Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds
   without errors or warnings. Scanned for forbidden declarations and data-level holes.
   The only remaining direct `sorry` is the named bounded-surjectivity theorem, with its
   node and docstring; the annihilator split theorem is proved. Open imported results
   account for any `sorryAx` reported by axiom checks. Verdict: pass.

3. Checked the two split statements for truth, strength, edge cases, sources, and
   duplication against the library and Mathlib. Bounded surjectivity is the strict
   coefficient-bounded comparison subproblem; annihilator acyclicity is the strict
   injective-annihilator step. Neither restates Gabber's target or duplicates an existing
   declaration. Verdict: pass.

4. Read the proof from the target downward: filtered representative, bounded lift,
   injective annihilator, torsion and acyclicity, then pushout and naturality. The route
   keeps the affine-comparison unit and removes only unused direct proof imports and
   dependencies listed above. The finite-cover theorem is retired with a concrete
   counterexample rather than weakened. Verdict: pass.

5. Checked the changed DAG nodes, new-node fields, proof/dependency unions, and the
   change record. The active effacement attachment records the narrower Lean theorem
   actually proved, while the stronger blueprint statement remains open. Verdict: pass.

Changes made during this reading: added this required current second-reading section;
no Lean code, signatures, definitions, nodes, or proof routes were changed.
