## What changed

Proved `AlgebraicGeometry.Etale.projectiveLine_strictLocal_modelComparison` without changing its signature or existing docstring. Its proof chooses an algebraic closure of k', obtains compatible strict henselizations and residue maps, restricts F along the resulting structural morphism, obtains the torsion instance from the existing inverse-image instance, and combines the stalk and cohomology comparisons for that same model.

Added three modules:

- `Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues`: the purely geometric construction, with explicit isomorphisms to the canonical strict-henselization schemes.
- `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison`: comparison only of the two stalk exchanges for a fixed compatible geometric model.
- `Sheaf.AlgebraicGeometry.ProjectiveLineResidueCohomologyComparison`: a proved residue-cohomology comparison. The proof base-changes the universal homeomorphisms, constructs the coefficient isomorphism from `pullback_forget_modules_iso`, and constructs the target isomorphism from that chosen source isomorphism. Naturality and composition of cohomology pullback then prove the equation by cancellation of the inverse-image composition isomorphisms. No coherence assertion about an arbitrary chosen forgetful isomorphism is assumed.

The original module adds four proof-only imports, including the algebraic closure module. Its two public imports are unchanged. The residue module imports only projective space and topological invariance for its public interface; the stalk module uses the base-change definitions (which publicly supply torsion sheaves), without importing strict-local closed-fibre exchange.

## Proved and sorry left

Proved the original one of one sorries:
`AlgebraicGeometry.Etale.projectiveLine_strictLocal_modelComparison`
(node `lem-weil-pbc-p1-strict-local-model-comparison`). No sorry remains in the assigned module.

Also proved:
`AlgebraicGeometry.Etale.projectiveLine_residueCohomologyComparison`
(node `lem-weil-pbc-p1-residue-cohomology-comparison`), together with its private helpers `cohomologyMap_comp_explicit` and `cohomology_square_equivalences`.

Exactly two new sorries remain, each the whole proof of a named public theorem with a source, full natural-language proof, and node:

- `AlgebraicGeometry.Etale.projectiveLine_compatibleStrictHenselizationResidues`
  (`lem-weil-pbc-p1-compatible-strict-henselization-residues`). This asks only for rings, maps, and geometric commutativities. It has no sheaf or cohomology conclusion.
- `AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison`
  (`lem-weil-pbc-p1-strict-local-stalk-exchange-comparison`). This fixes the geometric model and asks only for the two stalk equivalences and exchange equation. It has no residue cohomology conclusion.

The target proof is a reduction through these two independent remaining results, plus the proved residue comparison. It does not establish the entire transitive axiom closure yet.

## No longer needed

None of the original mathematical proof dependencies is eliminated. Strict-henselization functoriality, the stalk formula and termwise exchange are now the stated proof dependencies of the two remaining intermediates; topological invariance and cohomology functoriality are actually used by the proved residue comparison. They are not claimed pruned merely because the assigned module does not import them directly.

No original import is removed. All added proof imports are used. The redundant direct public import of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf` was removed from the new stalk module; `SmoothBaseChange.Defs` already publicly imports it. Its declarations remain needed, so this removes no mathematical node or reachable module. The new statements and the residue proof do not use strict-local closed-fibre exchange, strict-henselian projective-line cohomology comparison, proper base change, or field-extension cohomology invariance. The blueprint unit `sk-thm-p1` and all its realized steps remain unchanged.

For completeness, all five old direct `proof_deps` are replaced on the assigned node:
`lem-weil-pbc-strict-henselization-functoriality`,
`prop-weil-pbc-strict-henselization-stalk-formula`,
`lem-weil-pbc-derived-exchange-termwise`,
`prop-weil-pbc-universal-homeomorphism-topos`, and
`lem-weil-pbc-cohomology-pullback-functorial`.
The first three remain dependencies of the geometric/stalk intermediates; the last
two remain dependencies of the residue comparison. None is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The existing plan describes the mathematics, but its declarations do not directly have the signatures needed for these two simultaneous compatibility equations. In particular, the stalk formula is stated for abelian coefficients and algebraically closed points; the assigned theorem uses module coefficients at universe u+1 and possibly nonperfect separably closed fields. The existing injective-module abelian-acyclicity theorem uses a ring in Type u and a SheafOfModules encoding; it does not directly supply the coefficient-universe bridge required here. That bridge and comparison of the derived exchanges remain explicit tasks inside the stalk intermediate. The docstring and node do not treat preservation of injectives by forgetting coefficients as an input.

The geometric intermediate includes the integral factorizations: they are needed to make k and k' purely inseparable over the strict-henselization residue fields, hence to make the residue maps universal homeomorphisms. The algebraic closure used for the common pointing need not be algebraic over k when k'/k is transcendental; the proof uses splitting of separable polynomials in k instead of assuming such algebraicity.

Edge cases checked against the statements: degree zero uses section restriction; zero sheaves give zero groups; arbitrary X' is transported by the pullback universal property; nonperfect separably closed fields retain their possibly nontrivial purely inseparable residue extensions; extensions k'/k may be transcendental. The proved residue comparison requires neither torsion nor separable closedness, and uses only the stated universal-homeomorphism hypotheses. Dependency checks found no cycle through any new node.

## New nodes

`lem-weil-pbc-p1-compatible-strict-henselization-residues`: the geometric part of the original node's first step, independently of Λ,F,q. It records the canonical strict-henselization models and both pointed residue squares.

`lem-weil-pbc-p1-strict-local-stalk-exchange-comparison`: the original node's second step for a fixed model. Its two equivalences have only stalks as targets. The proof must establish compatibility by the termwise neighbourhood restriction maps, independently of closed-fibre comparison.

`lem-weil-pbc-p1-residue-cohomology-comparison`: the original third step, now proved. Its generality excludes the torsion, strict-henselian and geometric-stalk hypotheses because the argument needs only local residue maps, universal homeomorphisms, coefficient isomorphisms, and functoriality.

Interface-addition record: `coord/changes/ProjectiveLineStrictLocalModelComparisonReduction.md`. There is no change to an existing definition or statement and no existing downstream module needs adaptation.


## Second reading by Q1

1. Compared the assigned module with the repository using `diff -u`: the existing
   declaration's signature and docstring are byte-for-byte unchanged. Only its proof
   and four plain proof imports were added. No existing definition changes. The
   existing node differs only in `proof`, `proof_deps`, and `proof_origin`. The three
   added interfaces are declared in the change record. Verdict: pass.
2. Compiled all four modules in dependency order using `lcompile.py --all`, without
   errors or warnings. Searched the delivered Lean for forbidden declarations and
   hollow definitions: none. Exactly two occurrences of `sorry` remain, the complete
   proofs of the two reported public intermediate theorems. Scratch copies with
   `#print axioms` checked the original theorem, all three new public theorems, and
   both private residue helpers: only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The proved residue comparison still has upstream open dependencies;
   a proved body here does not mean its transitive axiom closure is closed. Verdict: pass.
3. Read both split statements and their full docstring arguments. The geometric
   statement contains no cohomology; the stalk statement fixes the geometric model
   and has no residue-cohomology conclusion. Neither restates the assigned item.
   Checked field bases, degree zero, zero coefficients/sheaves, nonperfect separably
   closed fields, nonalgebraic k'/k, and arbitrary presentations of the pullback X'.
   Integral point factorizations are used only for the purely inseparable residue
   maps; extending points to an algebraically closed field uses splitting of finite
   separable polynomials, not algebraicity over k. Independent `msearch.py` searches
   used "etale neighbourhood cohomology filtered colimit higher direct image stalk
   strict localization", henselian/residue-map variants, and a Loogle field-extension
   query; they found no existing complete comparison. Also searched the two source
   roots and read the strict-henselization residue/functoriality and stalk-formula
   interfaces. Those provide components, not these simultaneous conclusions; the
   coefficient bridge remains explicitly open. Neither split can be closed in a
   short routine argument with these interfaces. Verdict: pass.
4. Read the top-level reduction and the residue proof from their conclusions down.
   The same F0 and geometric model supply both equations. The residue proof reduces
   to topological invariance, inverse-image composition, forgetful comparison, and
   functoriality; no additional coherence for arbitrary chosen coefficient isos is
   required. All proof imports are used. Removed the redundant torsion-sheaf import
   from the new stalk module, as `SmoothBaseChange.Defs` publicly supplies it. The
   report now enumerates all five replaced original direct dependencies and explains
   why each remains needed transitively. Read `dag/units/sk-thm-p1.json`: its realized
   nodes and steps are unchanged, and this reduction bypasses none of them. Verdict: pass.
5. Matched each node's Lean declaration and statement, proof steps, dependency union,
   origin, source, and new-node metadata. The assigned node's new dependency list
   follows its actual calls; the two open intermediates retain their mathematical
   proof plans. Corrected the residue node's reversed notation for composite inverse
   image: c1 has target v* f*, and c2 has target g* u*, exactly as the Lean code uses.
   Verdict: pass after this prose correction.

Second reading changed the redundant new-module import, composite-pullback notation
in the residue node, and report completeness. No Lean statement or proof body changed.
