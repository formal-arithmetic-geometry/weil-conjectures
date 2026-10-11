## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`
with a compiled proof of the geometric reduction. It establishes compactness,
quasi-separatedness, the closed immersion, and its image as the inverse image of V(I).
For every finite cover, the proper composite satisfies the existing Stein connectedness
statement. It then applies a new general finite-cover connectedness criterion for
module-valued etale sections.

Added `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion` with that criterion,
a source and a complete natural-language proof. Added three private proof imports to
DegreeZero: this new module, HenselianConnectedness, and Mathlib PullbackCarrier.
Existing signatures, public imports, definitions, and the geometric-fibre assembly
are unchanged. The node copy records exactly this new reduction.

Both files compiled locally without warnings. LeanSearch was unavailable (HTTP internal
server error), recorded by msearch; LeanFinder, Loogle, Mathlib grep, and source-library
searches found no existing compatible theorem. The Stacks statements and proofs were
read online at Tags 09ZG and 09ZF; the latter's finite-cover criterion is the source of
our new criterion. No literal source passages were copied.

## Proved and sorry left

The original module now has no direct sorry:
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`
(node `lemma-weil-pbc-etale-degree-zero`) is proved from the new criterion and the existing
Stein connectedness statement. This is a partial delivery: its transitive proof still
uses sorry-bearing dependencies, including the existing Stein connectedness input.

One new direct sorry remains:
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections`
in `Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion`, node
`lem-weil-pbc-etale-module-h0-finite-connected-criterion`. Its proof is exactly `by sorry`.
The next worker must supply the spectral/Gabber argument and module-forgetful comparison.
No other direct sorry is delivered.

Edge cases of the new statement: for empty X all global module sections are zero; for
identity i the restriction is an isomorphism; for empty Z and nonempty X the hypothesis
fails already for h=id and the closure of any point, since IsConnected includes
nonemptiness; for a nilpotent thickening the image is all of X and the conclusion agrees
with topological invariance. No restriction on the characteristic or the coefficient
ring was introduced.

## No longer needed

No existing import was removed; the added imports are all used. No node realizing the
unit's statement or its steps is bypassed: the degree-zero step still uses Stein
connectedness followed by spectral restriction and Gabber's finite-cover argument.

The reduction no longer needs `lem-weil-pbc-zariski-h0-proper-henselian-pair`, module
`Sheaf.Paper.ZariskiH0ProperHenselianPair`: it supplies connectedness on all finite
covers directly. The general spectral and Gabber inputs remain dependencies of the
new criterion, so `Sheaf.Topology.SpectralClosedRestriction` and
`Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion` are not claimed globally pruned.

The corrected node records the direct geometric dependencies used by the proof:
`def-weil-pbc-scheme-conventions`, `lem-weil-pbc-qcqs-over-affine`,
`def-weil-closed-immersion`, `lem-weil-pbc-closed-immersion-base-change`, and
`lem-weil-pbc-fibre-product-points`, together with
`lem-weil-pbc-finite-morphism-permanence` for properness of the finite composite.
The former claim that these geometric dependencies were removed was incorrect and has
been corrected. The finite-pullback identities and inverse-image definition remain
unneeded direct proof edges. In particular,
`WeilConjectures.SixFunctors.BaseChange.GlobalSections` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` remain imported in the unchanged
public API; neither is claimed globally unnecessary. The finite-pullback identities
are not an extra obligation of this Lean theorem, which asserts only IsIso for a
fixed F and fixed pullback square.

## Where the brief, the DAG or earlier work was wrong

The planned Zariski/Gabber route has a formal interface mismatch:
`zariski_h0_proper_henselian_pair` uses Type u, while
`gabber_h0_etale_criterion` requires Type (u+1), and our theorem uses
ModuleCat.{u+1} Lambda. The existing spectral restriction declaration also uses
Type u. They cannot simply be applied to the module sheaf in DegreeZero.
The new criterion makes the universe and coefficient comparison part of one explicit
remaining obligation, without changing those existing statements or weakening this item.
The new docstring explicitly calls out the value-universe issue.

Stacks Tag 09ZG is currently Lemma 59.82.4, not Lemma 59.82.1 as the earlier spectral
statement's docstring says; the tag and its mathematical assertion are the intended ones.

## New nodes

`lem-weil-pbc-etale-module-h0-finite-connected-criterion` states the general geometric
criterion independently of henselian rings and proper morphisms. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleH0FiniteConnectedCriterion.lean`.
The DAG's existing set-valued Gabber criterion and spectral criterion are retained as
proof ingredients; this node packages their application and the required module and
universe comparisons. No definition, target statement, or existing interface changed,
so no change record or user adaptation is needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered DegreeZero module with the repository version. The theorem and definition signatures are byte-for-byte unchanged; only the proof and proof-only imports differ. The added criterion module and node are the declared split-off work.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The original target theorem has no direct `sorry`. The criterion theorem is the one explicitly listed split-off `sorry`; no axioms, unsafe declarations, or hollow definitions were added.

3. Checked the split-off criterion statement and its edge cases against the source and existing declarations. It is a genuine general finite-cover criterion, stronger in scope than the item-specific theorem and not a restatement. Searches and repository grep found no duplicate declaration.

4. Read the proof top-down. The target uses the finite-cover criterion and the existing Stein connectedness theorem, with the range/preimage calculation shown in Lean. The criterion's unresolved universe/module comparison is isolated in its named theorem and documented. The imports added to DegreeZero are used; no old import can be pruned from the delivered files.

5. Updated the target node's `proof`, `proof_deps`, and `proof_origin` to match the compiled proof. The unit route remains through Stein connectedness and the finite-cover criterion. The old Zariski/Gabber and finite-pullback edges are no longer direct dependencies and are pruned from the node.

Changed the target DAG node metadata only; no Lean statement or definition was changed. The dry-run delivery checks are the remaining verification step.

## Second reading by J1

1. Compared the delivered `DegreeZero.lean` against the repository copy. The existing definition and theorem signatures are byte-for-byte unchanged; only the theorem proof and proof-only imports differ. The added criterion module and DAG node are explicitly declared in the report, so no accidental public statement change was found.

2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The target theorem has no direct `sorry`. The only delivered `sorry` is the named criterion theorem, and it has a dedicated docstring, DAG node, and report entry. No forbidden declarations or hollow definitions were found.

3. Reviewed the split-off criterion. Its hypotheses and conclusion are mathematically meaningful and stronger in scope than the item-specific theorem, with edge cases recorded in the report. Repository and Mathlib searches found no duplicate declaration. The unresolved universe and module-structure argument is isolated in this named theorem rather than hidden in a partial proof.

4. Read the proof top-down. The target establishes compactness, quasi-separatedness, the closed immersion and range formula, then invokes Stein connectedness for every finite cover and the criterion. The criterion's module and universe comparison is the sole open obligation. Imports added to the target are used; no removable prior import was identified. The unit route through finite-cover connectedness remains represented.

5. Updated metadata agrees with the Lean proof: the target node lists the geometric, Stein, finite-morphism, and criterion dependencies actually used, while obsolete Zariski and finite-pullback edges are pruned. The criterion node records its source, statement, proof plan, Lean declaration, and split status. No target statement or definition changed.

Changes made during this second reading: none; the delivered files already passed compilation and the metadata matched the proof.
