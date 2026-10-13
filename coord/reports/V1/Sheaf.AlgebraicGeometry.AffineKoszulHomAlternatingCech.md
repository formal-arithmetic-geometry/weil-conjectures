## What changed

Proved the unchanged signature of
`AlgebraicGeometry.affineKoszulHomAlternatingCech` from two strictly smaller graded
statements. This is a decomposition, not a sorry-free proof of the mathematical
comparison. The new modules are
`Sheaf.AlgebraicGeometry.KoszulHomDegreePowerDiagram` and
`Sheaf.AlgebraicGeometry.FiniteLocalizationPowerColimit`.

The first constructs the actual additive Hom power diagram by precomposition
with the already constructed exterior-power Koszul transitions. All construction
and differential-commutation proofs are complete: `additiveHomPrecomp`,
`shiftedKoszul_eq_openTail`, and `koszulAdditiveHomPowerDiagram`. No data are
chosen from an unproved existence theorem. Its remaining statement identifies
one evaluated diagram with a finite family of coordinate multiplication systems.
The second defines that coordinate diagram explicitly and leaves only the general
finite-family localization colimit statement.

The main proof composes the natural diagram isomorphism, Mathlib's evaluation
colimit isomorphism, and the localization colimit isomorphism. It takes the
colimit itself as T and the identity as Φ; the existing signature allows this.
The existential binder `eIso` is unused in the statement's body. The now completed
proof triggers its unused-variable linter, so that linter is disabled locally for
this theorem without changing its signature or existing docstring.

The resumed worker checked the existing attempt against the unchanged signatures,
its dependency interfaces, and the unit realization record. Compilation through
`lcompile.py --all` passed for all three modules. The `deliver3.py --no-push`
dry run printed OK, with only the independent second reading pending; nothing
was pushed.
The source read was the Stacks perfect.tex section Koszul complexes, especially
`equation-system`, `lemma-alternating-cech-complex`, and the subsequent paragraph
on total Hom complexes; also algebra.tex's module localization universal property.
Source copies used for reading are scratchpad files and are not delivered.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.affineKoszulHomAlternatingCech`
(node `lem-sc-affine-koszul-hom-alternating-cech`). No sorry remains in the item.

Added two holes, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.koszulHomDegreePowerDiagram`
  (node `lem-sc-koszul-hom-degree-power-diagram`): the exterior-basis natural
  isomorphism for one total degree, without localization or a complex comparison.
- `AlgebraicGeometry.finiteLocalizationPowerColimit`
  (node `lem-sc-finite-localization-power-colimit`): localization of a finite
  coordinate multiplication system, without Koszul complexes or differentials.

Thus one hole is decomposed into two: holes closed 1, holes added 2, net -1.
The new lemmas are true for r=0, r=1, empty coordinate families, zero modules,
f_i=0, units f_i, and the zero ring. Finiteness of the tuple families is supplied
by Lean's finite function and subtype instances. Multiplication is pointwise,
including when the coordinate multipliers differ.

Existing `ModuleCat.localization_away_colimit` remains an unproved dependency of
its new finite-family successor item; it is not changed or added by this delivery.
No claim is made that the import closure is sorry-free.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.HomComplex`: its sheaf-valued Hom construction is not
  the additive Mathlib Hom complex appearing in the actual statement.
- `Sheaf.AlgebraicGeometry.AlternatingCechComputes`: no ordered/full Čech
  cohomology comparison is needed for the graded existential signature.
- `Sheaf.Paper.KoszulComplex`: its definitions remain available through the
  public shifted-Koszul import; the direct proof import is redundant.
- `Sheaf.RingTheory.ModuleLocalizationFilteredColimit`: retained as the planned
  proof dependency of the new finite-family module, so it is not globally pruned.

The original proof dependency `lem-pc-alternating-cech-computes` and its module
are not needed by this proof. The original `def-pur-hom-complex` proof branch
through `Sheaf.Algebra.Homology.HomComplex` is also unused: Mathlib's additive
HomComplex is already publicly imported. The Koszul-complex definitions and
single-module localization theorem remain needed transitively. No statement
realizing the blueprint unit's statement or steps is bypassed: its realized
statement and step lists are empty in dag/units/sk-thm-picard-duality.json.

The informal node's sign/differential step is not needed to prove this Lean
signature; that does not establish the stronger informal comparison.

## Where the brief, the DAG or earlier work was wrong

The existing theorem is materially weaker than its docstring and informal node.
It asserts only existence of D with specified objects, T with specified graded
terms, and an unspecified isomorphism colimit D -> T. It does not specify D's
transition maps, the differential of T, or the signed fraction formula for Φ.
This delivery voluntarily constructs the intended transitions, but the other
two properties still are not assertions of the signature. Therefore choosing
T=colimit D and Φ=identity is legal and removes the differential/sign step.
The docstring's claim that an objectwise clause fixes the totalization or that
the statement prescribes signs/fractions is incorrect. Neither the signature,
the docstring, nor the informal statement was changed; this semantic discrepancy
needs a separate interface review. Downstream work requiring the canonical
comparison cannot obtain its formula from this existential theorem.

The proof dependencies originally listed are insufficient as usable interfaces:
KoszulComplex defines the complex but does not expose the Hom degree basis
comparison; AlternatingCechComputes is a scheme-cover cohomology comparison,
not a localization double-complex construction; and the single-module
localization theorem does not itself state the finite-family additive colimit
identification. The two new graded lemmas fill exactly these gaps.

## New nodes

`lem-sc-koszul-hom-degree-power-diagram` is the one-degree exterior-basis and
transition identification, with an explicitly constructed sequential Hom diagram.
It uses the existing Koszul power transition construction, not a new existence
witness. Its source is Stacks perfect.tex's Koszul system and Tag 0911 basis
calculation, applied degreewise to the subsequent total Hom paragraph.

`lem-sc-finite-localization-power-colimit` is a general finite-family localization
colimit assertion. It uses the existing single-module localization-colimit lemma
and the common-stage finite-coordinate argument. Its proof in words includes
both representative and equality synchronization and the empty cases.

The original node's proof, proof_deps, and proof_origin are updated to the actual
Lean reduction. No existing definition, declaration signature, or visibility is
changed; no forced adaptations or change records are needed.

## Second reading by V1

1. Diffed each delivered module against the repository. The existing theorem's
   signature and docstring are byte-for-byte unchanged; only its proof, plain
   proof imports and local unused-variable linter option differ. The other two
   modules are new. No existing definition or public import changed. Verdict:
   interface preservation passes. The original formal signature is weaker than
   the informal comparison, as explicitly reported above; no stronger comparison
   is claimed by this reading.
2. Independently ran lcompile.py --all: all three files compile without warnings
   or errors. Compiled a scratch copy with #print axioms for all eight delivered
   declarations. The five constructions/helpers use only propext,
   Classical.choice and Quot.sound; the main theorem and two new theorems also
   use sorryAx as expected. Source scanning found exactly the two reported
   whole-theorem sorries and no forbidden declarations. The Hom diagram is an
   explicit construction. Classical.choice of the graded isomorphisms is an
   existential proof witness, not arbitrary data in a public definition.
   Verdict: valid reduction, with the two named obligations outstanding.
3. Read perfect.tex equation-system, lemma-alternating-cech-complex and its
   following total-Hom paragraph, and Mathlib's HomComplex Triplet convention
   p+n=q. Source degree -p contributes M^(n-p), on wedges of length p+1;
   precomposition multiplies by the product of the corresponding f_i. For r=2
   the terms are two copies of M^n and one M^(n-1), with multipliers f_0, f_1
   and f_0*f_1. For r=0 the positive exterior powers and target vanish; for r=1
   only M^n survives. Finite-family localization follows by synchronizing
   finitely many representatives and equality witnesses at their maximum stage.
   Empty families give zero groups; zero multipliers give zero colimits and
   localizations; unit multipliers give the original modules. Zero modules and
   the zero ring cause no exceptions. Both new lemmas have complete word proofs
   and matching nodes and are strictly smaller than the original comparison.
   Independently ran LeanFinder, Loogle and grep searches using exterior-basis,
   sequential-colimit and power-map terminology. Results included
   exteriorPower.map and AddCommGrpCat.FilteredColimits.colimit APIs, but no
   exact result. Searched lean/ and upstream WeilConjectures: the existing
   scheme-valued KoszulCechComparisonConstruction and finite-stage lifting/kernel
   lemmas do not supply either additive degree-diagram identification or the
   finite-family localization colimit. Neither hole closes in a few minutes
   from these interfaces. Verdict: true, necessary decomposition, not relabeling.
4. Checked the top-down proof: explicit diagram, degreewise natural isomorphism,
   evaluation preserving colimits, localization colimit, then identity to the
   colimit itself. The new modules' public imports supply public statement or
   definition dependencies; proof-only imports are plain. The pruning report
   accounts for all four old proof dependencies: Koszul definitions and the
   single-module localization theorem remain transitively needed; the sheaf Hom
   and alternating Cech comparison branches are unused. The unit record has
   realized.statement=[] and realized.steps=[[]], so no realized unit step is
   bypassed. Verdict: route and pruning pass. One hole closes and two are added,
   net -1; this remains a decomposition, not a finished mathematical comparison.
5. Read all three node files. The original proof and proof_deps describe the
   actual construction, graded-colimit reduction and identity comparison. The
   two new nodes match the finite hypotheses, degree indices and successor maps
   of their Lean statements and include their word proofs, sources, search
   records, creation metadata, blueprint ancestry, unit/chapter and verbatim
   Lean statement bodies. Their proof dependencies are exactly the shifted
   Koszul/open system/Koszul definitions and the single-module localization
   theorem used by their plans. Verdict: nodes agree with the Lean reduction;
   the original informal statement's stronger content remains separately flagged.

No Lean or node repair was necessary. The second reading changed only this
report, adding the independent review, source, edge-case, search, compilation
and axiom evidence.
