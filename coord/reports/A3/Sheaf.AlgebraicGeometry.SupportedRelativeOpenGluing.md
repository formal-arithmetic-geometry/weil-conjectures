## What changed

Completed `AlgebraicGeometry.Scheme.exists_supported_relative_open_gluing` without
changing its signature, visibility or docstring. Added the proof-only import
`Sheaf.AlgebraicGeometry.RelativeOpenGluing`, whose single theorem isolates the
underlying derived gluing and map construction (step 1 of the original node).
The core module also directly imports `Sheaf.AlgebraicGeometry.DerivedOpenLocalization`
for the fixed-universe localization theorem used in its remaining proof plan.
Added proof-only imports of `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
and `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` for the derived
homology comparisons and exactness of restriction along open immersions.

The local conclusions are proved, not postponed: `local_perfect_of_open_immersion`
transports a strictly perfect model through the isomorphism onto its open image,
checks degree bounds and finite-free retracts termwise, and constructs its derived
restriction comparison. `overlapRestrictionIso` compares the relative restriction
with restriction along `X.homOfLE`. `stalk_subsingleton_of_open_immersion` composes
exact homology comparison and the restriction stalk isomorphism. The theorem
chooses a covering member at each point and combines these facts with the gluing
map equations. All private helpers are proved and are used only in proofs.

The new theorem `exists_relative_open_gluing` has neither perfectness/support
hypotheses nor perfectness/support conclusions. It is strictly the first step,
not the supported statement with hypotheses repackaged. Its docstring and node
record the remaining transport to the existing `derived_open_gluing` theorem.
Read the source `cohomology.tex`, `lemma-glue` (Tag 08DG), retrieved into the
sandbox scratchpad, and Definition 08CM. The unit route is unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_supported_relative_open_gluing`
(node `lem-sc-supported-relative-open-gluing`). There are no remaining sorries
in the item's module or its private helper declarations.

Added one hole:
`AlgebraicGeometry.Scheme.exists_relative_open_gluing`
in `Sheaf.AlgebraicGeometry.RelativeOpenGluing`
(node `lem-sc-relative-open-gluing`). Its proof is exactly `:= by sorry`.
This is a decomposition: one upper hole closed, one lower hole added, net zero
holes removed. Perfectness and support are fully checked by the combining proof.
No definitions contain sorry, and no arbitrary witnesses from the new theorem
are used in definitions: its existential witnesses are eliminated in the proof.

Single-file compilation and compilation of the two modules in import order pass.

## No longer needed

No global node or module is pruned. The original direct proof imports
`Sheaf.AlgebraicGeometry.DerivedOpenGluing` and
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction` move to the new core
gluing module, where they remain dependencies of the stated remaining argument.
They are removed from the supported module itself. The supported node now uses
`lem-sc-relative-open-gluing` and `def-pc-perfect-complex`; its former gluing and
localization dependencies remain reachable through the new node.
The two public imports of the supported module are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt was a copy of the original unproved module, without
a report or partial proof. The original DAG's pointwise perfectness/support step
is correct, but needs explicit transport between relative restriction and the
open immersion, and between the two localized module sites. Those steps are now
proved in Lean. `Scheme.Modules` has a separately synthesized category structure;
the private typed restriction abbreviation and its exactness/additivity instances
ensure all derived functors use the project's shared `SheafOfModules` localization.
No existing statement, definition or target was changed, and no adaptations are needed.

Edge cases: the new gluing claim imposes no unsupported boundedness or
quasi-coherence condition, in agreement with Tag 08DG. When a cover member is
empty, the pointwise proof selects the other; when the union is empty both
perfectness and support are vacuous. Repeated or nested opens cause no extra
condition. An arbitrary, possibly nonclosed or empty subset T is handled solely
by the given pointwise nonmembership hypotheses. The formal proof uses no
compactness or closedness. Search of the blueprint for 08DG and glue complexes
found no imported blueprint match; library search found the existing cover-based
`derived_open_gluing`, but no relative-union theorem with this interface.

## New nodes

`lem-sc-relative-open-gluing`, in
`dag/nodes/sec-picard-framework/lem-sc-relative-open-gluing.json`, isolates the
unrestricted object/morphism gluing on W union V from the supported theorem.
It inherits the chapter and unit, cites Tag 08DG (`cohomology.tex`, `lemma-glue`),
and uses the existing gluing and localization nodes. LeanFinder, Loogle, Mathlib
source grep and the unavailable LeanSearch request are recorded from actual
searches. The new module is `lean/Sheaf/AlgebraicGeometry/RelativeOpenGluing.lean`.
There are no change records because no existing interface changed.

## Second reading by A3

1. Compared the supported module with the repository version and checked the existing
   declaration's docstring and complete signature by exact string equality. They are
   byte-for-byte unchanged. Its two public imports remain unchanged; the three added
   helpers and typed restriction abbreviation are private and occur only in proofs.
   The only new public statement is the reported core gluing theorem. No definitions,
   target statements or signatures of existing declarations changed. Verdict: pass.

2. Compiled both delivered modules in dependency order and a scratch copy printing
   axioms of all three mathematical helpers and both gluing theorems. The helpers use
   only propext, Classical.choice and Quot.sound. The supported theorem additionally
   uses sorryAx through exists_relative_open_gluing, as reported. The sole sorry in
   the delivered sources is exactly the named core theorem's proof. No prohibited
   declarations or hollow definitions occur; its existential witnesses are eliminated
   inside the theorem proof and never used to define arbitrary data. The termwise
   model transport preserves degree bounds and sends the finite-free retract equation
   to a retract of the transported free module using sigmaComparison and the unit
   isomorphism. The derived comparison has the required direction. The homology/stalk
   additive equivalence transports Subsingleton in the required direction. Verdict: pass.

3. Read cohomology.tex, lemma-glue (Tag 08DG), including its object construction and
   Mayer-Vietoris map-lifting conclusion, and definition-strictly-perfect and
   definition-perfect (Tags 08C4 and 08CM). Matched A, B, c, E, a, b and the overlap
   equation to the core theorem: the target there is E restricted to Y, and all
   comparisons are the canonical ambient restriction comparisons. No boundedness,
   affineness or support assumptions enter that first step. The core theorem omits
   every perfectness/support hypothesis and conclusion and is strictly a part of
   the original argument; the remaining local conclusions are actually proved.
   Empty W, empty V, empty Y, W=V, nested opens and arbitrary empty/nonclosed T
   require no extra hypothesis. Searched independently with LeanFinder for descent
   of derived objects and morphisms on open covers, and Loogle for restrictFunctorComp;
   found ordinary sheaf gluing and restriction comparisons, no matching derived
   relative gluing theorem. Searched lean/Sheaf, lean/WeilConjectures and the upstream
   WeilConjectures source for derived gluing and local perfectness; the covering
   derived_open_gluing is the relevant existing theorem, but requires transport
   between ambient-relative restrictions and the pulled-back opens of Y. No short
   direct application closes that remaining transport. Verdict: valid decomposition,
   not a completed axiom-free proof; one hole closed and one added, net zero.

4. Read derived_open_gluing and open_derived_localization_adjunction against the
   new theorem's proof plan. The former supplies both the transition identification
   and the compatible map; the latter supplies open-scheme localizations once the
   localized-site family is available. The model and stalk helpers use existing
   exact restriction, module equivalence and derived comparison declarations.
   The supported module no longer imports the covering gluing or localization
   adjunction directly; both remain reachable through the core theorem. Neither
   former proof dependency is globally pruned. Read dag/units/sk-thm-picard-duality.json:
   its realized record has no assigned statement or step nodes, and is unchanged.
   The route still uses derived_open_gluing and the local Definition 08CM argument,
   exactly as the original node did. Verdict: pass; no global pruning claimed.

5. Compared the existing node diff: only proof, proof_deps and proof_origin changed.
   Its three steps match the core theorem application, neighbourhood-model transport,
   and homology-stalk transport in the actual Lean proof. Checked the new node's
   statement against its verbatim Lean signature, source, proof steps, dependency
   union, search records, created/blueprint/chapter/unit and lean fields. Found that
   the new proof plan explicitly uses nonempty_derivedOpenLocalization, but its
   module and node were only transitively present via a proof-only import of the
   adjunction module. Added its direct proof-only import and added
   lem-pc-derived-open-localization-universe to step 1 and proof_deps of the new node.
   This supplies the localized-site family before invoking the adjunction result.
   Verdict: pass after that repair.

Second reading changed only the missing direct proof-plan import/dependency and this
report. No mathematical proof, existing interface or existing docstring was rewritten.
