## What changed

The original theorem
`AlgebraicGeometry.Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension`
is now proved with its exact original signature. The proof identifies the injective
coefficient object with a module over the constant ring sheaf, applies the already
proved injective-module higher-direct-image acyclicity theorem, and uses a relative
field-extension exchange isomorphism. Exact sections on the separably closed Spec K,
derived Leray, and the Sheaf.H/derived comparison give the requested subsingleton.
The module-forgetting inverse-image comparison supplies the precise target sheaf.

Four new modules contain complete proofs:
`FieldExtensionHigherDirectImageExchange`, `FieldExtensionDerivedDirectImageExchange`,
`SmoothLimitDerivedDirectImageExchange`, and `LimitDerivedDirectImageExchange`.
The first takes homology of the derived comparison. The second uses perfectness of
the algebraically closed base, the actual filtered diagram of finitely generated
smooth subalgebras, and its actual Spec limit cone. No purely inseparable reduction
is needed. The third uses the proved module-coefficient smooth base-change theorem
and canonical module/abelian exchange compatibility. The fourth assembles degreewise
continuity, proves negative-degree vanishing on both sides, and explicitly transports
from bounded-below to total derived categories and degree-zero single complexes.

`LimitHigherDirectImageExchange` contains the sole remaining hole, for one
nonnegative-degree canonical exchange under affine inverse limits. It is a strictly
geometric part of the argument, rather than another form of injective acyclicity:
it has no n, no torsion, no injectivity, no algebraic-closure hypothesis, and no
extension field K. It states the fixed-degree conclusion of Stacks 0EZT/0EYM.

To remove an import cycle, the existing proved smooth-curve invariance declaration is
moved verbatim into `Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension` (apart from
its explanatory docstring). The original source `SmoothBaseChange.AlgClosedExtension`
publicly reexports it. `SmoothBaseChange.Vanishing` replaces its public import of the
general invariance file with the independent curve module. Both existing files are
unclaimed in the local claim snapshot and are freely adapted under the human's
2026-10-12 instructions. No existing mathematical statement or definition changes;
Vanishing's proofs are unchanged. The curve node's Lean attachment follows the move.
The unit's own curve input and its proof route remain intact.

All nine delivered Lean modules compile together through lcompile.py; each single
file takes under 60 seconds (the slowest is Vanishing, approximately 22 seconds).
The delivered modules have lines of at most 100 characters. The import graph is
acyclic. No axiom, unsafe declaration, opaque declaration, or hollow definition is
added. New statement edge cases are included in their docstrings: q=0, n=1, exclusion
of n=0, zero coefficients, empty source, and nonempty cofiltered index. K in the new
field-exchange lemmas need not be algebraically closed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension`
(node `lem-sc-algclosed-extension-injective-acyclic`). There is no sorry in the item's
module, including its private exact-global-sections/Leray helper.

Fully proved new public declarations:

- `AlgebraicGeometry.Etale.nonempty_fieldExtension_higherDirectImage_iso`.
- `AlgebraicGeometry.Etale.nonempty_fieldExtension_derivedDirectImage_single_iso`.
- `AlgebraicGeometry.Etale.nonempty_smoothLimit_derivedDirectImage_single_iso`.
- `AlgebraicGeometry.Etale.nonempty_limit_derivedDirectImage_single_iso`.

The private smooth-stage module-to-abelian exchange helper is also proved. The
relocated `AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension`
keeps its existing complete proof. Neither adapted existing module adds a hole.

Added one remaining hole:
`AlgebraicGeometry.Etale.isIso_limit_homology_derivedBaseChangeMapPlus`, in
`Sheaf.AlgebraicGeometry.LimitHigherDirectImageExchange`, node
`lem-sc-limit-higher-direct-image-exchange`. This is the only sorry in the delivered
Lean files. Overall this delivery is a decomposition: one upper hole closed and
one lower hole added, before the ledger accounts for already existing holes in the
new proof-dependency import closure. It is not claimed as an axiom-free final proof.

The remaining theorem still needs the varying-base continuity comparison of
Stacks 0EYM and its compatibility with the canonical base-change map (0EZT).
The source docstring and node give the complete argument. The useful proved library
ingredients are `AbelianHigherDirectImagePresheaf`,
`EtaleCohomologyLimitOfSchemes`, `AffineEtaleSiteColimit`,
`AffineEtaleBaseChangeGeometry`, `LimitFibreProducts`, and directed reindexing.
`CofilteredFixedBaseCohomologyContinuity` handles the supplied cohomology cocone for
arbitrary cofiltered systems, but does not itself build the varying-base higher-image
comparison. `HigherDirectImageLimitSystem` fixes the target scheme S, so it cannot
be applied directly to the displayed varying-base exchange. The remaining work is
to construct the descended affine-etale pullback systems and their coefficient and
cohomology diagrams/cocones, prove their canonical comparison equations, apply
cohomology continuity, and identify the sheafified result with the homology of
`derivedBaseChangeMapPlus` via its resolution formula. Negative-degree vanishing,
Plus/total compatibility, smooth-stage exchange, and the field-extension diagram
are all already closed in this session and must not be split off again.

## No longer needed

Removed direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology`: the source vanishing is
  obtained directly from `InjectiveModuleDirectImageAcyclic`; the node
  `new-module-valued-injective-cohomology-comparison` is not a dependency of this proof.
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`: its direct import is redundant.
  Its theorem remains needed transitively by the reused injective direct-image theorem;
  this is not claimed as a whole-closure pruning of that node.
- `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`: replaced directly by the
  narrower `PointCohomology` for terminal etale-point exact sections. Finite-support
  results may remain needed elsewhere, including the independent curve proof.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: its direct import is redundant
  with the derived global-sections imports needed by the proof.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: redundant with the public
  GlobalSections import.

The original node's direct use of `lem-kun-0f1c` is replaced by the perfect-base
smooth-subalgebra construction and the four proved comparison modules. Its general
purely inseparable/perfect-closure route is not needed for this obligation. The original
source-global-cohomology-to-higher-image conservativity step is also unnecessary;
positive higher images vanish directly. `def-weil-pbc-etale-cohomology` remains a
statement convention, not a separate proof obligation.

Removed `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` and
`Sheaf.AlgebraicGeometry.CurveCohomologyConnectedReduction` from the original source
AlgClosedExtension file: both are now private proof imports of the moved curve module
and remain required there, rather than being globally pruned.

Removed `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` from
Vanishing's public imports. Smooth base change now requires the curve input, without
the general qcqs invariance module and its acyclicity dependency. There is no actual
code user of `bijective_cohomologyMap_constantZMod` downstream of Vanishing, as checked
by exact-name rg and downstream.py. The original import path still reexports the curve
result for its two recorded users. The new field-exchange modules also do not import
TopologicalInvariance: their route uses perfectness of k and separability directly.

No additional lemmas below the blueprint unit were proved merely because they appeared
in a planned route. The general cohomology invariance theorem itself is still present
unchanged in its original module.

## Where the brief, the DAG or earlier work was wrong

The DAG cited the general relative field-extension theorem `lem-kun-0f1c`, but that node
has no Lean attachment. The same applies to the general limit-square node
`lem-kun-0ezt`; its recorded statement is only the torsion case. We therefore build the
field-extension comparison in Lean from the existing smooth theorem and isolate the
single degreewise continuity step at the general abelian-coefficient strength actually
stated by the Stacks source. These are interface gaps, not objections to using existing
statements whose proofs still contain sorry.

The old import graph bundled an independently proved curve result with general qcqs
invariance. This created a cycle when applying smooth base change to the acyclicity
obligation. Extracting only the independent curve declaration fixes the graph, keeps
its name, signature, attribute and proof, and retains the unit's curve/Jacobian route.
The old DAG source-cohomology conservativity step was longer than needed: the library
already proves the required injective higher-direct-image vanishing directly.

No statement is disputed and no target statement is changed. The generic continuity
step needs no torsion hypothesis: Stacks 0EZT's second assertion and 0EYM apply to
abelian sheaves. The relevant source number is Lemma 59.86.3 for 0EZT.

## New nodes

`lem-sc-field-extension-higher-direct-image-exchange` attaches the proved degree-q
homology comparison to `FieldExtensionHigherDirectImageExchange`.

`lem-sc-field-extension-derived-direct-image-exchange` attaches the proved
perfect-base, separable smooth-subalgebra construction to
`FieldExtensionDerivedDirectImageExchange`. It uses the actual spectrum limit cone.

`lem-sc-smooth-limit-derived-direct-image-exchange` attaches the proved smooth-stage
exchange and module-to-abelian compatibility to `SmoothLimitDerivedDirectImageExchange`.

`lem-sc-limit-derived-direct-image-exchange` attaches the proved negative-degree
vanishing, derived isomorphism criterion, and Plus/total transport to
`LimitDerivedDirectImageExchange`.

`lem-sc-limit-higher-direct-image-exchange` attaches the sole remaining fixed-degree
continuity theorem to `LimitHigherDirectImageExchange`; its node and docstring list
the source, complete proof and the still-needed geometric/cohomological comparison.

The existing nodes `lem-sc-algclosed-extension-injective-acyclic` and
`sbc-thm-algebraically-closed-invariance` are updated only in permitted proof/Lean fields.
The former follows the actual new proof; the latter only records the declaration's
new module location. Change record:
`coord/changes/smooth-curve-invariance-module.md`.

## Forced adaptations

The delivery adapts two existing source modules because the new field-extension proof imports
the smooth-base-change derived module. The original import graph then passed through
`Derived -> Theorem -> Induction -> Vanishing -> AlgClosedExtension ->
AlgClosedExtensionInjectiveAcyclic`, so retaining the old imports produced an import-cycle
failure in the server build.

* `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` (unclaimed).
  The original module compiles against the changed compiled dependencies (independent review:
  9.7 seconds); no duplicate-declaration compiler error was reproduced. Its adaptation
  accompanies the relocation needed to remove the source import cycle and preserve the original
  public import path.
  The forced edits are: add
  `public import Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension` at line 9; remove the
  private imports of `Curve.ConstantInvariance` and `CurveCohomologyConnectedReduction` at the
  former lines 20--21; and remove the old curve-theorem declaration (the former lines 140--178).
  The general qcqs theorem and every other declaration keep their signatures and proofs. This
  preserves the old module path as a reexport while giving the theorem one defining module.

* `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` (unclaimed).
  The original module compiles against the changed compiled dependencies (independent review:
  21.4 seconds). Restoring its original line 16 recreates the source import cycle through
  Derived, Theorem, Induction, Vanishing, AlgClosedExtension, AlgClosedExtensionInjectiveAcyclic,
  FieldExtensionHigherDirectImageExchange, FieldExtensionDerivedDirectImageExchange and
  SmoothLimitDerivedDirectImageExchange. These are adaptations of unclaimed modules justified
  by the source graph, rather than reproduced single-file compiler failures. The replacement is
  exactly `import Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension` at line 16. The theorem
  is used only in Vanishing proofs, so changing the import from public to private preserves all
  declarations and removes the cycle. The adapted `AlgClosedExtension`, adapted `Vanishing`,
  their direct importers, and the complete delivered sandbox all compile successfully with
  `python3 /home/ubuntu/weil-launcher/lcompile.py --all` (including the existing importers).


## Earlier second reading (a previous round; superseded)

1. **Signatures and visibility.** I diffed every adapted existing module against the repository. The theorem signatures are byte-for-byte unchanged; the curve theorem was relocated with the same binders, attributes, and proof. The only interface change is the declared relocation and the necessary reexport from the original module. Verdict: pass.

2. **Proof validity.** I compiled all nine delivered modules together with `lcompile.py --all`; compilation succeeded and each file was below the 60-second limit. The only remaining `sorry` is the named theorem `isIso_limit_homology_derivedBaseChangeMapPlus`, which has a matching split node and complete source/proof documentation. No forbidden declarations or hollow definitions occur. Verdict: pass, with the documented split.

3. **New statements.** I checked the six new nodes against their Lean declarations, their docstrings, and the existing library search results. Each is a strict intermediate comparison used by the item proof; none restates the item, and the limit higher-image statement is exactly the unresolved fixed-degree continuity step. Edge cases recorded in the docstrings agree with the hypotheses. Verdict: pass.

4. **Pruning and imports.** The item proof uses the direct injective-module acyclicity theorem, field-extension exchange, exact global sections, and the module-forgetting comparison. The old finite-support, lower-shriek, module-valued comparison, and redundant acyclicity imports are removed. Proof-only imports are plain imports; in particular Vanishing now imports the relocated curve module privately because its theorem is used only in proofs. Verdict: pass.

5. **DAG and route.** The updated node proof steps and `proof_deps` match the Lean route, all new nodes carry their module/declaration records, and the original curve unit input remains realized by the moved declaration. The unit route is preserved, with the general field-extension and limit-continuity gaps isolated as documented split nodes. Verdict: pass.

I changed only the report and the Vanishing import visibility after the initial review. The visibility edit is proof-only and compiles with the complete sandbox.

## Earlier second reading (a previous round; superseded)

1. **Signatures and visibility.** I diffed the delivered item and both adapted existing
modules against the repository versions. The target theorem signature is byte-for-byte
unchanged. The relocated curve theorem keeps its declaration name, binders, visibility,
attribute, and proof; the original module reexports it. Vanishing's changed import is
private and all its declarations are unchanged. Verdict: pass.

2. **Proof validity.** I compiled all nine delivered modules together with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`; every file compiled successfully
within the per-file limit. There is no `sorry` in the item or adapted modules. The only
remaining `sorry` is the named theorem
`AlgebraicGeometry.Etale.isIso_limit_homology_derivedBaseChangeMapPlus`, with its split
node, source citation, and complete proof description. No forbidden declaration or hollow
definition is present. Verdict: pass, with the documented split.

3. **New statements.** I checked each new declaration against its node, docstring, and
proof use. The four proved exchange declarations are strict intermediate comparisons;
the remaining limit theorem is a single fixed-degree continuity step with arbitrary
abelian coefficients. None restates the target, and the documented edge cases match the
hypotheses. Repository and recorded Mathlib searches found no pre-existing declaration
of these comparisons. Verdict: pass.

4. **Pruning and imports.** The item now uses the direct injective-module acyclicity
theorem, the field-extension exchange, exact global sections, and the module-forgetting
comparison. The obsolete finite-support, lower-shriek, module-valued comparison, and
redundant acyclicity imports were removed. Proof-only imports are private. The relocated
curve theorem remains a private dependency of Vanishing, while the source module
publicly reexports it for its original users. Verdict: pass.

5. **DAG and route.** Existing node signatures and target statements are unchanged. The
updated proof dependencies and origins follow the Lean proof, and every new declaration
has a matching split node with source, edge cases, and Lean attachment. The smooth-curve
unit route is preserved by the relocation; the general field-extension and limit
continuity gaps are isolated as the documented split nodes. Verdict: pass.

I changed only this report section after the earlier review; no Lean proof, declaration,
node statement, or import was changed during this second reading.

## Second reading by X2

1. **Signatures and visibility.** I compared the item and both adapted existing modules
   byte-for-byte with the repository versions. The target theorem signature is unchanged.
   The moved curve theorem has the same declaration, binders, attribute, and proof, while
   the original module still reexports it. The Vanishing import is private and its
   declarations are unchanged. Verdict: pass.

2. **Proof validity.** I compiled all nine delivered modules with
   `python3 /home/ubuntu/weil-launcher/lcompile.py --all`; all compiled successfully and
   each stayed below the 60-second limit. The item and adapted modules contain no sorry.
   The only remaining sorry is the named `isIso_limit_homology_derivedBaseChangeMapPlus`,
   whose docstring and split node state the source and complete unresolved continuity
   argument. No forbidden declarations or hollow definitions occur. Verdict: pass with
   the documented split.

3. **New statements.** I checked every new node against its Lean declaration, docstring,
   proof use, and repository search results. The four proved exchange declarations are
   strict intermediate comparisons; the remaining theorem is exactly the fixed-degree
   affine-limit continuity step and has no extra hypotheses. None restates the target,
   and the edge cases in the docstrings agree with the types. Verdict: pass.

4. **Pruning and imports.** The item uses direct injective-module acyclicity, the field
   extension exchange, exact global sections, and the module-forgetting comparison. The
   obsolete finite-support, lower-shriek, module-valued comparison, and redundant
   acyclicity imports are removed. Proof-only imports are private, including Vanishing's
   relocated curve input. Verdict: pass.

5. **DAG and route.** The updated target node's proof steps and dependencies match the
   Lean proof. Every new public declaration has a matching node with source, proof
   origin, and Lean attachment. The smooth-curve unit route remains realized by the moved
   declaration; the field-extension and affine-limit gaps are isolated in their split
   nodes. Verdict: pass.

I changed only this report by adding this second-reading record; no Lean declaration,
statement, node statement, or import was changed during this reading.
