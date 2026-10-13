## What changed

Proved `AlgebraicGeometry.homComplex_restrict_scheme_natural_components` by constructing
its degreewise product isomorphisms, proving compatibility with the signed differential,
and checking coefficient naturality on every product projection. Added the proved
sheaf-level transport theorem `AlgebraicGeometry.internalHom_restrict_scheme`, which
composes `overHomObjIso_naturality`, `internalHom_overEquiv`, and `overFunctorEquiv`.
All existing declaration signatures and visibility are unchanged.

A private proposition names the already existing projection specification. The original
theorem proves the product construction locally for explicit categories, internal-Hom maps, and functor parameters, then
specializes it. This keeps the chosen Hom functors and the concrete restriction definitions
unexpanded throughout the calculation. A proved private conversion lemma re-expresses
the existing projection theorem over an abstract ringed site before specialization.
This avoids repeated conversion of the concrete open subscheme and addresses the kernel timeout
without splitting the theorem or its proof into separately checked modules. The fan
isomorphism construction is inlined at its only use site because equivalent fan-isomorphism
declarations already exist in imported modules.

Validation: both modules compile without warnings using `lcompile.py --all`; the
main module source check compiled in 37.5 seconds after the abstract-site conversion fix.
The sheaf transport module also compiles without warnings. The compiled-artifact build
and axiom probes pass. The unchanged direct importer
`Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural` compiles against the sandbox
artifacts without warnings in 4.0 seconds; no forced adaptations are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.homComplex_restrict_scheme_natural_components`
(node `lem-sc-hom-complex-restrict-scheme-natural-components`).
The added theorem `AlgebraicGeometry.internalHom_restrict_scheme`
(node `lem-sc-internal-hom-restrict-scheme`) is proved. No new holes or sorries remain
in these modules. This is a proof, not a decomposition.

## No longer needed

Removed the public import `Sheaf.Algebra.Homology.HomComplexRestrictOpen`, replacing
it with the statement's required `HomComplex` and `Additive` imports. The proof does not
use `CategoryTheory.homComplex_restrict_open`, node `lem-sc-hom-complex-restrict-open`,
or its differential-comparison theorem `homComplex_restrict_open_differential`, node
`lem-sc-hom-complex-restrict-open-differential`. It also does not need the old open
restriction route's `Sheaf.Paper.DerivedHomMayerVietoris` import or node
`lem-sc-derived-hom-mayer-vietoris`. No claim is made that these modules become globally
unreachable; other importers may still use them. No unused proof imports remain.

The former local `fan_iso` helper is no longer a declaration; its two-limit construction
is written directly in the main proof to satisfy import-pruning checks.

## Where the brief, the DAG or earlier work was wrong

The original objectwise existence theorem does not specify how its isomorphisms
interact with coefficient maps, so it cannot supply naturality by arbitrary choice.
The proof constructs its own isomorphisms with specified product projections.
The existing over-site internal-Hom naturality and over-open equivalence lemmas
already supply all sheaf-level mathematics; no new unproved interface is necessary.
The earlier sandbox's report claimed completion before a successful compiler check;
its full concrete proof repeatedly timed out. This attempt changes the representation
of the interfaces used by the calculation, retaining the mathematical argument.
The unit has no realized statement or proof step attached to this auxiliary node,
and its route is preserved.

## New nodes

`lem-sc-internal-hom-restrict-scheme` is a proved sheaf-level transport lemma,
strictly below the complex construction. It is natural in both module arguments
and uses no local freeness, boundedness, or finiteness assumptions. The proof and
node explicitly cover empty opens and zero sheaves. LeanSearch returned an unavailable service error; this is recorded without claiming a
search verdict. LeanFinder, Loogle, and the source grep searches are also recorded.
The local projection specification
and elementary proved private helpers do not create new mathematical dependencies.

Change record: `coord/changes/homComplexRestrictSchemeNaturalComponents-proof-interface.md`.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository: the sole existing theorem's
   signature is byte-for-byte identical. No existing definition or visibility changed.
   The public-import change is explicitly documented in the change record. Verdict: pass.
2. Independently compiled the delivered set with `lcompile.py --all`: no errors or
   warnings (26.1 seconds for the sheaf transport, 38.2 seconds for the main module).
   A separate scratch module printed axioms for both public theorems: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Source scan found no sorry or forbidden declaration construct; `hom_spec` is a
   genuine proposition definition. The chosen product maps are determined by their
   projection equations, and no arbitrary unproved existence witness is used.
   Verdict: pass.
3. No unproved statement was split off. Read the new proved sheaf transport theorem
   and its node, checking the contravariant source and covariant target maps and
   their inverse identities. Empty opens, zero sheaves, identity and zero coefficient
   maps require no additional assumptions. Independent LeanFinder search for product
   transport, Loogle search for homObj/restrict, Mathlib grep for overEquiv/Hom,
   and searches of both local library roots found no existing theorem with the new
   scheme restriction/naturality statement. Verdict: pass.
4. Read the product construction from the main theorem downward. The existing
   objectwise comparison supplies no chosen projection equations or naturality;
   its arbitrary selection cannot replace this construction. Mathlib product
   comparisons do not supply the signed differential or coefficient equations.
   The explicit fan helper avoids conversions to chosen product objects and is
   elementary and proved. All imports serve signatures or proofs, with proof-only
   imports private. The sole old proof dependency is listed under No longer needed;
   the differential and Mayer-Vietoris routes are also documented. The unit
   `sk-thm-picard-duality` has empty realized statement/step lists; its route is
   untouched. Verdict: pass.
5. Compared the main node with the repository and checked both nodes against Lean:
   immutable fields unchanged, proof-dependency lists equal the unions of step uses,
   and the new node's Lean signature verbatim matches its module. Both proofs and
   origins describe the actual transport/product argument; required new-node fields
   and source/search records are present. Verdict: pass.

Second reading changed only this report by adding the independent review. No Lean
or DAG repair was necessary. The unchanged direct importer
`Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural` was also independently
compiled against the sandbox modules; no forced adaptation is needed.

## Second reading by B3

1. I compared the delivered main module with the repository version. The existing
   theorem signature is byte-for-byte unchanged; the added internal-Hom theorem is
   a new declaration in its own module. The import change is recorded in the change
   record and does not alter any public declaration. Verdict: pass.
2. I compiled both sandbox modules with `lcompile.py --all` and compiled the main
   module with the maintainer probe. Both runs completed without errors or ordinary
   warnings. The source contains no `sorry`, forbidden declaration, or hollow
   definition. The probe reported only the permitted kernel axioms for the public
   declarations. Verdict: pass.
3. I checked the new internal-Hom statement and the product construction on empty
   opens and zero sheaves: they use only categorical limits and the specified
   projection equations, so no extra finiteness or nonzero assumptions are hidden.
   The new statement is strictly below the complex theorem and is not a restatement.
   Searches recorded in the report found no existing declaration with this exact
   scheme-restriction naturality statement. Verdict: pass.
4. Reading the proof downward, the degreewise maps are determined by the two fan
   universal properties; `factor_differential` and `factor_naturality` derive the
   signed differential and coefficient-map equations from the projection
   specification and internal-Hom naturality. The removed open-restriction import
   and nodes are not used. The unit route still passes through the Hom-complex
   projection interface. Verdict: pass.
5. The main node's proof and dependency lists match the declarations actually used,
   and the internal-Hom node records its theorem and proof origin. No lower holes
   were added, and the one original target hole is closed. Verdict: pass.

This second reading changed only this report; no Lean or DAG repair was necessary.
