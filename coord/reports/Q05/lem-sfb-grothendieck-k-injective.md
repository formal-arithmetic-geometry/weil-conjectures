## Worker report

This delivery records the exact existing declaration
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
(lines 170–180 of the read-only slopmaster2 source). No new module is needed.
The source is the current blueprint main-20261015, section sec-proetale-coefficients,
unit sk-def-sfb-derived-categories, lemma lem-sfb-grothendieck-k-injective.
The shared node already had an incomplete lead attachment to this same declaration;
this delivery completes the stage-2 lean record, changing no other field.
No repair note exists for this item.

Hypothesis and clause correspondence:

- “Let C be a Grothendieck abelian category”: `{C : Type u}`,
  `[Category.{v} C]`, `[Abelian C]`, `[IsGrothendieckAbelian.{w} C]`.
  Mathlib's Grothendieck condition supplies local smallness, exact filtered colimits
  and a separator at the chosen size. The three universes remain independent.
- “Every cochain complex K”: the conclusion is `HasKInjectiveResolutions C`, whose
  field `exists_isKInjective (K : CochainComplex C ℤ)` quantifies over all complexes.
- “admits ... K → I”: that field is exactly
  `∃ (L : CochainComplex C ℤ) (_ : L.IsKInjective) (i : K ⟶ L), Mono i ∧ QuasiIso i`.
  The change of the bound name I to L has no mathematical effect.
- “monomorphic”: the factor `Mono i` is explicit. The theorem is not merely
  existence of a quasi-isomorphism without monicity.
- “quasi-isomorphism”: `HomologicalComplex.QuasiIso i` means that the cohomology
  map is an isomorphism in every integer degree, as in the recorded dependency.
- “into a K-injective complex I”: `L.IsKInjective` uses Mathlib's
  `CochainComplex.IsKInjective`. Its defining field states that every map from an
  acyclic complex admits a homotopy to zero. Morphisms in the homotopy category
  are chain maps modulo homotopy, so this is precisely Hom_K(C)(A,L)=0 for every
  acyclic A. Mathlib's `CochainComplex.isKInjective_iff_rightOrthogonal` explicitly
  identifies this with right orthogonality to all acyclic objects.

Dependency declarations read:

- `def-weil-abstract-derived-category` has status mathlib. Its record points to
  `DerivedCategory` and `HasDerivedCategory` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (lines 70–95). These use
  `CochainComplex C ℤ` and localization at `HomologicalComplex.quasiIso C (.up ℤ)`.
  The node's current blueprint_update retains precisely these notions.
- The reused declaration imports the class interface through
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`;
  its class `CategoryTheory.Abelian.HasKInjectiveResolutions` was read at lines 83–86.
- The K-injectivity definition and its equivalence with homotopy orthogonality
  were read in `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` at lines 40–80.
  The Grothendieck class was read in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` at lines 55–75.

Edge cases checked: the zero complex and the zero abelian category are included;
there is no nonzero-object or nontriviality requirement. Arbitrarily unbounded
complexes are included, with indices ℤ and no truncation hypothesis. Acyclic K
is still allowed. All acyclic test complexes, including zero, occur in the
K-injectivity definition. No existence assumption for a derived localization or
an equality between object, hom and colimit universes is imposed. No statement
correction, new node, dependency repair, or STATEMENT-DISPUTED issue is needed.

Searches made with `msearch.py Q05 lem-sfb-grothendieck-k-injective`:

- leanfinder: “Every cochain complex in a Grothendieck abelian category admits a
  monomorphic quasi-isomorphism to a K-injective complex”. Eight results,
  including `CochainComplex.IsKInjective` and bounded-below injective-complex
  results; none is the full unbounded Grothendieck theorem.
- loogle: `CategoryTheory.Abelian.HasKInjectiveResolutions,
  CategoryTheory.IsGrothendieckAbelian`. Zero hits; unknown identifier for the
  first name (the resolution class belongs to upstream, not Mathlib).
- grep: `hasKInjectiveResolutions_of_isGrothendieckAbelian|class
  HasKInjectiveResolutions|class IsKInjective`. One Mathlib hit, the K-injectivity
  class in Algebra/Homology/HomotopyCategory/KInjective.lean:42.
- leansearch: “Every Grothendieck abelian category has K-injective resolutions by
  monomorphic quasi-isomorphisms”. Eight hits on ordinary injective resolutions,
  enough injectives and the small object argument; no full unbounded theorem.
- Direct rg on the slopmaster2 WeilConjectures source for the exact expected
  declaration and item id found the desired instance in
  CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean:173. The complete
  module, instance signature and defining class field were read. The item id
  itself has no upstream occurrence.
- Direct rg on lean/Sheaf for the exact theorem found existing consumers,
  including CategoryTheory/DerivedModuleDirectSums.lean:117 and
  CategoryTheory/Sites/RGammaDerivedLimit.lean:78, using this upstream instance.
- Direct rg on dag/lean_names_upstream.json for the exact theorem returned no
  hit; the declaration's source and the node's current closed upstream audit
  nevertheless identify it directly.

Validation attempted through the prescribed scompile.py wrapper using
scratch/ExistingChecks.lean: it imports only the owning upstream module and
checks the instance, the resolution class field, the orthogonality equivalence,
and the instance's axioms. Both local compilation and server confirmation fail
before this probe is compiled: the compulsory overlay replacement
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
reports at 119:18 that `AlgebraicGeometry.ProEt.overPullbackId` has already been
declared. The wrapper's source-overrides.json forces that unrelated module to
compile before inspecting this delivery's imports. Consequently changing this
probe's single, necessary import cannot repair the error; repairing the overlay
or wrapper is outside this worker's sandbox authorization.

The required deliver2.py --no-push dry run also failed with exit 1 on its
automatically generated existing-declaration probe: both the local attempt and
server confirmation reported the same unrelated overlay duplicate at 119:18.
It printed COMPILE FAILED on the server, nothing pushed; it did not print OK.
No READY claim is made without OK. No new proof or definition is introduced and no source
module is duplicated. The scompile.py --source command successfully returned
the current server's owning module, with the same instance signature and class
field implementation as the local source.

Retry audit (2026-10-16, after the dispatcher restarted this worker): reread
AGENTS.md, the stage-2 brief, stage rules, delivery errors section H, the
current blueprint lemma, the dependency record and the full owning upstream
module. The signature still matches exactly. A structural comparison of the
sandbox node with the shared node confirms that only `lean` differs, and the
JSON remains indent 1, non-ASCII preserved, with a final newline. The date is
2026-10-16 UTC. All previous searches are retained in searches.jsonl; direct
source and project searches were repeated and found the same exact instance.
The current server source was reread with scompile.py --source and has the same
instance signature and implementation.

The retry of scompile.py again fails both locally and in server confirmation
with precisely the same overlay duplicate declaration at Defs.lean:119:18.
Inspection of the wrapper confirms that source-overrides.json unconditionally
ensures this overlay module before visiting the probe's imports. The probe
already imports only the unique owning upstream module, so there is no
redundant delivery import to remove. This is a mandatory tool-overlay failure,
not a duplicate declaration introduced by this delivery; no authorized sandbox
edit can repair that external forced module. The live library, shared project,
and launcher tools have not been edited.

The required deliver2.py --no-push retry was started and waited over six minutes
without producing output. Its process had no acquired worktree-slot descriptor
and no child process; the sharedrepo wrapper waits for a free worktree slot
before any compilation. This queued retry was terminated after the independent
scompile.py retry had already reproduced the fatal mandatory-overlay error
locally and on the server. It did not reach preflight, print OK, or push. The
previous attempt's completed dry run had failed on the same overlay duplicate,
as recorded above. This retry does not claim a successful dry run.

The three required msearch kinds were also rerun: grep again found only Mathlib's
IsKInjective class; Loogle again reported the upstream resolution class unknown
in Mathlib; LeanFinder returned eight candidates (including IsKInjective and
bounded-below CM5b factorization results), with no full unbounded Grothendieck
resolution theorem. Results were appended to searches.jsonl.

## Second reading by Q05

Source audit: read the blueprint lemma at its recorded source place and Stacks
`injectives.tex`, section `section-K-injective` (Tag 079I), Theorem
`theorem-K-injective-embedding-grothendieck` (Tag 079P). The section adds no standing
hypothesis beyond Grothendieck abelian. The Stacks theorem additionally supplies
injective terms and functoriality; these extra clauses are not claimed by this node.
The blueprint statement is unchanged, so no statement_change or citer audit is needed.

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Category C | `{C : Type u} [Category.{v} C]` | Same arbitrary category |
| C abelian | `[Abelian C]` | Exact hypothesis |
| C Grothendieck | `[IsGrothendieckAbelian.{w} C]` | AB5, separator, locally small at w |
| Every cochain complex K | `exists_isKInjective (K : CochainComplex C ℤ)` | All K, unbounded |
| Some target I | `∃ (L : CochainComplex C ℤ)` | Same target notion |
| I K-injective | `∃ (_ : L.IsKInjective)` | Homotopy vanishing definition |
| A map K → I | `∃ (i : K ⟶ L)` | Correct direction and quantifier order |
| Monomorphic | `Mono i` | Exactly required |
| Quasi-isomorphism | `QuasiIso i` | Isomorphism on each cohomology object |
| Every acyclic A tests I | `nonempty_homotopy_zero` for every `K.Acyclic` | Equivalent via `isKInjective_iff_rightOrthogonal` |


I independently opened the node copy, the shared node, the upstream declaration and
the dependency record. The node introduces a Grothendieck abelian category
`\mathcal C`, then quantifies over every cochain complex `K`, and concludes existence
of a monomorphic quasi-isomorphism `K \to I` with `I` K-injective. The final sentence
defines K-injective by vanishing of `Hom` in `K(\mathcal C)` from every acyclic
complex. The upstream instance renders the category hypotheses as
`{C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]`; its
`HasKInjectiveResolutions.exists_isKInjective` field renders the universal complex,
the target `L : CochainComplex C ℤ`, `L.IsKInjective`, a map `i : K ⟶ L`, and the
conjuncts `Mono i ∧ QuasiIso i`. `CochainComplex.IsKInjective` is the recorded
Mathlib notion and its `isKInjective_iff_rightOrthogonal` theorem identifies the
condition with the stated homotopy-category vanishing. Every object and hypothesis
therefore matches, with no extra boundedness, nonzero, finiteness, characteristic,
or derived-category-existence assumption; the renaming `I` to `L` is immaterial.

The zero category, zero complex, acyclic complex, and all unbounded integer degrees
are covered. Universes `u`, `v`, and `w` remain independent. The only dependency,
`def-weil-abstract-derived-category`, is used through the recorded standard
`DerivedCategory`/quasi-isomorphism interface; no dependency repair is needed.
Independent searches were made with LeanSearch, LeanFinder, Loogle, and `rg` over Mathlib,
the upstream `WeilConjectures` tree, and project `lean/Sheaf`; they found only the
Mathlib K-injectivity definition and the exact upstream instance, so no new module is
appropriate. I found no mismatch and changed no statement or source declaration.

The fresh second-reader `scompile.py` run passed both local compilation and server
confirmation for `scratch/ExistingChecks.lean`. It checked the exact existing
instance, the universal resolution field, and the right-orthogonality equivalence;
`#print axioms` returned only `propext`, `Classical.choice`, and `Quot.sound`.
The old unrelated overlay duplicate described in the worker's history is resolved.
The second-reader `deliver2.py --no-push` run printed `OK (dry run)` for
commit `266381e7cb`: server preflight and the generated existing-declaration
compilation both passed. The delivery consists only of this report and the
item's completed `lean` binding.

Second-reader search details: LeanFinder used “An unbounded complex in an AB5
abelian category with a generator embeds in a homotopically injective complex”
(eight candidates: bounded-below CM5b, IsKInjective, enough injectives; no exact
unbounded result); Loogle used `CochainComplex.IsKInjective` (12 hits: the notion
and its elementary API); grep used
`kInjectiveResolutionFunctor|exists_isKInjective|homotopyZero` (17 Mathlib hits,
no full resolution result); LeanSearch used “Every unbounded cochain complex in
a Grothendieck category has a monomorphic quasi-isomorphism into a homotopically
injective complex” (eight ordinary/bounded-below resolution candidates). Direct
`rg` for “homotopically injective”, “monomorphic quasi-isomorphism”, and these API
names in upstream and `lean/Sheaf` confirmed the exact upstream instance. The
project's KInjectiveDegreewiseExistence module states the stronger termwise
injective/functorial result; it does not require replacing this exact match.
No new nodes, definitions, dependency modules, proofs, or postponed theorems were
introduced. Existing upstream docstrings remain unchanged; the node signature
is verbatim the existing instance header, and all its universes are bound.
