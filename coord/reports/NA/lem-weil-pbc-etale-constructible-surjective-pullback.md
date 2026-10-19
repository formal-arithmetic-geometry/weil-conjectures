## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_surjective_pullback`.
Its only theorem proof is `sorry`. No definition, dependency record, or natural-language
statement was changed, and no new node was needed.

The node agrees with Stacks Tag 095Q, lemma-check-constructible (3), read directly in
`literature/stacks-project/etale-cohomology.tex`, lines 12276–12318. The source allows
Noetherian rings; the node explicitly specializes to finite commutative rings.

Hypothesis and clause correspondence:
- The schemes U and V are `{U V : Scheme.{u}}`, with the morphism `f : V ⟶ U`.
- Quasi-compactness of each scheme is `[CompactSpace U]` and `[CompactSpace V]`.
- Quasi-separatedness of each is `[QuasiSeparatedSpace U]` and `[QuasiSeparatedSpace V]`.
- Surjectivity on points is `[Surjective f]`.
- The finite commutative coefficient ring is `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
- The module sheaf on the small etale site of U is
  `F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  This uses the constructible chapter's recorded module-valued encoding of modules over
  the constant coefficient ring sheaf, expressly allowed by def-weil-pbc-etale-sheaves.
- “F is constructible” is `IsConstructibleEtaleModuleSheaf F`, the recorded definition
  with a finite locally closed scheme stratification, constructible stratum images,
  and module-linear etale trivializations with finite module values.
- “if and only if” is `↔`.
- “the inverse image is constructible” is
  `IsConstructibleEtaleModuleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)`.
  This is the recorded inverse image functor, with the same coefficient ring throughout.

Statement dependencies used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: scheme quasi-separatedness.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: recorded sheaf conventions. The local
  older source checkout lacks that upstreamed path; the group clone retains its earlier
  `Sheaf/AlgebraicGeometry/EtaleSheaves.lean` text, which was read, including its module-valued
  encoding convention in the node record. The canonical recorded import is used.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`; its complete construction and
  docstring were read.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`; its complete signature, construction and docstring
  were read, as was `upperStarLowerStarAdjunction`.
- def-weil-pbc-scheme-conventions is a convention-only record with no declaration to import.

The file also imports the recorded modules of all stated proof dependencies, including
Mathlib matches, as non-public imports. Its docstring explains all five proof steps:
stratification pullback; filtered presentation and split-epi selection; geometric stalk
surjectivity detection; a second quotient presentation for the kernel; constructible
cokernel closure. No proof-dependency declaration is used as a substitute for a
statement-dependency notion.

Edge cases checked: empty U and V are allowed (including the empty-to-empty surjection);
no nonemptiness assumption was introduced. Surjectivity rules out empty V over nonempty U.
The zero coefficient ring and zero module sheaf are allowed. No characteristic, etaleness,
Noetherian-scheme, finite-type-morphism or extra quasi-compact-morphism hypothesis was added.
The module universe is u+1, as required by the recorded constructibility definition and
inverse image functor, with no independent small test universe.

Searches performed:
- `msearch.py` LeanFinder: “constructible etale module sheaf if and only if pullback along
  surjective morphism qcqs schemes constructible”. Eight hits, concerning constructible
  subsets and etale morphisms, with no matching sheaf descent theorem.
- `msearch.py` Loogle: `AlgebraicGeometry.Surjective, Sheaf`. Zero hits; the service reported
  unknown identifier `Sheaf`.
- `msearch.py` LeanSearch: “A sheaf of modules is constructible if and only if its inverse
  image under a surjective morphism of quasi compact quasi separated schemes is
  constructible.” Service unavailable (Internal Server Error); no verdict inferred.
- `msearch.py` Mathlib grep: `constructible.*(surjective|upperStar)|surjective.*constructible`.
  Two unrelated hits on constructible topologies/prime spectra.
- `rg` of the source project's WeilConjectures tree and the group clone's `lean/Sheaf`:
  the same concept/name pattern found existing pullback preservation and derived stability,
  but no surjective-descent equivalence for this predicate. Searching the item id found
  no source declaration. Searching `dag/lean_names_upstream.json` found no matching name.

No statement fault or disputed statement was found. Server compilation and the delivery
dry run are recorded below after validation.

Validation: `scompile.py NA lem-weil-pbc-etale-constructible-surjective-pullback` compiled
this delivered module cleanly on the server in 1.5 seconds (nice 19, two threads, 60-second
limit). `deliver2.py NA lem-weil-pbc-etale-constructible-surjective-pullback --no-push`
printed OK: server compilation and preflight passed except for the independent second
reading, which is reserved for the next worker. Nothing was pushed.


## Second reading by NA

Read the node's complete statement and five proof steps, the delivered Lean file,
all six statement-dependency node records, and the definitions they refer to. Read
Stacks `etale-cohomology.tex`, lemma-check-constructible (Tag 095Q), including the
entire statement and proof. Its assumptions are a surjective morphism between qcqs
schemes and a Noetherian coefficient ring in clause (3); there is no ambient base
field, characteristic, separation, or scheme-Noetherian hypothesis. The node explicitly
specializes clause (3) to finite commutative rings, which are Noetherian. No statement
correction is needed.

Object, hypothesis, and conclusion checklist:

- Schemes U and V: `{U V : Scheme.{u}}`. Read Mathlib's `Scheme` and `Scheme.Hom`
  signatures: locally ringed spaces locally affine, with their scheme morphisms.
  Verdict: the same objects, with an arbitrary bound universe u.
- Morphism V to U: `(f : V ⟶ U)`. Verdict: direction and generality agree; no etale,
  finite-type, flat, or finite-presentation instance is requested.
- Quasi-compact U and V: `[CompactSpace U]` and `[CompactSpace V]`. Verdict: exactly
  quasi-compactness of their underlying spaces, including the empty space.
- Quasi-separated U and V: `[QuasiSeparatedSpace U]` and `[QuasiSeparatedSpace V]`.
  Read Mathlib's affine-intersection and terminal-morphism equivalences in
  `Morphisms/QuasiSeparated.lean`. Verdict: scheme quasi-separatedness, not separatedness.
- Surjectivity: `[Surjective f]`. Read its class in `Morphisms/UnderlyingMap.lean`:
  the sole field is `Function.Surjective f`. Verdict: precisely surjective on points.
- Coefficients: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`. Verdict: the node's
  finite commutative ring, with no nonzero or characteristic condition.
- Module sheaf on U: `(F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  Read the etale-sheaves dependency record and its available earlier source text
  `Sheaf/AlgebraicGeometry/EtaleSheaves.lean`. The record explicitly permits this
  module-valued encoding for the constructible and six-functor chapters, alongside
  the constant-ring `SheafOfModules` encoding. Verdict: the recorded coefficient
  category, not an underlying set or abelian sheaf in place of a module sheaf.
- Constructibility of F: `IsConstructibleEtaleModuleSheaf F`. Read the complete
  recorded definition and `LocallyClosedStratification`, and the upstream
  `LocallyConstantDatum` it uses. It quantifies over a finite partition realized by
  scheme immersions, requires constructible parts, and module-linear isomorphisms
  to finite constant modules on an etale cover of each stratum. Verdict: both
  conditions (a) and (b) of the definition node are present, with no closure-order
  condition. The inherited topological stratification already requires constructible
  strata in the current upstream source; the repeated conjunct in the recorded
  predicate changes nothing about the complete constructibility condition.
- Equivalence: `↔`. Verdict: both preservation and reflection, in the node's order.
- Constructibility of inverse image:
  `IsConstructibleEtaleModuleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)`.
  Read `upperStar`, its surrounding category/universe variables and
  `upperStarLowerStarAdjunction` in the upstream `UpperLowerStar/Defs.lean`.
  It is left Kan extension along opposite base change followed by sheafification,
  for arbitrary scheme morphisms. Its category instances for ModuleCat are supplied
  by imports, not additional assumptions on f or F. Verdict: the recorded inverse
  image, preserving the coefficient ring and landing on V's small etale site.

Edge cases: no nonemptiness restriction on schemes, covers, or strata was introduced.
Empty-to-empty morphisms are allowed; empty V over nonempty U cannot satisfy the
node's own surjectivity hypothesis. A zero ring and the zero module sheaf are allowed.
The finite stratification's `n = 0` case remains available on the empty scheme.
No integer n, characteristic restriction, or independent small test universe occurs
in the theorem. The universe u is explicitly bound; finite coefficients can be lifted
into u+1, the universe used throughout the recorded constructibility and inverse-image
interfaces. Every variable is bound; no extra typeclass hypothesis is present.

Independent H4 searches (using different wording from the first reader):

- LeanFinder via `msearch.py`: "surjective inverse image reflects finite locally
  constant constructible module sheaves". Eight unrelated results about condensed
  sheaves, coherent topology, and profinite locally constant maps; no match.
- Loogle via `msearch.py`: `"IsConstructibleSheaf"`. Zero hits.
- LeanSearch via `msearch.py`: "Constructibility of an etale sheaf of finite modules
  is detected by pullback along a surjective morphism between quasi compact quasi
  separated schemes". Service unavailable (Internal Server Error); no verdict inferred.
- Direct rg in Mathlib, upstream WeilConjectures, and the project's lean/Sheaf tree:
  `constructible.*(iff|surject|reflect)|[Ss]urject.*[Cc]onstructible|[Cc]onstructible.*[Dd]escent`.
  Read the nearby upstream `Etale.constructibleSheaf_iff` (only the object-property
  wrapper equivalence) and `ConstructibleSheaf/Pullback.lean` (preservation, not
  reflection). The other hits concern derived amplitude, constructible subsets,
  finite pushforward, or limit descent. None states this surjective-pullback
  equivalence. Exact-name/source-label/item-id searches of upstream sources,
  `dag/lean_names_upstream.json`, and lean/Sheaf also found no matching declaration.

No new node or dependency module was delivered, so H12/H13 introduce no additional
objects to review. The file defines nothing; its only theorem has whole proof `sorry`.
Module and theorem docstrings identify Tag 095Q and the exact blueprint id, and the
five numbered proof paragraphs follow all five DAG steps, including the independent
quotient-presentation subargument before its second use on the kernel. Public imports
provide the recorded notions and non-public imports provide the stated proof inputs.
The namespace, module header, import families and 100-column convention pass review.
The node's `lean.statement` was checked verbatim against the theorem signature.

Mismatches and changes: no mathematical, signature, source, or documentation mismatch
found. The Lean module and node copy are unchanged; this second-reading report is the
only addition. Server compilation and delivery validation follow below.

Second-reader validation: scompile.py compiled the sole module cleanly on the server
in 1.5 seconds (nice 19, two threads, 60 seconds per file). The completed second-reading
delivery dry run printed OK; server compilation and full stage-2 preflight passed.
