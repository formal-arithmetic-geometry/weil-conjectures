## Worker report

The delivery states `SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions`
in `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`. Its proof is `sorry` only.
The supporting module `Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf` defines
`SheafOfModules.IsFiniteTypeLocallyConstant` with real data (a proposition, no sorry).

Source checked: `literature/stacks-project/sites-modules.tex`,
`lemma-kernel-finite-locally-constant`, Tag 093U (3), lines 8542–8614.
The source explicitly asserts weak Serre closure for finite type locally constant
module sheaves over a Noetherian ring. The node's statement requires no correction.

Hypothesis and clause correspondence:

- A small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  This uses the associated Grothendieck topology of the recorded precoverage site;
  the assertion is independent of the choice of covering presentation.
- A commutative Noetherian ring is `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Sheaves of the constant ring's modules are `CategoryTheory.ringedSiteModules.{u}
  ((constantSheaf J RingCat.{u}).obj (RingCat.of B))`.
  This is the dependency's transparent Mathlib `SheafOfModules` abbreviation.
- Locally constant of finite type is `IsFiniteTypeLocallyConstant J B F`:
  for EVERY object U there is a covering sieve S, and for EVERY arrow V → U in S
  there is `M : ModuleCat B` with `Module.Finite B M` and an isomorphism of
  module sheaves on the slice. Constants are constructed by the EXISTING
  `strictPerfectConstantSheaf` functor and restricted by `.over V`.
  The canonical constant-restriction comparison identifies this with constants
  formed directly on the slice. In particular these are module-linear isomorphisms,
  not isomorphisms merely of underlying sets or abelian groups.
- Kernels and cokernels: the first conjunct quantifies over every F, G and f : F ⟶ G;
  from the two local-constancy hypotheses it concludes that `kernel f` AND
  `cokernel f` satisfy the same predicate.
- Extensions: the second conjunct quantifies over every `ShortComplex` S and uses
  `S.ShortExact` (exact, monic first map, epic second map); local constancy of
  `S.X₁` and `S.X₃` implies local constancy of `S.X₂`.
- No points, connectedness, nonemptiness or terminal-object assumptions occur.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (ideals finitely generated).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`
  (sheafification of the constant presheaf).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (transparent abbreviation of Mathlib's category; full declaration read).
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the site/sheaf interface
  from def-weil-pbc-sites-and-cohomology; the cohomology clause is not needed here.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (top submodule finitely generated).
- `Sheaf.Paper.StrictPerfectCoefficientPackage`: `SheafOfModules.strictPerfectConstantSheaf`
  and `strictPerfectConstantPresheaf`, read at lines 164–189. The former is the latter
  composed with module sheafification along the ring sheafification unit. This is
  the existing construction, not an invented constant-module object.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor` (actual restrictions to the localized ringed site).
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`.

Proof-dependency imports: `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
(the recorded exact forgetful theorem), `Mathlib.CategoryTheory.Sites.EpiMono`
(local surjectivity), `Mathlib.CategoryTheory.Sites.CoverLifting` (constant restriction),
`Mathlib.RingTheory.Noetherian.Basic` (finite submodules). Localization and sheafification
modules are already public transitive imports of the definition module. The three
proof nodes for constant section exactness, local constant morphisms and constant
restriction have no separate landed statement modules; no unavailable module was imported.
The theorem docstring spells out all six proof steps of the node.

Edge cases checked mathematically: empty site (all local conditions vacuous), empty
covering sieve (the restriction is zero), zero module, zero ring, zero kernel/cokernel,
and extensions by zero. No positive rank is required, so the proof's free presentation
allows rank zero. The universe u can be chosen to contain the small site, coefficient
ring and module carriers; no independent lower test-object universe or points assumption
limits the assertion. Finitely generated B-modules admit carriers in the chosen coefficient
universe, and the ambient category is precisely the small-site module category.

Searches performed before writing:

- msearch LeanFinder: "Finite locally constant module sheaves over a noetherian ring
  closed under kernels cokernels extensions" returned condensed specializations,
  `SheafOfModules.IsFiniteType`, and solid modules; no arbitrary-site closure theorem.
- msearch Loogle: `CategoryTheory.constantSheaf, SheafOfModules`: OK, 0 hits.
- msearch grep: `IsLocallyConstant|WeakSerre|constantSheaf` in
  `Algebra/Category/ModuleCat`: OK, 0 hits.
- msearch LeanSearch: "Locally constant finite type sheaves of modules on an arbitrary
  site": unavailable, Internal Server Error. This supplies no absence evidence.
- msearch LeanFinder: "Locally constant finite type module sheaf on a site locally
  isomorphic to a constant finitely generated module": specialized condensed functors
  and `SheafOfModules.IsFiniteType`, no matching arbitrary-site predicate.
- rg in upstream WeilConjectures and local lean/Sheaf for LocallyConstant,
  locallyConstant, constantModule, and constantSheaf/RingCat combinations found
  scheme-specific lissity, pro-etale-specific lissity, and the reusable arbitrary-site
  `strictPerfectConstantSheaf` construction. These specialize the site and cannot
  replace the arbitrary-site predicate. The constant functor IS reused.
- rg for `IsFiniteTypeLocallyConstant` in dag/nodes, lean/Sheaf, upstream WeilConjectures
  and Mathlib: no hits. Searching the item id upstream: no hits.
- `tools/blueprint_refs.py search 'locally constant finite type'`: 0 blueprint matches.
  DAG definition-node searches also found only scheme/pro-etale-specific predicates.
- The strict-perfect package's dependency closure was checked: it does not reach this
  item, so reusing its constant functor introduces no cycle.

Validation: scompile.py compiled EACH delivered module separately in dependency order,
against the published library and private dependency overlay: 1.6 s and 2.0 s respectively;
no errors or warnings. Server output confirmed nice 19, two threads, 60 seconds per file.
No local Lean compiler or global build was run. Nothing is proved at stage 2.

## New nodes

`def-weil-pbc-finite-type-locally-constant-module-sheaf` supplies the missing arbitrary-site
predicate, following Tag 093U (3) and the node's explicit definition of local constancy.
It uses covering sieves and module-linear slice isomorphisms to restrictions of constant
finite modules. The constant functor is reused from
`def-weil-pbc-strict-perfect-coefficient-package`, not redefined. Searches above and the
new node's mathlib_searches explain why neither a Mathlib finite-type predicate alone
nor the scheme-specific existing predicates state this notion. The node is cited by
the item's new stmt_deps entry. No dependency module or statement correction is needed.

## Second reading by NA

I independently read both sandbox modules, both node JSON files, the statement
dependency records and their declarations. I read sites-modules.tex at
definition-locally-constant, lemma-locally-constant-finite-type and
lemma-kernel-finite-locally-constant, including the whole proof of part (3).
The latter is Tag 093U. Its only coefficient hypothesis is Noetherianity;
the node explicitly specifies commutative coefficients. The final-object
hypothesis in the preceding local-morphism lemma applies on slices, not to
the original site. The nonempty-topos hypothesis of the finite-type detection
lemma is likewise not an extra hypothesis of Tag 093U: degenerate slices
admit the zero-module description.

Object, hypothesis and conclusion checklist, in the order of the node:

- Small site: `{C : Type u} [SmallCategory C]` and
  `(J : GrothendieckTopology C)`. Verdict: correct. Covering sieves encode
  the associated topology of the recorded precoverage site, with the same
  sheaves and local conditions. No terminal object or points are assumed.
- Commutative coefficient ring: `(B : Type u) [CommRing B]`.
  Verdict: exactly the node, including the zero ring and every characteristic.
- Noetherian hypothesis: `[IsNoetherianRing B]`. Verdict: correct.
  I read Noetherian/Defs.lean, including `isNoetherianRing_iff_ideal_fg`;
  this says every ideal is finitely generated, as the dependency requires.
- Constant coefficient ring sheaf: `(constantSheaf J RingCat.{u}).obj
  (RingCat.of B)`. Verdict: correct. ConstantSheaf.lean defines this as
  the constant presheaf followed by `presheafToSheaf`, without requiring
  a terminal object. Bundling the commutative ring in RingCat retains its
  ring and module structures; no noncommutative coefficients are introduced.
- Ambient module sheaves: `CategoryTheory.ringedSiteModules.{u}` of that
  ring sheaf. Verdict: correct. I read RingedSiteModules.lean and Mathlib's
  `SheafOfModules`, its linear `Hom`, and its abelian instance. This is a
  transparent abbreviation of the general ringed-site category, not the
  scheme-only module category or the category of underlying abelian sheaves.
- Locally constant with finite type values: `IsFiniteTypeLocallyConstant
  J B F`. Verdict: correct. Its body is `∀ U, ∃ S, S ∈ J U ∧ ...`, then
  for every arrow `f : V ⟶ U` in S, `∃ M : ModuleCat.{u} B,
  Module.Finite B M ∧ Nonempty (F.over V ≅ ... .over V)`. Each value may
  depend on the cover member; no uniform module or rank is imposed.
  `Module.Finite` means finitely generated, not a finite underlying set.
  The isomorphism is in the module-sheaf category on the slice.
- Constants in that predicate: `(strictPerfectConstantSheaf J B).obj M`.
  Verdict: correct. I read its actual definition and
  `strictPerfectConstantPresheaf` in StrictPerfectCoefficientPackage.lean:
  the data are the constant module presheaf with identity restriction maps,
  followed by module sheafification along the ring-sheafification unit.
  No perfectness, projectivity, bounded complex, or splitting is demanded
  of M by this reusable functor. `SheafOfModules.over` really restricts
  to `J.over V` and the restricted ring; I read its definition in Mathlib's
  PushforwardContinuous.lean. The constant-restriction dependency identifies
  this with constants formed on the slice, so the formulation is equivalent
  to the source definition.
- Kernels between objects of the subcategory: the first conjunct quantifies
  over arbitrary `F G` and `f : F ⟶ G`, assumes both predicates and concludes
  `IsFiniteTypeLocallyConstant J B (kernel f)`. Verdict: exact, with no
  monomorphism or epimorphism restriction on f.
- Cokernels: the other conclusion in that same conjunction is
  `IsFiniteTypeLocallyConstant J B (cokernel f)`. Verdict: exact; the two
  local constancy hypotheses have the right quantifier order.
- Extensions: the second conjunct quantifies over every `ShortComplex` S
  in this same category and assumes `S.ShortExact`, the predicate on `S.X₁`
  and the predicate on `S.X₃`, concluding it on `S.X₂`. Verdict: exact.
  I read `ShortExact`: exactness plus a monic first map and an epic second
  map. This encodes every short exact sequence, including nonsplit ones;
  there is no splitting or sectionwise surjectivity hypothesis.

The new definition node
`def-weil-pbc-finite-type-locally-constant-module-sheaf` is warranted: its
notion is not already a general-site DAG definition or existing declaration.
Its self-contained statement matches the displayed predicate and the source's
local constancy definition with finite module values. Its cited dependencies
are exactly the ingredients used; its chapter/unit, creation record, ancestor
and via chain, empty proof fields, null match, none audits and Lean record
meet brief-stage2 section 5. No additional dependency module is needed.

Edge cases: an empty category makes the predicate vacuous; an empty covering
sieve is allowed precisely when it belongs to J. On a sheaf-theoretically empty
slice every module sheaf is zero, so choosing finite value zero loses no case.
Zero modules, zero kernels/cokernels, zero rings and extensions with zero outer
terms are all included. Finite presentations of length zero require no separate
hypothesis. There is no cohomological degree n, characteristic bound, field,
Noetherian site, scheme, or nonempty index-set assumption. A common arbitrary
universe u contains the small site, coefficients and module carriers, as in
the project's small-site convention; it imposes no fixed universe bound or
independent smaller universe on test objects.

Independent searches (different queries from the worker):

- LeanFinder: "A locally trivial sheaf of finitely generated modules on a site
  is stable under exact extensions and kernels over a Noetherian coefficient
  ring". Eight hits concern `SheafOfModules.IsFiniteType`, finite presentation
  and generating-section data; none requires local constancy or states this
  closure assertion.
- Loogle: `"LocallyConstant", "Sheaf"`. Twelve hits concern specialized
  condensed locally constant functions/presheaves, not arbitrary ringed sites.
- LeanSearch: "Locally trivial sheaves of finitely generated modules form a
  weak Serre subcategory on every small Grothendieck site". Unavailable
  (Internal Server Error); this is not evidence of absence.
- rg by `locally.constant`, `locallyConstant`, `LocallyConstant`, `WeakSerre`
  and declaration patterns in Mathlib's Sites and ModuleCat trees, upstream
  WeilConjectures and this project's lean/Sheaf: no matching arbitrary-site
  definition or theorem. I opened upstream ConstructibleSheaf/Defs.lean:
  `LocallyConstantDatum`, `IsLocallyConstantSheaf` and
  `IsFiniteLocallyConstantSheaf` specifically require a scheme's small etale
  site. I also opened this project's `IsLocallyConstantProEtaleModuleSheaf`:
  it specifically requires the pro-etale site. Neither replaces this notion.
  DAG searches for "locally constant" together with "finite type" locate
  the current lemma and specialized scheme/pro-etale definitions, not a
  duplicate arbitrary-site definition. The existing general constant-module
  construction is reused rather than copied.

No mismatch found; I left the Lean and node statements unchanged. There is
no statement_change requiring citer revalidation. Both module and declaration
docstrings cite the source and their own blueprint id. The theorem docstring
retains all six proof steps, including exact restriction, finite kernels,
finite-free presentation, generator lifts, the signed pushout and the final
finite quotient. The only sorry is the theorem's whole proof; the definition
has explicit data. There are no private definitions, file-local notation,
local instances, unbound variables or overlong lines. I mechanically compared
each recorded lean.statement with its literal file signature: both match
verbatim. Compilation and delivery validation are recorded below.

Second-reader validation: scompile.py compiled both delivered files separately
on the server: FiniteTypeLocallyConstantModuleSheaf.lean in 1.6 seconds and
FiniteTypeLocallyConstantSerre.lean in 2.0 seconds, with no errors or warnings.
The private overlay also compiled the two side-only dependency modules.
Every file used nice 19, two threads and the 60-second per-file limit.
