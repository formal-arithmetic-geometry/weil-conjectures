## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentHomInjectiveAcyclic` states that for a Noetherian scheme `X`, a coherent module `F`, and an injective module `I`, the internal sheaf Hom `SheafOfModules.homObj F I` has zero positive-degree module cohomology. The theorem uses `IsNoetherian X`, which is Mathlib's class extending `IsLocallyNoetherian X` and `CompactSpace X`, rendering the node's Noetherian hypothesis (quasi-compact and locally Noetherian). The hypothesis `hF` is `RingedSpace.IsCoherent X.toRingedSpace F`; `[Injective I]` is the injectivity hypothesis. The conclusion `∀ p : ℕ, 0 < p → IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (SheafOfModules.homObj (R := X.sheaf) F I))` renders “for every p>0, H^p(X, Hom(F,I))=0” as the categorical zero object in `ModuleCat`.

The internal Hom declaration used is `SheafOfModules.homObj` from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`. The cohomology notion is `RingedSpace.moduleCohomology` from `Sheaf.Topology.RingedSpaceModuleCohomology`. The Noetherian and injective notions are Mathlib's `AlgebraicGeometry.IsNoetherian` and `CategoryTheory.Injective`; coherent modules use the project's `AlgebraicGeometry.RingedSpace.IsCoherent`.

The source proof dependencies `lem-sc-ext-coherent-hom-injective-flasque`, `lem-sc-zariski-flasque-acyclic`, and `lem-sc-module-abelian-zariski-cohomology` justify the statement mathematically. The first has the recorded declaration `AlgebraicGeometry.isFlasque_homObj_of_coherent_injective` in `Sheaf.AlgebraicGeometry.IsFlasqueHomObjOfInjective`. The latter two have no landed `lean` records in the dependency nodes, so no private replacements were introduced; the present file states the target directly using the established module-cohomology definition.

Edge cases checked: `p = 0` is excluded by `0 < p`; the empty scheme and one-point scheme reduce to the zero higher-derived functor case; `F = 𝒪_X` specializes to acyclicity of an injective module. The file compiled with `scompile.py` without errors or warnings.

Searches: `rg` over `WeilConjectures` and project `lean/Sheaf` for the node and for Hom/injective/acyclic declarations; Mathlib search for `moduleCohomology`, `IsNoetherian`, and sheaf Hom acyclicity. The exact Hom-flasque declaration was found in `Sheaf/AlgebraicGeometry/IsFlasqueHomObjOfInjective.lean`; no existing declaration matching the target acyclicity statement was found.

## Earlier second reading (a previous round; superseded)

The statement, hypotheses, imports, and edge cases were reread against the node and source. The recorded signature omits the proof body as required; the declaration is marked `existing: false` on branch `sheaf-dag`.

## Second reading by V1

I independently read the item node, its six statement dependencies and their recorded
signatures, the shared coherent-module and cohomology definitions, and the upstream
internal Hom definition. There are no new nodes, dependency modules, or statement
corrections in this delivery.

Object/hypothesis/conclusion checklist (all pass):

- Scheme X: `(X : Scheme.{u})`, with arbitrary universe `u`, is precisely the scheme.
- Noetherian: `[IsNoetherian X]` is the Mathlib class extending exactly
  `IsLocallyNoetherian X` and `CompactSpace X` (Noetherian.lean:280). These render
  `pqf-def-locnoeth` and `def-weil-pbc-quasi-compact-scheme`; no separatedness,
  regularity, finite dimension, or base field is assumed.
- Two O_X-modules: `(F I : SheafOfModules.{u} (moduleRings X.toRingedSpace))` is the
  established module-sheaf category on X, with its inherited abelian structure.
- Coherent F: `hF : RingedSpace.IsCoherent X.toRingedSpace F` is the recorded
  `pqf-def-coherent` declaration: finite type and finite-type kernels of all maps from
  finite free modules on all opens. Its definition was opened, not inferred from its name.
- Injective I: `[Injective I]` is the recorded `def-sp-injective-resolutions` predicate
  (Basic.lean:32): extension of every map into I along every monomorphism, equivalently
  surjectivity of the node's contravariant Hom restriction. No resolution is an extra input.
- Internal Hom: `SheafOfModules.homObj (R := X.sheaf) F I` is the recorded
  `def-pur-sheaf-hom` declaration (InternalHom.lean:143). I opened its construction:
  sections are the O-linear maps on localized sites, with scalar multiplication,
  restriction, and a sheaf structure; this is not global Hom or stalkwise Hom.
- Cohomology: `(RingedSpace.moduleCohomology X.toRingedSpace p).obj ...` is the
  right-derived global-sections functor on module sheaves, as `pqf-def-cohomology`
  identifies explicitly in PQFCohomology.lean. I opened both this signature and the
  underlying definition in RingedSpaceModuleCohomology.lean; it lands in ModuleCat,
  not bare Type and not the abelian-sheaf Ext definition.
- Vanishing in every positive degree: `∀ p : ℕ, 0 < p → IsZero (...)` covers exactly
  all p>0 after X,F,I and their hypotheses. IsZero in ModuleCat means the zero module,
  hence precisely zero cohomology. No extra clause or choice of resolution occurs.

Source: the local literature checkout lacks the Stacks .tex files. I fetched the official
Stacks repository's equiv.tex and cohomology.tex into this item's scratchpad and read
`lemma-Ext-0-regular` (Tag 0FZ3), `section-ext`, and
`lemma-injective-restriction-surjective` (Tag 01EA).
https://stacks.math.columbia.edu/tag/0FZ3 is the corresponding displayed lemma.
0FZ3 assumes regularity and finite dimension for the Ext bound; its cited Ext-sheaf
spectral sequence is on an arbitrary ringed space, and the 01EA extension-by-zero argument
also only assumes a ringed space. Thus these extra hypotheses of the final bound are not
hypotheses of this acyclicity input. The node's stated Noetherian/coherent specialization
is valid and is rendered unchanged. The node's three proof steps are flasqueness,
flasque abelian-sheaf acyclicity, and the module/abelian comparison, in that order.

Edge cases: p=0 is excluded and need not vanish; all positive natural degrees occur.
Empty schemes are admitted (no Nonempty assumption). F=0 or I=0 is admitted and the
internal Hom is zero. There is no index set in this statement. No characteristic or
field restriction occurs. `universe u` is explicitly bound; the opens, rings and module
sections use the shared universe convention, and the internal Hom's max-universe on
this site is u. Larger module carriers can be represented by raising u; there is no
fixed small universe or independent test-universe hypothesis. No hidden binders remain.

Independent searches:

- LeanFinder: "higher cohomology of internal Hom into injective sheaf of modules vanishes"
  returned eight related declarations (Sheaf.H, cohomologyPresheaf, K-injective complexes,
  and a derived-category vanishing result), none stating this theorem.
- Loogle: `SheafOfModules.homObj` returned no hits and reported the upstream identifier
  unknown; this is a search limitation, not evidence that the definition is absent.
- LeanSearch: "internal Hom injective sheaf acyclic global sections" was unavailable
  (Internal Server Error); no negative verdict is attributed to that service.
- `rg -i 'acyclic.*hom|hom.*acyclic|coherent_hom_injective_acyclic'` on Mathlib,
  WeilConjectures and project lean/Sheaf found complex-level results and flasque-sheaf
  results, but no exact internal-Hom module-cohomology statement. I also searched
  dag/lean_names_upstream.json for homObj and injective names.
- Opened `Scheme.Modules.subsingleton_H_of_injective` in upstream InjectiveFlasque.lean
  and `TopCat.Sheaf.IsFlasque.subsingleton_H` in upstream Flasque.lean: the former treats
  I itself, the latter flasque abelian sheaves and their Ext cohomology. Neither is this
  theorem. The landed Hom-flasque sibling gives flasqueness, not cohomology vanishing.

Mismatches repaired: H8/H9 documentation only. Added the conventional copyright header
and module source docstring; expanded the theorem docstring with the source place and
all three DAG proof steps and their exact dependency IDs. The theorem signature,
imports, namespace, and node's mathematical statement are unchanged. There are no
new definitions, hollow definitions, private copies, or proved results: the sole theorem
retains `by sorry`. The node's `lean.statement` remains the file's exact normalized
signature. Compilation and delivery preflight are checked below.
