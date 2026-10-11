## Worker report

The module `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks` states
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_coherent_free_stalks`.
There is one theorem, with proof `sorry`, no new definition, and no statement correction.
Its docstring gives all three steps of the DAG proof with the dependency IDs.

Hypothesis and conclusion correspondence:

- A scheme X: `{X : Scheme.{u}}`, using `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Scheme` (dependency `def-pc-scheme`). Its full structure and
  `Scheme.Hom` were read at lines 35–76: locally ringed space with affine neighbourhoods.
- Locally Noetherian: `[IsLocallyNoetherian X]`, using
  `AlgebraicGeometry.IsLocallyNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`
  (dependency `pqf-def-locnoeth`). Its class at lines 56–59 requires Noetherian rings on
  affine opens; its recorded cover equivalences identify this with the node's definition.
- An O_X-module F: `(F : X.Modules)`, the scheme's category of structure-sheaf modules.
  This is the same carrier as `SheafOfModules (moduleRings X.toRingedSpace)` in the
  coherence dependency, not an abelian sheaf without its module action.
- Coherence: `hcoherent : RingedSpace.IsCoherent X.toRingedSpace F`, using
  `AlgebraicGeometry.RingedSpace.IsCoherent` from `Sheaf.AlgebraicGeometry.Coherent`
  (dependency `pqf-def-coherent`). Its entire docstring and definition were read:
  finite type, and finite-type kernels for every finite-free map on every open.
- Every stalk finite free: `hfree : ∀ x : X, Module.Free ... ∧ Module.Finite ...`.
  The ring is `X.presheaf.stalk x`; the module is the carrier
  `↑(TopCat.Presheaf.stalk F.val.presheaf x)`. The existing scalar action from
  `Mathlib.Algebra.Category.ModuleCat.Stalk` is the action induced by germs;
  no independent action or chosen model of a stalk is supplied.
- Finite locally free on X: `SheafOfModules.IsFiniteLocallyFree.{u, u, u} F` from
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
  Its docstring and class at lines 150–158 require local free generators with finitely
  many generators on each cover member; ranks may vary. A fixed global rank is not imposed.

Sources read: [Stacks 0GWM](https://stacks.math.columbia.edu/tag/0GWM), the
finitely-presented localization-free lemma; [Stacks 01XZ](https://stacks.math.columbia.edu/tag/01XZ),
coherence on locally Noetherian schemes; and the use of the stalk criterion in the proof
of [Stacks 0CC4](https://stacks.math.columbia.edu/tag/0CC4). The local literature file
`literature/stacks-project/algebra.tex` is absent on this machine, so the tags were read online.
The stated scheme criterion is the affine-local application of these sources; the
regularity/integrality assumptions of 0CC4 are used there to obtain free stalks, not here.

Edge cases checked before writing: the zero sheaf has finite free rank-zero stalks and
rank-zero local trivializations. For the empty scheme the stalk condition is vacuous and
an empty cover realizes finite local freeness. Disconnected schemes may have different
ranks on their components; the chosen conclusion allows this. No quasi-compactness or
finite global cover is demanded of X. Nonfree coherent modules (e.g. the ideal (s,t) on
Spec k[s,t]) fail the stalk hypothesis at the origin and cause no false implication.
No characteristic, positive-rank, integrality, or finite-dimensional restriction is added.
Universe u is explicit, matching the recorded coherence carrier; all binders are explicit.

Searches executed with `/home/ubuntu/weil-launcher/msearch.py E1
lem-sc-coherent-free-stalks-locally-free`:

- `leansearch`: query `coherent sheaf finite free stalks finite locally free`;
  service unavailable, Internal Server Error; no result was inferred from the failure.
- `leanfinder`: query `coherent sheaf with finite free stalks is finite locally free`;
  eight hits on finite-type local generators and finite presentation, none states this theorem.
- `loogle`: query `SheafOfModules.IsFiniteLocallyFree`; unknown identifier, zero hits
  (the notion is supplied by the source extension, whose class was opened and reused).
- `grep`: query `coherent.*stalk|stalk.*coherent|isFiniteLocallyFree.*stalk|stalk.*isFiniteLocallyFree`;
  zero hits in Mathlib.
- Direct `rg` in `WeilConjectures/`, Mathlib's sheaf directory and `lean/Sheaf` for
  `IsFiniteLocallyFree|IsLocallyFree|stalk.*[Ff]ree|[Ff]ree.*stalk` found the existing
  finite-local-freeness definitions and related generic-stalk results, no exact theorem.
- Direct `rg` for `coherent.*[Ss]talk|[Ss]talk.*coherent` in the source project and
  `lean/Sheaf` found only related comments, not this criterion.
- Node ID search in `WeilConjectures/` and `dag/lean_names_upstream.json`: no hit.
- Full proposed declaration/file name search in Mathlib, `WeilConjectures/`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

The server initially requested the explicit carrier coercion on the abelian stalk;
this was corrected to `↑(TopCat.Presheaf.stalk F.val.presheaf x)`.

## Second reading by E1

Independent reading of the sandbox node and its complete Lean module, then all three
statement-dependency nodes and the declarations recorded on them. No mathematical,
statement, dependency, or documentation mismatch was found. The Lean and node record
are retained unchanged; this section records the independent review and new searches.

The node's objects, hypotheses, and conclusion, in order:

1. An arbitrary scheme X: `{X : Scheme.{u}}`. Verdict: exact. The recorded
   `AlgebraicGeometry.Scheme` in Mathlib/AlgebraicGeometry/Scheme.lean:42 extends a
   locally ringed space with affine neighbourhoods at every point, as def-pc-scheme
   requires. There is no affine, nonempty, separated, integral, or base-field binder.
2. X is locally Noetherian: `[IsLocallyNoetherian X]`. Verdict: exact. Opened the
   recorded class in Mathlib/AlgebraicGeometry/Noetherian.lean:57 and its already-proved
   `isLocallyNoetherian_of_affine_cover` and `isLocallyNoetherian_iff_of_affine_openCover`
   signatures. Thus its every-affine-open formulation is equivalent to the node's
   existence of a Noetherian affine cover, without quasi-compactness of X.
3. An O_X-module F: `(F : X.Modules)`. Verdict: exact. Read
   Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:39: this is `SheafOfModules.{u}
   X.ringCatSheaf`. Also read `moduleRings` in DerivedHomMayerVietoris.lean:34; its
   composition of the structure sheaf with the forgetful ring functor is the same ring
   sheaf used by X.Modules. Hence the coherence predicate really applies to F itself.
4. F is coherent: `(hcoherent : RingedSpace.IsCoherent X.toRingedSpace F)`.
   Verdict: exact. Read the entire definition and docstring of the recorded
   Sheaf.AlgebraicGeometry.Coherent module. It requires F.IsFiniteType and, for every
   open U, natural number n and map from the free module on ULift (Fin n) to F.over U,
   finite type of its kernel. This is precisely pqf-def-coherent's kernel definition;
   it does not substitute the source project's weaker quasi-coherent-plus-finite-
   presentation predicate. Restrictions and kernels use the inherited structures.
5. Every stalk F_x is a finite free O_{X,x}-module: `(hfree : ∀ x : X,
   Module.Free (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk F.val.presheaf x) ∧
   Module.Finite (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk F.val.presheaf x))`.
   Verdict: exact. Module.Free asserts a basis; Module.Finite asserts finite generation,
   together equivalent to a finite free module. Read the CommRingCat stalk instance
   and `germ_smul` in Mathlib/Algebra/Category/ModuleCat/Stalk.lean: the scalar action
   is induced by the module sheaf's restriction maps and germs. The carrier coercion
   only exposes the additive stalk's type; there is no arbitrary scalar action or
   independently chosen stalk. Quantification is over every actual scheme point.
6. Conclusion: F is finite locally free on X:
   `SheafOfModules.IsFiniteLocallyFree.{u, u, u} F`. Verdict: exact. Read the class in
   WeilConjectures/Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean:155 and the
   underlying Mathlib LocalGeneratorsData, IsLocallyFreeData and IsFiniteType classes.
   It asks for a covering family of opens and generators whose free-module map is an
   isomorphism on each member, with a finite generator set on each member. Neither a
   uniform rank nor a finite covering family is required. This is the whole conclusion.

Source check: the literature checkout is absent here. Read the rendered tags and
fetched the actual Stacks algebra.tex, coherent.tex and divisors.tex into this item's
scratchpad, with no changes to the repository. Algebra's conventions explicitly allow
commutative rings with identity including the zero ring. At
`lemma-finitely-presented-localization-free` (Tag [0GWM](https://stacks.math.columbia.edu/tag/0GWM)),
finitely presented modules free at a prime become free on a principal neighbourhood.
The node applies this on Noetherian affines, where its finite modules are finitely
presented. At `lemma-coherent-Noetherian`
(Tag [01XZ](https://stacks.math.columbia.edu/tag/01XZ)), the surrounding text and lemma
assume a locally Noetherian scheme; coherence yields the required finite affine modules.
At `lemma-torsion-free-over-regular-dim-1`
(Tag [0CC4](https://stacks.math.columbia.edu/tag/0CC4)), regularity, integrality and the
dimension bound are used to establish freeness of stalks. They are not additional
assumptions of the subsequent free-stalk criterion reviewed here. No omitted ambient
hypothesis or node fault was found.

Edge cases: the zero sheaf is allowed, with rank-zero local bases (Fin 0 is allowed in
coherence and finite empty generator sets in finite local freeness). On an empty scheme,
the stalk hypothesis is vacuous and the empty covering is allowed by CoversTop; no
Nonempty binder occurs. The zero affine ring therefore causes no excluded case.
Disconnected schemes can have different finite ranks on different components, including
rank zero. There is no characteristic restriction, bound on dimension, global rank, or
finite-cover hypothesis. Universe u is explicitly declared and arbitrary; X.Modules is
the recorded universe-u module carrier. The covering can be indexed in Type u: the
site of opens has that universe, and LocalGeneratorsData.shrink explicitly shrinks any
cover to a subset of its opens. Thus the three explicit universe arguments on the
conclusion introduce no restriction beyond the dependency's carrier convention.

Independent searches (different queries from the worker's) with msearch.py:

- LeanSearch: `finite presentation sheaf free at every point locally free`.
  Service returned Internal Server Error, recorded unavailable; no verdict inferred.
- LeanFinder: `locally free sheaf criterion all stalk modules have finite bases`.
  Eight results, all generator/free-section data and finite-type constructions; none
  asserts the scheme-wide coherent free-stalk criterion.
- Grep: `locallyFree.*stalk|stalk.*locallyFree|freeLocus|exists_free_localizedModule`.
  Eighteen Mathlib hits, pointing chiefly to the affine module free locus and
  localization lemmas. Opened `freeLocus_eq_univ_iff`: it characterizes projectivity
  of a finitely presented ring module, not this sheaf statement.
- Direct rg in WeilConjectures/ and repository lean/Sheaf with
  `stalk.{0,100}(free|basis)|(free|basis).{0,100}stalk|coherent.{0,80}locally.?free`
  found related generic-stalk and fixed-rank results, but no exact criterion. Opened
  `Scheme.Modules.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq`: it concerns Spec R,
  quasi-coherent modules, flat finitely presented global sections and a fixed rank;
  it is not this node's arbitrary-scheme statement with possibly varying ranks.
- Full theorem name and node ID searches in Mathlib, WeilConjectures/, lean/Sheaf,
  and dag/lean_names_upstream.json found no declaration or name collision.

No new definition nodes or dependency modules were supplied or needed; all recorded
statement dependencies are usable as read. There is no statement correction, hence no
corrected-statement citer verdict to inspect. H5/H6: the delivery introduces no
unsupported definition and proves nothing; its only theorem ends in `by sorry`.
H8/H9: both source docstrings carry the item's blueprint ID, and the theorem docstring
matches all three proof steps and their named dependencies. The four imports respectively
supply coherence, locally Noetherian schemes, the canonical module-stalk action, and
finite local freeness. All Lean lines fit 100 characters; all variables and the universe
are bound. The node's lean.statement is verbatim the file's signature.

Validation: scompile.py compiled the unchanged module on the server in 2.2 seconds,
exit code 0, with no warnings or errors. The second reading changes only this report.

## Review fix by R-cfs1201

The stalk hypothesis wrote F_x as the bare abelian stalk `↑(TopCat.Presheaf.stalk F.val.presheaf x)`
with Mathlib's module instance. The stalk of an O_X-module is the landed
`AlgebraicGeometry.RingedSpace.moduleStalkFunctor` (def-pc-module-stalk-functor; one definition per
notion, H4), so `hfree` now reads `Module.Free (X.presheaf.stalk x)
((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ∧ Module.Finite ...`, importing
`Sheaf.Algebra.Homology.ModuleStalkFunctor` in place of `Mathlib.Algebra.Category.ModuleCat.Stalk`.
The mathematical content is unchanged (the functor's object is the same stalk with the germ action).
Everything else matched the node: arbitrary scheme, `[IsLocallyNoetherian X]` (node says locally
Noetherian), `RingedSpace.IsCoherent X.toRingedSpace F`, varying-rank `IsFiniteLocallyFree`
(def-sc-finite-locally-free-sheaf allows the r_i to vary); edge cases (empty scheme, zero sheaf,
disconnected X) fine. The fixed file compiled clean for L.
