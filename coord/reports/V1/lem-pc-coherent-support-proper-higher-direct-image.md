## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` states
`AlgebraicGeometry.isCoherent_schemeModuleHigherDirectImage_of_support_proper`, with its
only proof `sorry`. It defines no new notion and changes only the item's `lean` record.

Clause-by-clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`.
- S locally Noetherian: `[IsLocallyNoetherian S]`.
- The morphism f : X → S: `(f : X ⟶ S)`.
- f locally of finite type: `[LocallyOfFiniteType f]`. No properness, quasi-compactness,
  or separatedness is imposed on f.
- The O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
- F coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- Its support proper over S: `(hSupport : Scheme.Modules.HasSupportProperOver f F)`.
  This recorded dependency expresses closedness of the nonzero-stalk locus and properness
  of its reduced induced closed subscheme over S.
- Every integer p ≥ 0: `(p : ℤ) (hp : 0 ≤ p)`.
- R^p f_*F: `(schemeModuleHigherDirectImage f p).obj F`, using the recorded functor
  that places F in degree zero, applies Rf_*, and takes its p-th cohomology sheaf.
- Coherent O_S-module conclusion:
  `RingedSpace.IsCoherent S.toRingedSpace ((schemeModuleHigherDirectImage f p).obj F)`.

The two `HasDerivedCategory` binders use exactly the shared module-sheaf categories required
by the dependency's signature, with explicitly bound independent morphism universes wX
and wS. These supply the chosen derived-category constructions, not additional geometric
hypotheses. All variables and universes are explicitly bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.Modules.HasSupportProperOver`, whose definition uses
  `AlgebraicGeometry.Scheme.IsClosedSubsetProperOver`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeModuleHigherDirectImage`, built from
  `schemeHigherDirectImage` and `schemeDerivedDirectImage`.

Edge cases checked before writing: p = 0 is included; positive degrees are included without
an upper bound; negative degrees are excluded precisely by hp. F = 0 and X empty have empty
support and remain covered. S empty is also permitted. A nonproper f with proper support is
covered; no assumption that all of X is proper over S is introduced. The proper-f case
recovers the usual proper coherence assertion. No nonemptiness or field restriction occurs.

Source verification: the literature file is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/08DS. Its statement agrees exactly with the node.
The current web numbering is Lemma 30.26.10, rather than the node's old 30.11.3; the stable tag
and label identify the same statement. The source proof uses the support factorization,
proper coherence, affine closed-immersion acyclicity, and Leray, as in the module docstring.
This numbering discrepancy requires no statement correction.

Searches for an existing statement (all through the designated msearch.py where applicable):

- LeanFinder: `coherent sheaf support proper over base coherent higher direct image`.
  Returned general support/preimage and sheaf-pushforward declarations, including
  `Scheme.Hom.range_subset_ker_support` and `Functor.sheafPushforwardCocontinuous`;
  none is the coherent proper-support higher-direct-image statement.
- Loogle: `IsCoherent, schemeModuleHigherDirectImage`: zero hits, unknown identifier
  `IsCoherent`.
- LeanSearch: `higher direct image coherent sheaf proper support`: service unavailable,
  Internal Server Error. No negative mathematical verdict is inferred from this failure.
- Mathlib grep: `higherDirectImage|support.*[Pp]roper|[Cc]oherent` in AlgebraicGeometry,
  and the narrower `higherDirectImage|support.*[Pp]roper`: the latter returned only an
  unrelated module-docstring line in Morphisms/Basic.lean; no matching theorem.
- Project/source rg: `coherent.*support|support.*proper|schemeModuleHigherDirectImage|coherent_higher`
  in WeilConjectures and lean/Sheaf: found the dependency definitions, support lemmas,
  and source `isQuasicoherent_higherDirectImage`. Read the source DirectImage.lean
  `isFinitePresentation_higherDirectImage` signature and docstring: it assumes f proper,
  so it does not state this proper-support result for a locally finite type f.
- Source grep for the exact item id: no match.
- Upstream name index rg: only `lem-pc-projective-coherent-higher-images`, not this item.
- Exact proposed declaration-name rg in Mathlib, WeilConjectures and lean/Sheaf: no match.

No statement dispute, new node, or unusable dependency was found. Server scompile passed
with exit code 0 in 2.1 seconds and no warnings.

## Second reading by V1

I independently read the item node, its three proof steps, the delivered Lean, and every
statement dependency's node and recorded declaration. No mathematical or Lean mismatch
was found, so the module and node record are unchanged.

Objects, hypotheses, and conclusion (each verdict: exact):

- Schemes X and S: `{X S : Scheme.{u}}`, arbitrary schemes in an arbitrary universe.
- S locally Noetherian: `[IsLocallyNoetherian S]`. I opened Mathlib Noetherian.lean:
  the class requires Noetherian section rings on affine opens, equivalent to the node's
  affine-cover definition. It does not require global Noetherianness.
- Morphism f from X to S: `(f : X ⟶ S)`.
- Locally finite type f: `[LocallyOfFiniteType f]`. I opened Mathlib FiniteType.lean:
  its affine-pair finite-type condition is the recorded dependency's local notion;
  no quasi-compactness, separatedness, or properness of f is assumed.
- O_X-module F: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`, the shared
  category used by both coherent modules and derived direct image.
- Coherence of F: `hF : RingedSpace.IsCoherent X.toRingedSpace F`. I opened Coherent.lean:
  finite type and finite-type kernels of all maps from finite free modules on every open,
  exactly the coherent clause of pqf-def-coherent, including rank zero.
- Support proper over S: `hSupport : Scheme.Modules.HasSupportProperOver f F`.
  I opened ClosedSubsetProperOverBase.lean: its existential closed subset equals exactly
  `{x | ¬ Subsingleton (F.presheaf.stalk x)}` and its reduced induced closed subscheme
  is proper over S. This is the dependency node's full support condition, not properness
  of X or of an unrelated subset.
- Every nonnegative integer p: `(p : ℤ) (hp : 0 ≤ p)`, after f and F, with no bound above.
- R^p f_*F: `(schemeModuleHigherDirectImage f p).obj F`. I opened
  SchemeDerivedDirectImage.lean and DerivedCategory.lean: singleFunctor places F in
  degree zero, the shared ringed-space derived direct image applies Rf_*, and
  homologyFunctor takes degree p. No independent higher-direct-image definition appears.
- Conclusion: `RingedSpace.IsCoherent S.toRingedSpace` of that same higher direct image;
  the entire coherence condition is asserted, not merely quasi-coherence or finite type.
- The two HasDerivedCategory instances use the exact shared categories of the dependency
  and independently bound wX and wS. They specify localization constructions rather than
  additional geometric conditions. All universe and term variables are explicitly bound;
  no fixed characteristic, ground field, or extra Noetherian hypothesis occurs.

Source reading: local Stacks .tex is absent. I fetched upstream coherent.tex into the
sandbox scratchpad and read section-proper-over-base, definition-proper-over-base,
its surrounding paragraphs, lemma-module-support-proper-over-base, and
lemma-support-proper-over-base-pushforward. I also opened
https://stacks.math.columbia.edu/tag/08DS. The source has precisely the hypotheses above;
no standing hypothesis adds quasi-compactness or separatedness of f. The support
terminology presupposes locally finite type f, already present. Current numbering is
30.26.10; the stable Tag 08DS and lemma label agree. The three docstring proof steps
match the node: factor through a proper closed subscheme, use closed-immersion affine
acyclicity and derived composition, then obtain local Noetherianness and coherence on Z
and apply proper coherence. No statement correction or citer review is needed.

Edge cases: p = 0 and every positive degree are included; negative degrees are excluded
exactly as in the source. Zero F and empty X have empty support and are allowed. Empty S
is allowed (a morphism to it forces empty X); no nonemptiness is imposed. There is no
index set or characteristic restriction. Nonproper f with proper support is allowed.
The arbitrary scheme universe and shared module universe follow the dependency nodes;
the derived morphism universes are arbitrary and independent. No new definition node
or dependency module is present or necessary. There are no hollow definitions, private
notions, local notation, or proofs beyond the single named theorem with `sorry`.

Independent searches, using different terms from the worker:

- LeanFinder via msearch.py: `finitely presented module sheaf direct images nonproper
  morphism proper nonzero stalk locus`; eight hits, all finite-presentation definitions
  and local finite presentation, none states the proper-support assertion.
- Loogle via msearch.py: `IsProper, SheafOfModules`; zero hits, unknown identifier IsProper.
- LeanSearch via msearch.py: `finiteness of cohomology of a coherent module supported on
  a proper closed subscheme`; service unavailable (Internal Server Error), not a
  mathematical negative result.
- rg on Mathlib AlgebraicGeometry, WeilConjectures, and repository lean/Sheaf:
  `support.*[Pp]roper|[Pp]roper.*support|[Cc]oherent.*[Dd]irect|[Dd]irect.*[Cc]oherent`.
  Read the shared proper-support definitions and the upstream higher-direct-image
  finiteness theorem in DirectImage/FiniteFreeComplex.lean. The latter assumes proper f
  in its surrounding section and states finite presentation, not this assertion for
  merely locally finite type f. Related étale compact-support theorems are different
  categories and coefficient sheaves. No existing exact statement was found.
- rg for the proposed declaration and exact blueprint id in WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no match. Thus existing:true would be incorrect.

Changes: only this second-reading section was appended. The worker's report remains.
The recorded lean.statement matches the theorem signature verbatim. Server compilation
and delivery preflight are checked using the prescribed scripts below.

Verification outcome: the first scompile invocation encountered a temporarily missing
server V1 build artifact for SchemeDerivedDirectImage. The subsequent prescribed delivery
dry run compiled successfully and printed OK (commit 888b2583e), with all preflight checks
passing. No source workaround or replacement definition was needed.
