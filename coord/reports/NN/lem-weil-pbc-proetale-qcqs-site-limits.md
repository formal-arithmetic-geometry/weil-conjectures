## Worker report

The delivery states `AlgebraicGeometry.Scheme.ProEt.qcqs_site_limits` in
`Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`. Its only proof is `sorry`.
`Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite` supplies concrete definitions of
its category, inclusion, and finite covering precoverage. No data is postponed.
The natural statement is unchanged. No statement dispute or dependency fault was found.

Hypothesis and clause correspondence:

- An arbitrary scheme X is `(X : Scheme.{u})`, with explicitly declared universe u.
  Mathlib's `X.ProEt` and `ProEt.precoverage X` are the small pro-etale category
  and its prescribed covering families. These are the same objects and covers
  used by the recorded dependency `Scheme.proEtaleDerivedCategory`.
- The size convention is rendered by `universe u`, schemes in `Scheme.{u}`, and
  the resulting category of objects in `Type (u+1)` with homs in `Type u`.
  All categories are sets in a larger universe; no cardinal restriction or
  independent test-object universe is imposed. The full category presentation
  is equivalent to the permitted choice of skeleton.
- The full subcategory C on qcqs source schemes is `ProEt.Qcqs X`, the
  `ObjectProperty.FullSubcategory` of `qcqsObjects X`. Its predicate is exactly
  `CompactSpace U.left ∧ QuasiSeparatedSpace U.left`, referring to U itself,
  rather than to quasi-compactness of its structure morphism over an arbitrary X.
- Finite pro-etale covering families are `qcqsPrecoverage X`, the intersection
  of `(precoverage X).comap (qcqsInclusion X)` with `Precoverage.finite (Qcqs X)`.
  The latter requires a finite set of arrows after uncurrying a presieve. Every
  finite family gives such a presieve; every such presieve is represented by its
  finite set of arrows. Repetitions do not affect either fpqc covering or the
  node's convention of reindexing coverings.
- “C is a site” is the first four conjuncts: `HasIsos`,
  `IsStableUnderComposition`, `IsStableUnderBaseChange`, and `HasPullbacks`
  of this precoverage. These are the four site structures explicitly specified
  by the recorded `def-weil-pbc-sites-and-cohomology` Lean note.
- “Has fibre products” is `HasPullbacks (Qcqs X)`.
- “Computed as scheme fibre products” is preservation of `WalkingCospan`
  limits by `qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X`.
  This functor lands in Scheme and forgets only the structure arrows.
- “Inclusion preserves fibre products” is preservation of `WalkingCospan`
  limits by `qcqsInclusion X` itself, landing in `X.ProEt`.
- “Sends coverings to coverings” is the explicit quantification over T and R,
  taking membership in `qcqsPrecoverage X T` to membership of
  `R.map (qcqsInclusion X)` in the full small-site `precoverage X`.
- “For every T, C/T has finite limits” is `∀ T : Qcqs X,
  HasFiniteLimits (Over T) ∧ ...`.
- “Computed as scheme limits over T” is `PreservesFiniteLimits` of
  `Over.post (X := T) (qcqsInclusion X ⋙ ProEt.forget X) ⋙
  Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T)`.
  `Over.post` sends the slice to `(Scheme/X)/(T/X)` and
  `iteratedSliceForward` sends it to `Scheme/T.left`; thus the target is the
  intended slice, including the terminal object T.
- “If X itself is qcqs” is the implication
  `CompactSpace X → QuasiSeparatedSpace X → ...`; this is a conclusion
  conditional on X, not a restriction on the preceding clauses.
- Its two conclusions are `HasFiniteLimits (Qcqs X)` and preservation of
  finite limits by `qcqsInclusion X ⋙ ProEt.forget X`, into `Scheme/X`.
- “Adjoining finitely many arrows with the same target” quantifies T and
  presieves R and S on T; R is a covering and S belongs to the finite
  precoverage. The conclusion `R ⊔ S ∈ qcqsPrecoverage X T` says exactly that
  their union is a cover. The added arrows need not themselves cover T.

Dependencies read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`; its source identifies its site as Mathlib's
  `Scheme.ProEt` and `ProEt.topology`. We import this recorded dependency and
  reuse `ProEt.precoverage`, `ProEt.forget`, and the actual site objects.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.proetalePrecoverage`,
  `ProEt`, `ProEt.precoverage`, `ProEt.forget`. The covering dependency is a
  Mathlib leaf, so it needs no replacement Lean record.
- `Mathlib.CategoryTheory.Sites.Precoverage`: `Precoverage`, `HasIsos`,
  `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`, and
  `comap`, as specified by the sites-and-cohomology dependency's Lean record.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  its projections; the general fibre-product notion is used through
  `HasPullbacks` and preservation of `WalkingCospan` limits.
- The two convention dependencies have no declaration/module; their recorded
  notes prescribe universes and the Mathlib scheme-property classes used here.
- Proof imports include `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
  (`WeaklyEtale.of_comp`, composition/base-change instances),
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (quasi-compact and
  quasi-separated permanence), `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
  (the recorded permanence leaf's remaining clauses), and
  `Mathlib.CategoryTheory.MorphismProperty.Limits` (pullback stability).
  The theorem docstring carries all four original proof steps and names their
  DAG inputs. No proof dependency import is omitted for a cycle.

Edge cases checked before writing:

- X is arbitrary, including empty and non-qcqs schemes. No terminal object or
  unrestricted finite-limit assertion is made for C unless X is qcqs.
- Empty finite diagrams in C/T have terminal object T. Limits are preserved in
  Scheme/T, not in Scheme (which would incorrectly send T to Spec Z).
- An empty cover is permitted exactly when its underlying full-site family
  covers; the finite precoverage includes the empty presieve. The proof of
  adjoining arrows retains all original witnesses, including the empty-target
  case. S may be empty and need not be a cover.
- Equalizers use the diagonal construction through V ×_T V, with all intermediate
  objects qcqs. No unjustified quasi-compact diagonal of the arbitrary base X
  is used. The conditional global finite-limit clause includes X/X.
- Index sets are not fixed to a chosen cardinal: the finite-arrow presieve
  presentation covers arbitrary finite index types, including repetitions.

Searches performed (all against read-only sources):

- `msearch.py ... leanfinder "quasi compact quasi separated small pro etale site
  finite limits"`: eight hits, including the etale-site declarations and
  `QuasiCompactCover.of_finite`; none is this qcqs subsite or lemma.
- `msearch.py ... loogle "CategoryTheory.Limits.HasFiniteLimits,
  CategoryTheory.ObjectProperty.FullSubcategory"`: four hits including generic
  full-subcategory finite-limit instances; no pro-etale qcqs specialization.
- `msearch.py ... grep "[Qq]cqs|[Qq]uasi[Cc]ompact.*[Ss]ite"
  AlgebraicGeometry`: 24 hits in unrelated qcqs geometry, none defines this site.
- For the new definition, `leansearch` query "quasi compact quasi separated pro
  etale full subcategory finite covering precoverage" was unavailable (Internal
  Server Error). `leanfinder` with the identical query returned eight hits
  on quasi-compact covers and the etale topology, no matching definition.
- `msearch.py ... grep "qcqs.*[Pp]ro|[Pp]ro.*qcqs"`: zero Mathlib hits.
- `rg` of qcqs/subsite and pro-etale/qcqs combinations in the DAG,
  `lean/Sheaf`, the exact `lean/WeilConjectures` framework, and upstream
  `WeilConjectures` found related lemmas but no definition of this subsite.
  `blueprint_refs.py search 'qcqs pro'` returned zero blueprint matches.
  Searches for the chosen declaration names in all source trees and
  `dag/lean_names_upstream.json` found no collision.
- Read Stacks `proetale.tex`, `lemma-w-contractible-hypercovering` (Tag 09A1),
  including the exact qcqs subsite paragraph, and `lemma-fibre-products-proetale`
  (Tag 098M). The framework document `coord/pefw-upstream-framework.md` was read;
  the existing Mathlib small-site geometry suffices, so no alternate coefficient
  or pro-etale objects have been introduced.

Validation: both delivered files compiled separately, in dependency order,
through `scompile.py` on the server: 1.3 s and 1.4 s, respectively, nice 19,
two threads, 60 seconds per file; no errors or warnings were printed.

## New nodes

`def-weil-pbc-proetale-qcqs-subsite` defines the qcqs full subcategory of X.ProEt,
its inclusion, and the precoverage of finite pro-etale covers. Source: Stacks
Project Tag 09A1, qcqs subsite paragraph in the proof of
`lemma-w-contractible-hypercovering`. No existing DAG definition carries this
notion: the parent and neighboring nodes use it only in lemma statements.
The three search kinds and direct project/framework searches above found no
specialized declaration. Mathlib's full-subcategory construction and finite
precoverage are reused instead of copied. The module consists entirely of
concrete definitions; no auxiliary theorem or hollow data definition is added.

## Second reading by NN

I read the item's node, both sandbox modules, the new definition node, all seven
original statement dependencies and all proof-dependency records. I read Stacks
`proetale.tex`, the entire qcqs paragraph in the proof of
`lemma-w-contractible-hypercovering` (09A1), and `lemma-fibre-products-proetale`
(098M), including the surrounding hypotheses. Both start with an arbitrary
scheme; neither imposes Noetherianity, separatedness, a field, or nonemptiness.
I also read the exact group-clone pro-etale `Proetale/Basic.lean` and
`coord/pefw-upstream-framework.md`. The framework uses the same Mathlib `ProEt`
category; no alternative pro-etale category is needed here.

Clause-by-clause inventory and verdict for the repaired signature:

1. Object and size: `X : Scheme.{u}` with explicit `universe u` is an arbitrary
   scheme in the objects' universe. `Scheme.ProEt`, read in Mathlib
   `Sites/Proetale.lean`, is `MorphismProperty.Over @WeaklyEtale ⊤ X`, with all
   scheme morphisms over X. This is precisely the small pro-etale site of the
   recorded dependency `Scheme.proEtaleDerivedCategory`. The universe-polymorphic
   full-category presentation is equivalent to choosing its small skeleton in a
   larger universe. Verdict: matches, with no extra geometric hypothesis.
2. Category: `Qcqs X = (qcqsObjects X).FullSubcategory`, where the predicate is
   `CompactSpace U.left ∧ QuasiSeparatedSpace U.left`. Thus qcqs refers to the
   source scheme, not its map to the possibly non-qcqs base. The inclusion is
   `(qcqsObjects X).ι`. Verdict: exactly the full subcategory in 09A1.
3. Coverings: `qcqsPrecoverage X` is the comap of `ProEt.precoverage X` along
   `qcqsInclusion X`, intersected with `Precoverage.finite (Qcqs X)`.
   I read `Precoverage.comap`, `Precoverage.finite`, and
   `Precoverage.ofArrows_mem_finite`: these express exactly finite sets of
   covering arrows, and represent all finite families after removing repetitions.
   `ProEt.precoverage` is the comap of `Scheme.proetalePrecoverage`, namely fpqc
   weakly etale covers. Verdict: matches the prescribed finite covers.
4. Site and fibre products: the repaired statement starts
   `∃ h : HasPullbacks (Qcqs X), ∃ J : @Pretopology (Qcqs X) inferInstance h,
   J.toPrecoverage = qcqsPrecoverage X ∧ ...`. `Pretopology` supplies precisely
   singleton-isomorphism covers, pullback covering presieves, and compositions
   with a finite cover for each arrow. The equality fixes its covers exactly,
   rather than merely generating a topology containing them. The witness h
   supplies all fibre products. Verdict: matches after the repair described below.
5. Computation and preservation: `PreservesLimitsOfShape WalkingCospan` for
   `qcqsInclusion X` and for
   `qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X` gives respectively
   preservation into the full small site and computation in schemes. Verdict:
   both clauses present, with their intended codomains.
6. Cover preservation: for every `T : Qcqs X` and `R : Presieve T`, membership
   in `qcqsPrecoverage X T` implies membership of `R.map (qcqsInclusion X)` in
   `precoverage X ((qcqsInclusion X).obj T)`. Verdict: matches every cover.
7. Slice limits: for every `T : Qcqs X`, `HasFiniteLimits (Over T)` and
   `PreservesFiniteLimits (Over.post ... ⋙ Over.iteratedSliceForward ...)`.
   I read `Over.post` and `Over.iteratedSliceForward`: their composite takes an
   arrow to T to the underlying scheme arrow to T.left, landing in Scheme/T.left.
   Verdict: precisely finite limits over T, including the terminal object T.
8. Qcqs base: `CompactSpace X → QuasiSeparatedSpace X →` precedes only
   `HasFiniteLimits (Qcqs X) ∧ PreservesFiniteLimits
   (qcqsInclusion X ⋙ ProEt.forget X)`. Verdict: the extra hypothesis applies
   exactly to the global finite-limit clause, computed in Scheme/X.
9. Adjoining arrows: for every T and presieves R,S on it, R is a cover and S
   is finite; `R ⊔ S` remains in `qcqsPrecoverage X T`. Verdict: matches;
   S need not cover and may be empty. No reversed quantifiers or extra condition.

Mismatch repaired (H3): the worker used
`qcqsPrecoverage.IsStableUnderBaseChange` and `.IsStableUnderComposition`.
Mathlib explicitly documents these classes as stronger than the corresponding
`Pretopology` axioms. They quantify over arbitrary indexed presentations of a
presieve, not only its finite set of arrows. An infinite repetition of one arrow
can present a finite presieve; choosing distinct isomorphic pullback objects for
those repetitions can produce infinitely many distinct pullback arrows.
Similarly, different finite covers for infinitely many repetitions can have an
infinite union. Finiteness of the starting presieve does not imply finiteness of
those outputs. This explains why Mathlib provides `Pretopology.finite`, but no
corresponding stability instances for `Precoverage.finite`.

I replaced the first four classes and the separate pullback conjunct by an
existential pullback structure and an actual Mathlib pretopology with exactly
the prescribed covering precoverage. All remaining clauses are unchanged. I
updated the proof-plan docstring to explain this distinction and copied the
complete new signature verbatim into `lean.statement`. The natural-language
node already says the right thing, so no node statement correction or citer
change is needed. The earlier worker-report claim that these four classes render
the site clause is superseded by this second reading. The generic sites node's
Lean note prescribes the stronger four-class precoverage encoding. That encoding
is unsuitable for finite presieves, for the reason above; its underlying recorded
`Precoverage` is reused as the covering collection, and Mathlib's existing
`Pretopology` supplies the literal three axioms. This is a defect of that encoding
for this application, not a different mathematical site notion. No private
replacement definition or dependency module is needed.

New-node review (H12): `def-weil-pbc-proetale-qcqs-subsite` introduces exactly
09A1's qcqs full subcategory, full inclusion, and finite covering families. Its
six statement dependencies are exactly its bracket citations; all are existing
scheme/site/size/covering notions. Its kind, split status, chapter/unit, source,
empty proof/proof_deps, null proof_origin/mathlib_match, creation record and
empty audit states meet the new-definition field rule. `blueprint_refs.py ancestor`
confirms `thm-weil-pbc-qbar`. Related DAG nodes assert properties of this subsite;
none already defines it. The module reuses Mathlib's generic full subcategory,
comap, intersection and finite-precoverage constructions. All four bodies are
concrete; there is no `sorry` in data. No dependency module was delivered.

Independent searches, with queries different from the worker's:

- `leanfinder`: "weakly etale schemes with compact quasi separated source slice
  finite limits" returned eight etale-site/property results, no matching category
  or theorem.
- `loogle`: `CategoryTheory.Precoverage.finite` returned five results, including
  the generic finite precoverage and finite pretopology. I opened both and used
  their distinction to repair the theorem.
- `leansearch`: "full subcategory quasi compact quasi separated weakly etale
  schemes finite pretopology" was unavailable (Internal Server Error).
- Direct `rg` searches of Mathlib, upstream WeilConjectures, the exact group-clone
  WeilConjectures framework, and `lean/Sheaf` for proet/qcqs combinations,
  quasi-compact quasi-separated subcategories, and the four proposed names found
  no existing specialized subsite or statement. The sole broad subsite hit in
  `DerivedQCohCompactGeneration.lean` concerns a different geometric setting.
  Searches in dag/nodes found the related qcqs geometry statements but no
  competing definition node. The upstream name index has no name collision.

Edge cases: empty X and empty site objects are included; the empty family is a
cover exactly when the underlying pro-etale precoverage permits it. Empty added
presieves are allowed. Removing repetitions does not affect finite-family
coverage. The repaired site clause no longer inadvertently quantifies finiteness
over infinite repeated presentations. The empty finite diagram in C/T maps to T
in Scheme/T, not to the terminal scheme Spec Z. For non-qcqs X no terminal object
of C is asserted. All finite-limit shapes and scheme universes remain those of
Mathlib; no independent small universe of test schemes is introduced. There are
no coefficient, characteristic, or positive-integer hypotheses to exclude zero
or positive-characteristic cases.

All original proof steps occur in the theorem docstring: weakly-etale and qcqs
permanence for fibre products; the three site axioms; terminal objects, products
and the diagonal construction of equalizers for slice/global finite limits;
retaining the fpqc witnesses after adjoining arrows. The generic permanence
matches were read in Mathlib and their proof imports remain. There is one named
theorem with proof `sorry` and no other theorem or proved auxiliary statement.
Docstrings identify the source tags and their respective blueprint nodes. No
file-local notation, private definition, unbound variable, or universe remains.

Validation after repair: both delivered modules compiled separately through
`scompile.py` on the server, nice 19, two threads, 60 seconds per file; 1.4 s and
1.5 s, with no errors or warnings. The new definition module needed no change.
