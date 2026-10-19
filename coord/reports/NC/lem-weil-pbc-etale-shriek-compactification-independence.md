## Worker report

Existing declaration family; no Lean module is added. The main construction is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` (lines 194–207).
The recorded module `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
publicly imports that module and supplies all the coherence clauses. All five
recorded declarations were read with their full signatures, surrounding binders,
and docstrings. The node is unchanged except for `lean`.

Clause-by-clause matching:

- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  The coefficient category is `ModuleCat.{u + 1} Λ`; the derived categories are
  `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and
  the corresponding category for Y. These are precisely the bounded-below
  small-etale module-sheaf categories in the dependency record.
- Schemes and morphism: `{X Y : Scheme.{u}} {f : X ⟶ Y}`. The existing results
  assume `[QuasiCompact f]` and are valid more generally than the node's setting.
  A finite-type morphism is quasi-compact, so no extra hypothesis is needed.
  Quasi-compactness and quasi-separatedness of both schemes, and separatedness
  and finite type of f, may all be supplied as in the node; they do not restrict
  any additional parameter in the recorded result. This is a reuse of a general
  existing theorem, not a newly strengthened or weakened statement.
- Compactifications: `(c d : Compactification f)` supplies Z, proper g, open
  immersion i, and `comm : f = i ≫ g`. The definition has no density requirement.
  Although its open immersion is not required quasi-compact in general, in this
  setting `Compactification.quasiCompact_openImmersion` supplies exactly this
  condition from `[QuasiCompact f]`. Thus its objects here are exactly the node's
  compactifications, not a specialization or enlargement of them.
- Candidate functor Rp_* j_!: `rightDerivedLowerShriekOfCompactificationPlus`
  is definitionally `D+(openImmersionLowerShriek _ c.i) ⋙ R+(lowerStar _ c.g)`.
  The unbounded analogue named by the projection-compactification dependency
  is not substituted for the required bounded-below functor.
- Natural comparison: `rightDerivedLowerShriekOfCompactificationPlusIso Λ c d`
  is a natural isomorphism of these functors, constructed from their common
  refinement `Compactification.inf c d`.
- Independence of common refinement, including its arrows: the theorem
  `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`
  quantifies over `{c d e : Compactification f}`, `r : e.Refinement c`, and
  `s : e.Refinement d`, with no cartesian or density condition, and identifies
  the canonical comparison with `RefinementIso Λ r ≪≫ (RefinementIso Λ s).symm`.
  Consequently every such pair gives the same comparison. The earlier theorem
  `...PlusIso_eq` requiring cartesian squares was deliberately not used as the
  record of this clause.
- Identity for equal compactifications: `...PlusIso_refl (c : Compactification f)`
  says `PlusIso Λ c c = Iso.refl _`.
- Cocycle for triples: `...PlusIso_trans (c₁ c₂ c₃ : Compactification f)` says
  `PlusIso Λ c₁ c₂ ≪≫ PlusIso Λ c₂ c₃ = PlusIso Λ c₁ c₃`.

Dependencies read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-scheme-conventions`: convention-only record, no declaration;
  its quasi-compact, separated, finite-type, and proper notions are Mathlib's.
- `def-weil-pbc-projection-compactification`:
  WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, and its
  bounded-below counterpart `rightDerivedLowerShriekOfCompactificationPlus`.
- `def-weil-pbc-extension-by-zero`:
  WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs,
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-pbc-direct-image`:
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  `AlgebraicGeometry.Etale.lowerStar`, and
  WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` (the recorded name is
  defined here and re-exported through the derived direct-image imports).
- `def-weil-pbc-derived-categories`:
  Sheaf.AlgebraicGeometry.DerivedCategories, the documented existing
  `DerivedCategory.Plus` on module-valued sheaves. Its torsion predicate is not
  needed: for a finite coefficient ring all these coefficients are torsion.

Also read `Compactification` in WeilConjectures.Compactification.Defs,
`Compactification.Refinement` in WeilConjectures.Compactification.Refinement,
and the source Stacks `more-etale.tex`, label `lemma-shriek-well-defined`
(Tag 0F7I), including the cofiltered comparison proof. The existing declaration
family covers the source's finite-ring bounded-below specialization and every
clause of this node. No dependency repair or new definition is needed.

Edge cases checked: the empty source scheme is allowed; compactifications need
not have dense open image; common refinements need not be cartesian over X;
the zero ring and zero complexes are allowed; proper f allows its identity
compactification. No nonzero-ring, nonempty-scheme, positive-degree, or
characteristic hypothesis occurs. The index-free statement introduces no
universe restriction on a family of test schemes. Λ in Type (u+1) and
ModuleCat.{u+1} match the dependency encoding.

Searches:

- msearch.py leanfinder, query "derived compactly supported direct image
  independent of compactification natural isomorphism cocycle": eight unrelated
  compactly supported continuous-map and condensed-set hits; no Mathlib match.
- msearch.py loogle, query "AlgebraicGeometry.Compactification, CategoryTheory.NatIso":
  zero hits, unknown identifier AlgebraicGeometry.Compactification (an upstream,
  not Mathlib, notion).
- msearch.py grep, query "shriek|compactification" in CategoryTheory: zero hits.
- rg in the upstream SixFunctors/Etale/Derived tree for independence and
  compactification isomorphisms: found LowerShriekIndependence and
  LowerShriekCoherence; their actual declaration signatures were then read.
- rg for the node id throughout upstream WeilConjectures: no tagged declaration.
- rg for CompactificationPlusIso and compactification independence in lean/Sheaf:
  no competing declaration; the upstream family supplies the result.

Validation repair (2026-10-15): the server existing-declaration probe now passes.
Preflight identified that the former primary declaration was re-exported rather
than defined in the recorded module. The primary declaration is now
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`,
whose verbatim signature is recorded from LowerShriekCoherence. The declaration
family still includes the construction, refinement comparison, identity and
cocycle, so no mathematical clause changed. No new module, dependency repair,
statement correction, or disputed statement. Independent second reading remains
for the next worker; this worker does not supply that section.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node, Stacks more-etale.tex at
lemma-shriek-well-defined (0F7I), and the actual upstream declarations,
including their enclosing variable binders. No mathematical mismatch was found;
the existing record and the natural statement are unchanged.

Object, hypothesis, and conclusion checklist:

1. Finite commutative coefficient ring: `Λ : Type (u + 1)`, `[CommRing Λ]`,
   `[Finite Λ]` in LowerShriekIndependence and LowerShriekCoherence. Verdict: matches.
2. Small-etale module sheaves and bounded-below derived categories:
   `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
   and the analogous category for Y. I read the dependency module
   Sheaf.AlgebraicGeometry.DerivedCategories and the signatures of lowerStar,
   rightDerivedLowerStarPlus and openImmersionLowerShriek. Verdict: same categories
   and functors, with no substitution of the unbounded category.
3. Schemes T,B and h:T→B: `{X Y : Scheme.{u}} {f : X ⟶ Y}`.
   Scheme and Scheme.Hom are Mathlib's recorded objects. The node assumes qcqs
   schemes and separated finite-type h. The existing family only needs
   `[QuasiCompact f]`, which is supplied by finite type. Applying a more general
   existing family to the node's setting adds no hypothesis and loses no case.
   Verdict: applicable to every object and morphism quantified by the node.
4. Compactification c=(j,p), including factorization, proper p and quasi-compact
   open j: `Compactification f` has fields `Z`, `g`, `i`, `comm`, `isProper`,
   `isOpenImmersion`. I read Compactification.Defs: the missing explicit
   quasi-compactness field follows from
   `Compactification.quasiCompact_openImmersion (c) (hf : QuasiCompact f)`.
   There is no density requirement. Verdict: same compactification data here.
5. Candidate Rp_* j_!: the dependency's bounded-below declaration
   `rightDerivedLowerShriekOfCompactificationPlus` is definitionally
   `D+((c.i)_!open[A]) ⋙ R+((c.g)_*[A])`. Its unbounded sibling is not used
   in the comparison statements. Verdict: matches.
6. Natural isomorphism for every c,d:
   `rightDerivedLowerShriekOfCompactificationPlusIso Λ c d` has functor-isomorphism
   type, constructed by cartesian comparisons through `Compactification.inf c d`.
   The construction is real data, not a bare chosen Nonempty witness. Verdict: matches.
7. Independence of the common refinement, including both arrows:
   `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso` quantifies
   over arbitrary `{c d e : Compactification f}` and `r : e.Refinement c`,
   `s : e.Refinement d`, and equates the fixed comparison with the ratio of
   the two refinement comparisons. I read Refinement's fields `hom`, `i_hom`,
   `hom_g` and its properness instance. There is no cartesian hypothesis on r,s.
   I also read the real definition of PlusRefinementIso through the dense
   refinement of its source. Verdict: every common refinement and arrow pair
   gives the same comparison; the earlier cartesian-only theorem would not suffice.
8. Identity for equal compactifications: `...PlusIso_refl (c)` states equality
   with `Iso.refl _`. Verdict: matches.
9. Cocycle for triples: `...PlusIso_trans (c₁ c₂ c₃)` states that the first two
   comparisons compose to the third. The same fixed comparison construction
   occurs in all clauses. Verdict: matches, with the required quantifier order.

Source check: 0F7I assumes finite-type separated maps of qcqs schemes and proves
independence by cofiltered compactifications and composition of their comparison
maps. Its torsion-ring argument applies to finite rings, including the zero ring.
The existing family supplies precisely these conclusions in that specialization.
The source's proof and the node's seven-step expanded proof agree: comparison
along refinements, coherent composition, cancellation under further refinement,
equalization of arrow pairs, then identity and the triple cocycle. Existing reuse
adds no new postponed theorem or definition requiring a proof docstring.

Edge cases: empty schemes and nondense compactifications are admitted; the ring
may be zero and complexes may be zero. No characteristic is inverted or excluded.
No degree n is quantified or restricted; all bounded-below complexes are included.
There is no index set to require nonemptiness. The scheme universe u is arbitrary;
the coefficient and module universe u+1 is exactly the recorded derived-category
convention, with no additional equality of site object and morphism universes.

Independent searches (different queries from the worker): msearch leanfinder for
"exceptional direct image bounded below etale module sheaves comparison
compactifications" returned unrelated qcqs section/localization statements;
msearch loogle for `"compactification"` returned zero hits. Direct rg for
`shriek|exceptional.*(image|pushforward)` in Mathlib AlgebraicGeometry and
CategoryTheory returned no match. Direct rg for compactification independence,
PlusIso_eq_refinementIso and PlusIso_trans in upstream and lean/Sheaf located
the recorded upstream family and consumers, with no competing Sheaf statement.
The five recorded declarations and the dependency definitions were opened and
read, rather than inferred from their names. The recorded primary signature is
verbatim the theorem at LowerShriekCoherence lines 442–447.

Changes: appended this independent reading only; no Lean file, node correction,
new node or dependency repair is necessary. No statement_change is present.

Validation blocker: the current launcher scompile.py run_many unconditionally
calls nt_local_compile.run first. That implementation sets LCOMPILE_REMOTE=0
and invokes lc.run locally. deliver2.py uses this run_many even for its existing
#check probe. This conflicts with the dispatcher's explicit server-only/no-local-
compiler instruction. I did not invoke the local compiler, modify the tools, or
work around their contract. The required dry run and push remain pending a
server-only delivery-tool path.


## Second reading by NC

Independent second reading, 2026-10-15. I opened the sandbox node, its six
statement dependencies and their recorded source declarations, Stacks
more-etale.tex (the construction preceding lemma-shriek-well-defined and the
whole proof of that lemma), and the upstream compactification definitions.
The earlier second reading's compiler-policy blocker is superseded by the
human's explicit authorization of scompile.py and deliver2.py.

Object/hypothesis/conclusion checklist (natural statement first):

1. A finite commutative coefficient ring Λ. Lean: the enclosing binders
   `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` in both independence and
   coherence modules. Verdict: matches; no nontriviality or characteristic
   restriction.
2. Bounded-below derived categories of small-etale Λ-module sheaves on T and B.
   Lean: `DerivedCategory.Plus (Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))` and its Y counterpart. I read DerivedCategories.lean
   and the dependency record: this is the shared six-functor encoding, not a
   different SheafOfModules category or the unbounded sibling. Verdict: matches.
3. Schemes T,B and separated finite-type h between qcqs schemes. Lean:
   `{X Y : Scheme.{u}} {f : X ⟶ Y}` and `[QuasiCompact f]`. Finite type supplies
   quasi-compactness; the existing family is more general and applies to every
   case in the node without requiring additional assumptions. Scheme and Hom
   are the recorded Mathlib notions. Verdict: existing reuse is applicable.
4. A compactification (j,p), with quasi-compact open j, proper p and p∘j=h.
   Lean: `Compactification f`, fields `Z`, `i`, `g`, `comm`, `isOpenImmersion`,
   `isProper`. I read Defs.lean: `quasiCompact_openImmersion` derives the missing
   explicit qc field from QuasiCompact f. No density assumption is imposed.
   Verdict: the same compactification data in this setting.
5. Candidate Rh! = Rp* j!. Lean:
   `rightDerivedLowerShriekOfCompactificationPlus` is explicitly
   `D+((c.i)_!open[A]) ⋙ R+((c.g)_*[A])`.
   I read openImmersionLowerShriek (localizationLowerShriek), lowerStar (the
   continuous sheaf pushforward by etale base change), and
   rightDerivedLowerStarPlus (rightDerivedFunctorPlus). Verdict: same functors
   as the extension-by-zero, direct-image and projection dependencies.
6. For each c,d a natural isomorphism of these functors. Lean:
   `rightDerivedLowerShriekOfCompactificationPlusIso Λ c d` has exactly that
   functor-isomorphism type. Its body composes the two actual cartesian
   comparisons through `Compactification.inf c d`, using asIso and inverse.
   Verdict: canonical real construction, not an arbitrary chosen isomorphism.
7. Independence of the common refinement and its arrows. Lean: the primary
   `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`
   quantifies over all `{c d e : Compactification f}`, `r : e.Refinement c`,
   `s : e.Refinement d` and equates the fixed iso to the refinement ratio.
   Refinement has precisely the commuting maps `hom`, `i_hom`, `hom_g`;
   properness is derived. Neither r nor s must be cartesian. I read the actual
   PlusRefinementIso definition through the dense refinement of e, and its
   agreement theorem for cartesian arrows. Verdict: includes arbitrary
   refinements and arrow choices, unlike the earlier cartesian-only Iso_eq.
8. Equal compactifications give identity. Lean: `...PlusIso_refl (c)` gives
   `PlusIso Λ c c = Iso.refl _`. Verdict: matches for the same construction.
9. Triple cocycle. Lean: `...PlusIso_trans (c₁ c₂ c₃)` gives
   `PlusIso Λ c₁ c₂ ≪≫ PlusIso Λ c₂ c₃ = PlusIso Λ c₁ c₃`.
   Verdict: correct order and all triples, for the same fixed comparisons.

Source and proof check: 0F7I assumes separated finite-type maps of qcqs schemes.
The preceding construction allows torsion coefficients; finite Λ makes all
module coefficients torsion, including the zero-ring case. Its proof uses
cofiltered compactifications, proper-open comparison, and compatibility with
composition. The node expands this into seven steps: choose the cofiltered
category; coherent derived composition; natural invertible proper-open maps;
coherent refinement comparisons; cancellation after further refinement;
equalization of both arrow pairs; identity and triple cocycle. These agree
with the source and the recorded existing family. No new theorem is postponed,
so no new proof docstring or DAG node is necessary. No statement_change or new
node/dependency module is present. The primary lean.statement is verbatim the
signature at LowerShriekCoherence.lean lines 442–447, excluding its proof.

Edge cases: empty source/target schemes and nondense compactifications are
allowed; the zero ring and zero complexes are included. There is no n, finite
index set, positive-degree condition or excluded characteristic. All bounded
below complexes are covered, with no uniform lower bound imposed. The arbitrary
scheme universe u and coefficient/module universe u+1 match the dependency
convention; no additional equality of site object and morphism universes is
required. Proper f admits `Compactification.ofIsProper f` with identity j.

Independent searches: msearch leanfinder, query "Canonical comparison of
exceptional derived direct image functors through arbitrary proper refinements"
returned generic sheaf pushforward, derived exact-functor comparison and
localizer comparison declarations, not this theorem. Loogle query
`"LowerShriek", "Iso"` returned zero hits. Direct rg with
`shriek|exceptional.*direct.*image|compactification.*derived` in Mathlib's
AlgebraicGeometry and CategoryTheory returned no match. Direct rg with
`compactification.*[Ii]ndependen|[Ii]ndependen.*compactification|PlusIso_eq_refinementIso`
in upstream WeilConjectures and project lean/Sheaf found the existing
LowerShriekIndependence/Coherence family and consumers; those actual definitions
and full surrounding binders were opened above. No competing project definition
should be introduced.

Mismatches/changes: no mathematical or signature mismatch found. Appended this
current independent reading; retained the worker report and existing Lean record.
No Lean source file is added or changed. Delivery validation below probes every
recorded declaration through the authorized compilation wrapper.
