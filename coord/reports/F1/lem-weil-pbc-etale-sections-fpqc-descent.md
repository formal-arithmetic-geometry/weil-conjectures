## Worker report

The module Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent states
AlgebraicGeometry.existsUnique_etaleSection_of_fpqc_cover, with sorry as its only proof.
The item is unchanged outside lean. No new definitions, dependency modules, or corrections
are needed.

Hypotheses and clauses, individually:

- S is a scheme: `{S : Scheme.{u}}`.
- The arbitrary family indexed by I is `{I : Type v}`, `T : I → Scheme.{u}`,
  `g : ∀ i, T i ⟶ S`. No nonemptiness, finiteness, or quasi-compactness of
  individual arrows is assumed.
- The family is fpqc: `hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S`.
  This is exactly the dependency record's flat, jointly surjective, quasi-compact-family
  precoverage, not a stronger singleton-style condition on every g i.
- F is a sheaf of sets on the small etale site:
  `F : Sheaf S.smallEtaleTopology (Type (u + 1))`, following the recorded
  inverse-image declaration's universe convention.
- g_i inverse image is `(Scheme.etaleSetPullback (g i)).obj F`.
- Gamma(S,F) is `F.obj.obj (op (⊤_ S.Etale))`, evaluation at the final object.
- Gamma(T_i,g_i inverse image F) is evaluated at the base change of that final
  object, `(MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (⊤_ S.Etale)`.
  Base change preserves the final object; this is the identity scheme T_i over T_i
  up to its canonical isomorphism, so evaluation is all global sections, not a
  restricted class. Using this final object avoids arbitrary terminal transports.
- The product of these sets is the dependent function type of the binder `s`.
- The overlaps are `pullback (g i) (g j)` with `pullback.fst` and `pullback.snd`.
  Their structure maps are the projection composites, identified using
  `pullback.condition (f := g i) (g := g j)`.
- Each side of `hcompat` first pulls back s_i (respectively s_j) using the unit of
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` for its projection.
  It then applies the composition isomorphism from
  `Classical.choose etaleSetInverseImageCompositionUnits.2.2` at the iterated
  base-changed final object. This is the recorded dependency's unique
  unit-compatible isomorphism, not an arbitrary isomorphism supplied as a hypothesis.
- `obj.map ((MorphismProperty.Over.pullbackComp ...).hom.app (⊤_ S.Etale)).op`
  identifies evaluation on the iterated fibre product with evaluation on the
  final object base-changed along the composite. The right side's `Eq.mp` uses
  precisely pullback.condition.symm to identify the two overlap structure maps;
  it makes no new mathematical assumption.
- The equalizer condition is `hcompat : ∀ i j, ... = ...`.
- The canonical map is the adjunction unit at the final object, displayed in the
  concluding equations. The composition-and-unit dependency implies its values
  satisfy hcompat. Consequently `∃! t, ∀ i, unit(t) = s i` for each compatible s
  is exactly bijectivity onto the equalizer: existence is surjectivity, uniqueness
  is injectivity. No extra conclusion is asserted.
- The singleton clause is included by taking I = PUnit, T constant, and g constant:
  hcompat has precisely the two projection pullbacks on T times_S T, and the
  conclusion is unique descent. It does not need another declaration or proof.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and
  Scheme.Hom. Read their definitions and docstrings (Scheme.lean:34-76).
- def-weil-pbc-fpqc-covering: Mathlib.AlgebraicGeometry.Sites.Fpqc,
  AlgebraicGeometry.Scheme.fpqcPrecoverage, defined as propQCPrecoverage @Flat.
- def-weil-pbc-etale-sheaf-of-sets: its mathlib_match is CategoryTheory.Sheaf,
  Mathlib.CategoryTheory.Sites.Sheaf, used with Scheme.smallEtaleTopology; read
  the category definition and its sheaf property. The node is a Mathlib leaf and
  needs no additional lean record.
- lem-weil-pbc-sets-etale-inverse-image-composition-units:
  Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits,
  AlgebraicGeometry.etaleSetInverseImageCompositionUnits. Read the full statement
  and proof docstring. Its .2.2 existential supplies the canonical composition
  isomorphisms. Its imported Scheme.etaleSetPullback in
  Sheaf.AlgebraicGeometry.EtaleSheaves is the actual set inverse image, left Kan
  extension followed by sheafification; read its definition and docstring.
- Mathlib's MorphismProperty.Over.pullbackComp (OverAdjunction.lean:116) was read
  to check the direction of its hom: direct base change to iterated base change,
  hence contravariant restriction maps iterated evaluation to direct evaluation.

Edge cases checked before writing: identity cover gives the ordinary identity
restriction and unique gluing. Empty I is allowed; an empty fpqc covering requires
S empty and the empty-cover sheaf axiom makes its global-section set a singleton.
An empty member contributes its unique section; no exclusion is needed. For
Spec of a field covered by Spec of a separable closure, overlap compatibility is
exactly descent invariance, so arbitrary non-invariant sections are not asserted
to descend. I has its own unrestricted universe v (a covering family, not a
filtered-limit indexing category); schemes and sheaves use exactly the universes
of the recorded inverse image. No characteristic or coefficient restriction occurs.

Source read: https://stacks.math.columbia.edu/tag/09XN (local literature tex not
present on this machine). Its second assertion and proof state exactly the unique
gluing property formalized here. The docstring carries the node's four proof steps
and their named dependencies, including agreement of local sections and uniqueness.

Searches made:

- msearch.py leansearch, query "fpqc descent sections etale sheaf": UNAVAILABLE,
  Internal Server Error; no negative verdict inferred from this service failure.
- msearch.py leanfinder, query "Sections of a small etale sheaf descend uniquely
  along an fpqc covering": 8 hits, general site local-faithfulness/extensionality,
  CoversTop.sections_ext, TopCat.Sheaf.existsUnique_gluing', etc.; none states
  fpqc descent of inverse-image sections on small etale sites.
- msearch.py loogle, query "Scheme.fpqcPrecoverage, Sheaf": 0 hits, unknown
  identifier Scheme.fpqcPrecoverage (unqualified search name); no exact declaration.
- msearch.py grep, query "fpqc.*section|section.*fpqc", AlgebraicGeometry/Sites:
  0 hits.
- rg of source WeilConjectures and lean/Sheaf for "fpqc.*descent|sections.*[Ff]pqc|
  fpqc.*sections": quasi-coherent module sections, descent of morphisms, opens,
  etale schemes and torsors only; none is arbitrary small-etale set-sheaf sections.
- rg for the item id in WeilConjectures: no match.
- tools/lean_names_upstream.py show for the item: no declaration for this item.
- Read/search of existing Etale*.lean modules and sections modules confirms that
  Scheme.etaleSetPullback exists and is reused. The chosen theorem name has no
  match in the source/project searches.

Validation: server single-file compilation and delivery preflight are run through
scompile.py and deliver2.py --no-push. No local Lean build is run.

- Follow-up msearch.py loogle with the fully qualified query
  "AlgebraicGeometry.Scheme.fpqcPrecoverage": 8 hits, the precoverage itself,
  stability instances, topology comparisons, and singleton membership; no
  section descent theorem. The precoverage is reused.
- Exact-name rg for existsUnique_etaleSection_of_fpqc_cover across Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no match.

The final single-file server compile passed in 2.3 seconds with exit code 0,
no errors and no warnings. The delivery dry run printed OK; its only outstanding
preflight section is the independent second reading, to be written by the second
reader. Nothing was pushed.

## Second reading by F1

Independent reader: I opened the item's node copy and the entire Lean module,
then read all four statement dependencies and their declarations. I did not write
this statement. Verdict: PASS, with no mathematical or Lean-source changes.

Source check: the local repository has no Stacks tex checkout. I fetched the
upstream etale-cohomology.tex into this item's scratchpad and read
lemma-describe-pullback, lines 4959-5027, together with the preceding agreement-open
lemma. I also read https://stacks.math.columbia.edu/tag/09XN. The second assertion
is explicitly restated in the source proof as unique descent of compatible
inverse-image sections. Specializing tau to etale gives exactly this node.
There are no standing separatedness, Noetherian, finiteness, characteristic, or
coefficient hypotheses in this source statement.

Object/hypothesis/conclusion inventory and its Lean rendering:

1. Scheme S: `{S : Scheme.{u}}`. PASS. The dependency def-pc-scheme records
   Mathlib's locally affine locally ringed space and its morphisms; I opened
   Scheme.lean, the structure Scheme and structure Hom, rather than relying on
   their names.
2. Arbitrary family of schemes and arrows indexed by I: `{I : Type v}`,
   `T : I → Scheme.{u}`, `g : ∀ i, T i ⟶ S`. PASS. No extra instance on S,
   T, I, or g is bound.
3. Fpqc covering: `hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S`.
   PASS. I read def-weil-pbc-fpqc-covering, Fpqc.lean's fpqcPrecoverage,
   QuasiCompact.lean's propQCPrecoverage, and Cover/QuasiCompact.lean's
   QuasiCompactCover and exists_isAffineOpen_of_isCompact. These encode flat
   arrows and the finite affine-open image covering condition of the node.
   They do not require each individual arrow to be quasi-compact.
4. Arbitrary sheaf of sets F on the small etale site: `F : Sheaf
   S.smallEtaleTopology (Type (u + 1))`. PASS. I read the sheaf-of-sets dependency,
   Sites/Sheaf.lean's IsSheaf and Sheaf full subcategory, and Sites/Etale.lean's
   smallEtaleTopology and covering-family characterization. This is the small
   site of all etale S-schemes, not the big site or a constructible subcategory.
5. Inverse images: `(Scheme.etaleSetPullback (g i)).obj F`. PASS. I opened
   EtaleSheaves.lean's etaleSetPullback: the data are sheafified presheaf pullback
   along base change. I also read the full statement and proof docstring of
   EtaleSetInverseImageCompositionUnits.lean, including the type and unit
   characterization of its existential composition family.
6. A tuple in the product of global-section sets: the dependent function binder
   `s : ∀ i, ...obj.obj (op (...pullback ... (g i)).obj (⊤_ S.Etale))`.
   PASS. Base change of the terminal etale S-object is terminal over T_i:
   its structure arrow is the projection from the pullback of identity_S.
   Evaluation there is canonically all Gamma(T_i, g_i inverse image F).
7. The overlap scheme and its structure arrow: `pullback (g i) (g j)` and
   `pullback.fst (g i) (g j) ≫ g i`. PASS. The other composite is identified
   using `pullback.condition.symm`; there is no extra assumption on an overlap.
8. The two equalizer arrows: each side of `hcompat` applies the projection's
   sheaf-adjunction unit to s_i or s_j, then the hom component of
   `Classical.choose etaleSetInverseImageCompositionUnits.2.2`, then
   the inverse-image sheaf's map on `(Over.pullbackComp ...).hom.app ... |>.op`.
   PASS. I read OverAdjunction.lean's pullback and pullbackComp: the hom goes
   from direct to iterated base change, so its contravariant map correctly
   sends iterated evaluation to direct evaluation. The chosen composition
   family is not arbitrary: its choose specification contains the unit equation
   and fixed-sheaf uniqueness. The dependency's unit equation uses the inv
   comparison; the hom comparison here cancels it. Eq.mp on the right transports
   precisely the whole section carrier from the second composite to the first.
9. Equalizer membership: `hcompat : ∀ i j, ... = ...`. PASS. It asks for all
   ordered pairs, with both sections compared in the same inverse-image sheaf
   and at the same terminal object over the overlap.
10. Canonical restriction and bijectivity onto the equalizer: the conclusion
    `∃! t : F.obj.obj (op (⊤_ S.Etale)), ∀ i, unit.app F ... t = s i`.
    PASS. These units are exactly the canonical restriction maps. Their values
    satisfy hcompat by the dependency's unit equation and equality of the two
    overlap structure arrows. Unique existence for every compatible tuple is
    surjectivity onto the equalizer and injectivity; no arbitrary incompatible
    tuple is claimed to descend. Quantification is covering, F, tuple, compatibility,
    then unique global section, as in the node.
11. Singleton clause: specialize I to PUnit, T and g constant. PASS. The unique
    pair gives the two projections from T times_S T. Necessity follows from the
    same unit equation; sufficiency and uniqueness are the displayed conclusion.
    The clause needs no redundant additional assertion.

Edge cases: empty I is not excluded; joint surjectivity then forces S empty and
its sheaf has one global section by the empty covering axiom. Empty members and
empty overlap schemes likewise have one section. Identity covers are allowed.
A separable-closure cover of Spec k still requires overlap invariance, rather
than descending every section. No n or characteristic is introduced; n = 0 in
an affine-open refinement is permitted. The scheme universe u is arbitrary and
set values use the recorded inverse-image universe u+1; larger values can be
accommodated by raising u. The independent v on I is allowed for covering
families (this is not a filtered-limit indexing restriction). There are no
unbound variables or universes on inspection.

Independent searches (different wording from the worker's):

- LeanFinder via msearch.py: "An etale sheaf of sets has unique gluing of global
  sections after a faithfully flat quasi compact covering": eight hits, including
  TopCat.Sheaf.existsUnique_gluing and Scheme.GlueData.sheafValGluedMk. These
  concern open covers or Zariski gluing, not arbitrary etale inverse-image sections.
- Loogle via msearch.py: "AlgebraicGeometry.Scheme.fpqcPrecoverage,
  CategoryTheory.Sheaf": zero hits.
- LeanSearch via msearch.py: "Global sections of inverse images of a sheaf of
  sets on small etale sites satisfy faithfully flat descent": service unavailable
  (Internal Server Error), recorded as unavailable, with no negative inference.
- rg on Mathlib, WeilConjectures, and lean/Sheaf for fpqc together with section
  or sheaf, and faithfully flat with sheaf: hits are quasi-coherent module
  sections, torsors, and continuous-map/adic-function sheaves. I opened
  Modules/FpqcSections.lean's sections_ext_of_mem_fpqcTopology and
  exists_sections_of_mem_fpqcTopology: both require a quasi-coherent O_X-module,
  so neither is this theorem. The existing set inverse image is reused.

H4-H9: no duplicate definition, no definition introduced, and the sole proof is
`by sorry`. The module and declaration docstrings name Tag 09XN and this blueprint
id. The four proof paragraphs reproduce agreement opens, descent of opens,
local section representatives and factorization, and gluing plus uniqueness,
with the relevant DAG dependencies. Imports supply the cover predicate and the
inverse-image composition theorem and are used. The module has no local notation,
private declaration, hidden let binder, or target change. There are no new nodes,
dependency modules, or statement corrections to review. No mismatch was found;
the second reading changes only this report. The node's lean.statement is checked
verbatim against the declaration signature by the delivery preflight.

Second-reader validation: scompile.py passed, exit 0, in 2.3 seconds with no
warnings. deliver2.py --no-push printed OK: preflight and compile both passed.
