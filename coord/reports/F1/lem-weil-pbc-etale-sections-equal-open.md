## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen` states
`AlgebraicGeometry.existsUnique_etaleSections_equal_open`. Its only theorem proof
is `sorry`; no definition is introduced. The item node changes only in `lean`.

### Statement correspondence

- The scheme S is `(S : Scheme.{u})`.
- A sheaf of sets on its small étale site is
  `(F : Sheaf S.smallEtaleTopology (Type (u + 1)))`. This is the existing
  Mathlib full subcategory of presheaves satisfying the sheaf condition, with
  exactly the coefficient universe used by the dependency's inverse image.
- The étale object V → S is `(V : S.Etale)`. Its scheme is `V.left`, its structure
  morphism is `V.hom`, and the two sections are `(s t : F.obj.obj (op V))`.
- The arbitrary test morphism is quantified as
  `∀ (T : Scheme.{u}) (a : T ⟶ V.left)`. No étaleness, finiteness, separation,
  nonemptiness or other hypothesis is imposed on a.
- The composite e is literally `a ≫ V.hom`, without a second arbitrary choice.
- The inverse-image sheaf is `(Scheme.etaleSetPullback (a ≫ V.hom)).obj F`,
  the existing left-Kan-extension-then-sheafification construction. The section
  e* s is the adjunction unit evaluated at F and `op V`, then applied to s;
  the identical expression with t gives e* t. It is precisely the adjunction
  used in the recorded dependency, with continuity supplied explicitly.
- Base change of V is
  `(MorphismProperty.Over.pullback @Etale ⊤ (a ≫ V.hom)).obj V`, whose underlying
  scheme is `pullback V.hom (a ≫ V.hom)` = V ×_S T.
- The source of restriction is the T-étale object
  `MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : Etale (𝟙 T))`.
  The map `(a, id_T)` is exactly `pullback.lift a (𝟙 T) ...`; its compatibility
  is the existing equality `(Category.id_comp (a ≫ V.hom)).symm`.
  `MorphismProperty.Over.homMk` makes it a T-site morphism, using the existing
  projection identity `pullback.lift_snd`. The presheaf's `.obj.map ... .op`
  restricts the unit section to that terminal object, which is evaluation on T.
- The unique open subscheme W ⊂ V is `∃! W : V.left.Opens`.
  `W.toScheme` is the canonical restricted scheme and `W.ι` its inclusion.
- Factoring through W is `(∃ b : T ⟶ W.toScheme, b ≫ W.ι = a)`.
- The iff in the node is rendered by `↔` between this factorization and equality
  of the two restricted unit sections. Existence and uniqueness apply to this
  entire property for every T and a, not merely to étale test objects.

### Dependency declarations and source reading

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. Read the structures and their docstrings;
  `X ⟶ Y` is the scheme morphism type. Opens are Mathlib's `Scheme.Opens`, with
  `Scheme.Opens.toScheme` and `.ι` in `Mathlib.AlgebraicGeometry.Restrict`.
- `def-weil-pbc-etale-sheaf-of-sets`: the node is a Mathlib leaf whose
  `mathlib_match` is `CategoryTheory.Sheaf`,
  `Mathlib.CategoryTheory.Sites.Sheaf`; read the full-subcategory declaration
  and `Scheme.smallEtaleTopology` in `Mathlib.AlgebraicGeometry.Sites.Etale`.
  The object V uses Mathlib's property-restricted over category.
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`:
  `AlgebraicGeometry.etaleSetInverseImageCompositionUnits` in
  `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`. Read its full
  signature and proof docstring, including its local notation expansion.
  The module imports the dependency and uses exactly the same underlying
  `Scheme.etaleSetPullback`, `MorphismProperty.Over.pullback`, and
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` unit.
  The pullback definition is in `Sheaf.AlgebraicGeometry.EtaleSheaves`, and the
  adjunction is in `Mathlib.CategoryTheory.Sites.Pullback`.
- The continuity theorem `AlgebraicGeometry.Etale.isContinuous_overPullback`
  is imported from `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
  The server exposes it as a theorem, whereas the local read-only source says
  instance; a server `#print` established its full signature. The `@` form of
  the existing adjunction explicitly supplies this theorem. The server accepted
  the expression without extra hypotheses or file-local instances.

The local Stacks TeX file is absent on this machine. Read the authoritative
[Stacks Tag 09XM](https://stacks.math.columbia.edu/tag/09XM), Lemma 59.39.1,
statement and proof, online. The source treats sections over the base itself;
this node is its application over the étale object V, using the original
sheaf's restrictions. The source's open-representability and stalk-pullback
argument is the three-step proof copied into the theorem docstring. No statement
correction is needed.

### Edge cases

- If s = t, the characterized open is all of V; every a factors and both
  restriction expressions coincide. No inequality of s and t is assumed.
- If V is empty, its only open is empty, and a morphism to V has empty domain;
  both sections agree by the empty-cover sheaf condition.
- If T is empty, it factors through every candidate W, and the sheaf on its
  étale site has a singleton value on the empty object, so the equality holds.
- The empty agreement locus is allowed. For example, distinct sections of a
  constant two-element sheaf have no agreement over any nonempty connected test.
- Non-étale a is included: the site arrow is `(a, id)` between T-étale objects,
  not a itself asserted étale. Identity and open-immersion a are included, which
  are also the tests establishing uniqueness.
- No characteristic or noetherian assumption occurs. Universes are explicitly
  declared (`universe u`); all schemes and test schemes share u and coefficients
  have Type (u + 1), as in the existing inverse-image construction.

### Searches

All msearch commands used the group F1 and item
lem-weil-pbc-etale-sections-equal-open.

- `leanfinder`: "For two sections of a sheaf on the small etale site there is a
  unique open subscheme through which a scheme morphism factors if and only if
  their inverse image restrictions agree". Eight hits: structure-sheaf
  `Scheme.OpenCover.ext_elem`, `Scheme.hom_ext_of_forall`, `Scheme.Hom.appLE_congr`,
  topological `Presheaf.section_ext` / `Presheaf.IsSheaf.section_ext`,
  `TopCat.Sheaf.objSupIsoProdEqLocus_inv_eq_iff`,
  `Scheme.spread_out_unique_of_isGermInjective'`, and `Spec.basicOpen_hom_ext`.
  None states the étale inverse-image agreement-open claim.
- `loogle`: `AlgebraicGeometry.Scheme.Opens, CategoryTheory.Sheaf`. Two hits,
  `Scheme.AffineZariskiSite.sheafEquiv` and
  `Scheme.Modules.sheafComposePushforwardComp`, unrelated to this theorem.
- `leansearch`: "largest open subscheme where two sections of an etale sheaf
  agree". Service unavailable (Internal Server Error); no search verdict.
- msearch `grep`: `equal.*sections|sections.*equal|largest.*open` under
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` of `lem-weil-pbc-etale-sections-equal-open|sections.*equal|equal.*sections`
  over the source `WeilConjectures` and repository `lean/Sheaf` found only other
  section extensionality, glueing and cohomology statements. An additional
  `rg` of `etale.*[Ss]ections.*[Ee]qual|equal.*[Oo]pen|agreement.*[Oo]pen`
  over `dag/lean_names_upstream.json`, `WeilConjectures` and `lean/Sheaf` found
  unrelated quasi-affine equal-opens and pro-étale-point material, no match.
- Read Mathlib property-over constructors and pullback declarations, confirming
  the existing `Over.mk`, `Over.homMk`, `Over.pullback` and `pullback.lift`
  supply all data; no missing notion and no new node are required.

### Validation

Server single-file compilation via scompile.py succeeded in 2.0 seconds with
no errors or warnings. The only theorem proof is `sorry`, as required by stage 2.
No STATEMENT-DISPUTED or node fault remains. Independent second reading is left
to the dispatcher-appointed second reader.


## Second reading by F1

Independent reading of the sandbox node and EtaleSectionsEqualOpen.lean against
Stacks Tag 09XM, not a repetition of the worker's report. I also read the three
statement-dependency nodes and their actual declaration signatures.

### Objects, hypotheses and conclusion

1. Scheme S: `(S : Scheme.{u})` uses the recorded `AlgebraicGeometry.Scheme`;
   Mathlib's local-affine locally ringed space and scheme morphism structures
   match def-pc-scheme. Verdict: exact.
2. Sheaf of sets F on the small etale site: `(F : Sheaf S.smallEtaleTopology
   (Type (u + 1)))`. I read `CategoryTheory.Sheaf`, its full-subcategory
   definition using `Presheaf.IsSheaf`, and `Scheme.smallEtaleTopology`, the
   induced etale topology with jointly surjective covering families. These are
   the dependency's recorded Mathlib notions. Verdict: exact.
3. Etale object V -> S and two sections: `(V : S.Etale)` and
   `(s t : F.obj.obj (op V))`. The property-restricted over category has etale
   structure arrows and arbitrary base-compatible morphisms (`Q = top`), not
   a separated or finite-etale specialization. Verdict: exact.
4. Arbitrary test scheme and morphism: `forall (T : Scheme.{u})
   (a : T -> V.left)` inside the property of W. There is no instance on a;
   no Noetherian, finiteness, characteristic or nonemptiness hypothesis occurs.
   Verdict: exact.
5. Composite e: every inverse-image and base-change expression uses
   `a ≫ V.hom`. Verdict: exact; e is determined, not independently quantified.
6. Inverse image and pulled-back sections: `Scheme.etaleSetPullback` is the
   existing left Kan extension followed by sheafification. The displayed
   `sheafPullbackConstruction.sheafAdjunctionContinuous` unit evaluated at F,
   then `op V`, sends s or t to a section on V x_S T. I opened the full
   composition-units dependency signature, expanded its local L/b/unit
   notations, and checked that this is the same adjunction and construction.
   Verdict: exact, with no private substitute.
7. Restriction defining s|_T and t|_T: `.obj.map` acts on the opposite of
   `Over.homMk (pullback.lift a (identity T) ...) ...`. Its source is the
   identity etale object of T and its target is the base change of V.
   `pullback.lift_snd` supplies the over-T compatibility. I read Over.mk,
   Over.homMk and Over.pullback; the underlying target is V x_S T with second
   projection. Thus the map is (a,id_T), and the final value is evaluation at T.
   Verdict: exact, including for non-etale a.
8. Unique open subscheme of V: `existsUnique W : V.left.Opens` uses Mathlib's
   canonical restricted scheme `W.toScheme` and open inclusion `W.ι`, whose
   definitions I opened. Verdict: exact; uniqueness is of the open subset,
   hence of its canonical open subscheme.
9. Factorization iff equality: `(exists b : T -> W.toScheme, b ≫ W.ι = a)`
   is equivalent to equality of the two restricted unit images. Both directions
   are present. The order is one unique W, then every T and a. No clause asserts
   uniqueness of the factorization or restricts the tests. Verdict: exact.

### Source, edge cases and conventions

The local literature checkout has no Stacks TeX. I fetched the authoritative
Stacks etale-cohomology.tex into this item's scratchpad and read the section
preamble and lemma-where-sections-are-equal, also checking
https://stacks.math.columbia.edu/tag/09XM. The section imposes no ambient
hypotheses. Applying its base-section statement to the sheaf restricted over V
and using inverse-image compatibility gives precisely this node's statement.
The source's subsheaf, open representation and geometric-stalk pullback steps
are all in the declaration docstring; uniqueness is justified there by testing
candidate open immersions.

Equal sections allow W = top; an empty agreement locus allows W = bottom.
Empty V and empty S are included; a map to an empty scheme has empty source.
Empty T factors through every W and its two sections agree by the empty-cover
sheaf axiom. Identity and open-immersion tests are available for uniqueness.
No index set, zero object, n, or characteristic parameter is introduced.
The arbitrary universe u is bound, all schemes share the site's scheme universe,
and Type (u+1) is the coefficient universe of the recorded inverse image. There
is no extra independent test universe that could make the characterization
vacuous. No new node or dependency module is delivered, and there is no
statement_change to review.

Both imports serve the existing inverse-image construction/adjunction and
continuity theorem. There is no new definition, hollow data, local notation,
private abbreviation, unbound variable, or proved theorem. The single theorem
has exactly a sorry proof; both docstrings name the source and blueprint.
I checked the 100-character limit and exact equality of lean.statement with
the file signature programmatically.

### Independent searches and result

I ran msearch with this group/item and different wording:

- LeanSearch: "an etale sheaf equalizer of two sections is represented by an
  open immersion"; service returned Internal Server Error, so no verdict.
- LeanFinder: "The locus of equality of two sections of an etale sheaf is an
  open subset universally under base change"; eight hits concerning the ring
  etale locus, etaleTopology and a locally ringed space coequalizer, none this
  statement.
- Loogle: `"equal", "open", Sheaf` could not resolve the short Sheaf name;
  reran `CategoryTheory.Sheaf, "equal"`, yielding topology-transport and
  condensed equalizer-condition statements, neither this theorem.
- Mathlib grep: `equalizer.*open|open.*equalizer|agreement|sections.*coincide`
  under AlgebraicGeometry found only a quasi-separatedness compactness proof.
- Independent rg of the same concepts and `where.sections` in WeilConjectures
  and project lean/Sheaf found unrelated glueing/extensionality and an
  unramified morphism agreement locus. I opened FormallyUnramified.eqLocus
  and the EtalePoint use: these concern two morphisms into an unramified scheme,
  not arbitrary sections of any sheaf of sets, and do not duplicate this node.

No mismatch was found; I preserved the Lean and node verbatim and added only
this second-reading report. Fresh scompile of the delivery module succeeded
in 2.0 seconds with exit code 0 and no warnings or errors.
