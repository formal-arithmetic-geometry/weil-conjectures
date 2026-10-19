## Worker report

The delivery states `CategoryTheory.exists_ringedExtendedCech_completion_model` in
`Sheaf.Paper.ExtendedCechCompletionModel`. The item's prose statement, proof, and proof
edges are unchanged. Its statement dependencies gain seven definition nodes supplying
notions that the three original dependencies did not define. No dependency node is
re-recorded. Every new theorem has proof `sorry`; definition data are actual constructions.

Hypothesis and clause correspondence:

- A small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  The ring is `(O : Sheaf J CommRingCat.{u})`. A common universe contains the site and rings;
  `w` explicitly chooses the localization morphism universe, also on every slice.
- The ideal sheaf is `(I : ringedSiteModules ... O)` with a module monomorphism
  `ι : I ⟶ SheafOfModules.unit ... O` and `[Mono ι]`. A submodule of the rank-one ring module
  is precisely an ideal subsheaf. No quasi-coherence assumption is imposed.
- Local finite generation is Mathlib's `[I.IsFiniteType]` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`. This uses finite local generating
  families and does not assert that the section ideal on an object is finitely generated.
  The refined search found this existing definition; the initial duplicate local-finiteness
  predicate was removed before delivery.
- `D(O)` is Mathlib's `DerivedCategory` of the recorded `CategoryTheory.ringedSiteModules`.
  The latter is transparently `SheafOfModules`. `ringedSiteDerived` and `ringedSiteComplex`
  are public abbreviations, not replacement categories.
- The local-completeness clause is `IsLocallyDerivedRingedIdealComplete O I ι E`.
  Its binders quantify over every object `U` and every section `f`; the existential preimage
  under `ι.val.app (op U)` is exactly membership in the ideal. Its conclusion is `IsZero`
  of the recorded `derivedInternalHom (J.over U) (O.over U)` from the single complex of
  `ringedSectionLocalization` to `ringedDerivedRestriction O U |>.obj E`.
- `ringedSectionLocalization` is sheafification of the presheaf with actual carriers
  `Localization.Away (s.val X)` and the universal localization lifts as restrictions.
  `ringedSliceSection O U f` restricts `f` along each object's structure arrow into `U`.
  Thus localization means sheafified sectionwise localization, including on every slice.
- `ringedExtendedCech` is the ordered total tensor of `[O → O[1/f_i]]` in degrees zero
  and one. Expanding the tensor indexes degree `q` by `q`-element sorted subsets. The
  tensor of the associated localizations is canonically localization at their product;
  finite direct sums canonically equal finite products. This gives the alternating complex
  in the node, with degree-zero `O` under the unit identifications, and zero outside
  `[0,r]`. The total tensor differential has the sign given by the number of preceding
  degree-one factors, exactly the alternating localization differential.
- Each two-term augmentation is identity at degree zero and zero elsewhere. The tensor of
  these maps, followed by the canonical unit isomorphism, is the extended augmentation.
  The `Nat.rec` zero branch is literally `⟨O[0], 𝟙 _⟩`, covering `r = 0`.
- The first conjunct quantifies `∃ K ε` with `K : ringedSiteComplex O` and a chain map
  `ε : K ⟶ ringedSiteRingComplex O`. `HasLocalExtendedCechDescription` quantifies over
  every `U`, `r` and specified generating list. It gives a derived isomorphism from the
  actual local tensor model to the restricted `Q K`. Its equality is the augmentation
  square, using the canonical comparison for restriction of the ring complex.
- `IsRingedIdealGeneratingList` uses Mathlib's `GeneratingSections` of `I.over U`;
  an equivalence of its indexing type with `Fin r` matches the sections' images at the
  terminal slice object to the specified list. This is exactly sheaf generation by that
  list, rather than sectionwise surjectivity or a freely varying chosen local model.
- The subsequent `∀ K ε` applies to every augmented model with that local description,
  not only the model whose existence was just asserted.
- `ringedCechCompletionFunctor O K` is the curry of the recorded derived internal Hom
  functor at `op (Q.obj K)`, hence is precisely `E ↦ RHom(K,E)`.
- `ringedCechCompletionUnit` is `ringedDerivedHomUnit` followed by contravariant
  precomposition with `Q.map ε`. `ringedDerivedHomUnit` uses evaluation at one, the actual
  functorial K-injective replacement, its resolution map, and the canonical
  `Localization.fac` for the existing definition of `derivedInternalHom`. It does not
  choose an arbitrary isomorphism `E ≅ RHom(O,E)` from an existence theorem.
- The first universal-model conclusion says every output is locally complete. The second
  says the units are natural. The third is bijectivity of composition with `η_E` into
  every complete `L`; together these are precisely the left-adjoint reflection into the
  full subcategory of complete objects. Naturality in `L` is automatic from composition.
  The final clause is exactly `IsIso η_E` for every locally complete `E`.

The main theorem's docstring contains all seven supplied proof steps, including the
cover-dense subcategory, functorial sheafified ring complexes, generator independence,
gluing, the localization contraction, the positive-degree filtration, and global
orthogonality giving the universal mapping property. It cites the original proof nodes.

Dependencies read and reused include `DerivedCategory`, `HasDerivedCategory`,
`DerivedCategory.Q` (`Mathlib.Algebra.Homology.DerivedCategory.Basic`),
`CategoryTheory.ringedSiteModules` (`Sheaf.CategoryTheory.RingedSiteModules`), and
`CategoryTheory.derivedInternalHom` with its construction and full signature
(`Sheaf.Algebra.Homology.DerivedInternalHom`). Existing tensor and sheafification are
`HomologicalComplex.tensorObj`, `tensorHom`, `leftUnitor`,
`SheafOfModules.monoidalCategory`, `SheafOfModules.tensorClosed`, and
`PresheafOfModules.sheafification` with its adjunction. Slice restriction is the existing
`SheafOfModules.overFunctor`; its derived functor uses Mathlib's `Functor.mapDerivedCategory`.
Canonical evaluation uses `homComplexUnitEvaluation`,
`homComplex_unit_evaluation_isIso`, and `homComplex_unit_evaluation_comm` in the respective
`Sheaf.Algebra.Homology.HomComplexUnitEvaluation*` modules. The completion-unit definition
reuses the existing K-injective replacement, rather than introducing another replacement.
The existing proof dependency `CategoryTheory.rhom_global_sections` is imported from
`Sheaf.Algebra.Homology.RhomGlobalSections`; stated Mathlib proof dependencies are imported
as well. Proof dependencies without recorded declarations cannot yet be imported.

Edge cases checked: empty sites and empty covers; the zero ring and zero ideal; the unit
ideal; zero modules and zero complexes; empty generating lists; zero generators (localization
at zero is the zero ring); invertible generators (the one-section complex is contractible);
all integer degrees, including negative degrees; arbitrary unbounded derived objects.
No prime, characteristic, Noetherianity, scheme, enough-points, or boundedness restriction
is introduced. The ideal-membership condition and the finite-type assumption are substantive.
The `HasDerivedCategory` binders express the existing chosen-universe convention.

Searches: `msearch.py leanfinder` for “Global extended Cech complex and derived completion
of sheaves on a ringed site” returned ordinary sheafification and condensed-sheaf
constructions, no matching theorem. `msearch.py loogle "SheafOfModules, localization"`
returned zero hits and reported the unknown identifier `localization`. `msearch.py grep`
for `extendedCech|derivedCompletion|locallyDerivedComplete` returned zero hits. Direct `rg`
through upstream `WeilConjectures`, this project's `lean/Sheaf`, and
`dag/lean_names_upstream.json` found constant-coefficient derived-completion towers and
unrelated affine Cech cycles; neither is the general ringed-site statement. Searching the
item ID in upstream source found no attached declaration. `blueprint_refs.py search
"extended Cech"` returned zero blueprint nodes. The DAG's related localization and Cech
statements were read; they have no Lean declaration supplying these constructions.

Seven further LeanFinder searches covered each added notion individually. Their raw
queries and results are in the new nodes' `mathlib_searches`. They found the existing
`SheafOfModules.GeneratingSections` and `IsFiniteType`, which are reused, and the existing
tensor-complex construction, which is also reused. Other hits were scheme-only localized
modules, cohomological bounds, evaluation/corepresentability, or ordinary local cohomology.
A combined LeanSearch query returned Internal Server Error; it is recorded as unavailable,
without a mathematical verdict. Grep of all proposed public names in Mathlib, upstream,
`lean/Sheaf`, and the upstream-name map returned no conflicts.

All delivered files are checked with `scompile.py` on the server only, nice 19, two threads,
60 seconds per file. No local compiler or Lake build is used. One expensive derived-ring
restriction comparison was replaced by separately typed canonical comparisons on the ring
module, its single complex, and its derived image; the 60-second limit was not increased.
Only named proof obligations use `sorry`. The tensor-closed structure chosen from the
existing theorem is used to supply tensor preservation properties; the tensor data themselves
are fixed by the existing `monoidalCategory`, and no unknown coefficient or complex is chosen.

No statement correction and no STATEMENT-DISPUTED issue was found.

## New nodes

`def-weil-pbc-ringed-section-localization` defines actual sheafified sectionwise localization,
its restriction maps, its map from the ring sheaf, and the restriction of a section to a slice.
Source: algebraization.tex, Tags 0996 and 099E. Mathlib's ring localization and module
sheafification are reused; searches found only scheme-specific localization sheaves.

`def-weil-pbc-ringed-ideal-generators` matches a specified finite list of ring sections to
Mathlib's generating sections of the ideal module on the slice. Source: Tag 099E.
Mathlib's `GeneratingSections` and `IsFiniteType` are reused; the new predicate only supplies
the prescribed-list/image condition needed to quantify the local Cech comparison.

`def-weil-pbc-ringed-extended-cech` constructs the augmented localization complex by the
existing total tensor construction applied to the actual augmented two-term complexes.
Source: Tags 0996 and 099E. Searches found tensor-complex infrastructure but no such
localization complex or augmentation. Empty lists are constructed explicitly.

`def-weil-pbc-ringed-derived-restriction` specializes the existing exact-functor derived
construction to slice restriction, with canonical ring-module, single-complex and derived
comparisons. Source: Modules on Sites, Tag 03DJ, and Cohomology on Sites, Tag 08JB.
The DAG's localized-ringed-site node gives ordinary module restriction; no existing
arbitrary-ringed-site derived restriction or its needed exactness instances were recorded.
The new named theorems postpone only the additive and exactness proofs.

`def-weil-pbc-ringed-completion-unit` constructs the actual canonical evaluation/unit map
and its augmentation-induced composite, and curries the existing internal Hom functor.
Source: Tag 099F and sites-cohomology.tex, Section 08J7. Existing evaluation maps and their
proofs are reused. The existing derived-unit-isomorphism lemma is scheme-specific;
no new arbitrary isomorphism or Hom functor is substituted.

`def-weil-pbc-locally-derived-ringed-ideal-complete` is the literal localization/internal-Hom
vanishing condition on every slice and every section of the ideal. Source: Tags 0999 and
099F. Existing constant-coefficient tower-completeness definitions have different categories
and hypotheses and cannot serve this general ideal-sheaf definition.

`def-weil-pbc-local-extended-cech-description` packages exactly the augmentation-compatible
local derived isomorphisms for every slice-generating list. Source: Tag 099E. This is a
predicate about the actual constructed Cech complex, not an arbitrary supplied complex or
an unconstrained local-model parameter. Searches found no existing predicate of this form.

## Second reading by NE

I independently opened the base node, its sandbox copy, all eight delivered modules,
the three original statement-dependency nodes and their recorded declarations, and every
new definition node. I read algebraization.tex, the introduction to Derived completion on
a ringed site immediately before Tag 0996, Tags 0999, 099E and 099F, and the restriction
statement of sites-cohomology.tex Tag 08JB. The source assumes an arbitrary ringed site
and a finite type ideal sheaf, not a Noetherian ring, a scheme, or finite generation of
the section ideal on every object. The Lean preserves this distinction.

My object/hypothesis/conclusion checklist, with the matching Lean and verdict:

1. Small site: `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
   Commutative ring sheaf: `O : Sheaf J CommRingCat.{u}`. Match. The common universe can
   contain the site and coefficients; it does not impose cardinality or characteristic
   conditions. The `HasDerivedCategory.{w}` instances globally and on each slice are the
   chosen-localization-universe convention of `def-weil-abstract-derived-category`, not
   geometric or boundedness hypotheses.
2. Ideal subsheaf: module `I`, map `ι : I ⟶ SheafOfModules.unit ...`, and `[Mono ι]`.
   Match: a module subobject of the rank-one commutative ring module is an ideal subsheaf.
   Local finite generation: `[I.IsFiniteType]`. Match: I opened Mathlib Generators.lean;
   its definition uses covering families and finite generating sections on slices, not
   finite generation of `I(U)` as a module on sections.
3. Module sheaves and unbounded derived objects: `ringedSiteModules` is transparently
   `SheafOfModules`; `ringedSiteComplex` is `CochainComplex ... ℤ`, and `ringedSiteDerived`
   is the recorded Mathlib `DerivedCategory`. Match with the dependency signatures.
4. Localization and slice restriction: `ringedSectionLocalization` sheafifies the actual
   `Localization.Away` presheaf. Its restriction maps are localization lifts extending
   the ring restrictions. `ringedSliceSection` restricts a section along the structure
   arrow into `U`. `ringedDerivedRestriction` derives the existing exact `overFunctor`.
   Match; no replacement ring, module category, or freely chosen restriction is used.
5. Local completeness: `IsLocallyDerivedRingedIdealComplete` quantifies over every `U`
   and ring section `f`, tests membership by `∃ y, ι.val.app ... y = f`, and requires
   `IsZero` of `derivedInternalHom` from the degree-zero localization to restricted `E`.
   Match, including all further slices and arbitrary unbounded `E`.
6. The extended alternating complex and augmentation: `ringedExtendedCech` recursively
   tensors the actual `[O → O[1/f]]` complexes. I checked the terms, localization
   differential, projection, and order of the recursion. The summands for degree `q`
   correspond to sorted q-element subsets; tensoring localizations gives localization
   at their product, and finite coproducts are finite products here. The total tensor
   differential has sign `(-1)^p` on the second factor, hence the specified alternating
   signs. The augmentation is the tensor of the projections followed by the left
   unitor. Match up to precisely these canonical identifications, without changing
   the augmented derived object quantified in the node.
7. Existence of global augmented model: the first conjunct is `∃ K ε,
   HasLocalExtendedCechDescription O I ι K ε`. The predicate quantifies over every
   `U`, `r`, and specified generating list. `IsRingedIdealGeneratingList` uses actual
   Mathlib `GeneratingSections` on the slice, with index equivalent to `Fin r`; the
   images at the terminal object are the specified `f`. Since `ι` is monic, this is
   equivalent to generation of the ideal subsheaf by those ring sections. The
   derived isomorphism has source the actual local Cech model and target restricted
   `Q K`; its equation is exactly the augmentation square with the canonical ring
   restriction comparison. Match, with no coherent choice of all isomorphisms added.
8. Any augmented model: the second conjunct is a new `∀ K ε` followed by the local
   description implication. Match: it does not restrict to the existential witness.
9. Reflection functor and its canonical unit: `ringedCechCompletionFunctor O K` curries
   the recorded `derivedInternalHom` at `op (Q.obj K)`. `ringedCechCompletionUnit`
   composes `ringedDerivedHomUnit` with precomposition by `Q.map ε`. I followed the
   evaluation isomorphism, the actual K-injective replacement, its resolution map,
   and `Localization.fac`; their directions yield `E → RHom(O,E) → RHom(K,E)`.
   Match; an arbitrary isomorphism has not been chosen from an existence assertion.
10. The reflection clauses are: every output is locally complete; the units commute
    with every `g : E ⟶ E'`; composition with the unit is `Function.Bijective` on
    Hom into every complete `L`; and `IsIso` of the unit on every complete `E`.
    Match. The Hom bijection is exactly the universal arrow into the full subcategory;
    naturality in `L` follows from associativity of composition, so no missing
    additional hypothesis or adjunction datum is concealed.

Edge cases: the empty site is permitted and the slice conditions then quantify over
no objects. Empty covering sieves use the ordinary sheaf and generator conditions.
`r = 0` is literally the recursion base `⟨O[0], 𝟙 _⟩`; the generating-list predicate
then says the ideal on that slice is zero. Zero generators localize to zero; a unit
generator makes its two-term complex contractible. Zero ideal, unit ideal, zero ring,
zero modules, negative integer degrees, and unbounded complexes are included. There
is no prime, nonzero-ring, enough-points, Noetherian, finiteness-of-site, or scheme
hypothesis. Every universe and variable is explicitly bound. There is no `n > 0`
restriction hidden in the finite-list parameter.

New-node reading: all seven records have the required definition-node fields, empty
proof and proof-dependency lists, source, search records, ancestor/via data, and Lean
attachments. Their exact signatures occur verbatim in their modules. The localization,
generating-list, tensor Cech, derived-restriction, completion-unit, local-completeness,
and local-description definitions match their own statements as checked in items 4–9.
The new finite-list predicate reuses Mathlib generation and does not duplicate local
finite type. The restriction abbreviations expose the existing category rather than
creating a second category. The named `sorry` lemmas in the localization, two-term,
and restriction modules postpone proof laws only; they determine no unknown carrier,
complex, or map. There are no dependency-repair modules in this delivery.

Independent searches: I ran `msearch.py leanfinder` for "Derived adic completion of
sheaves as reflector using tensor product of two term localization complexes";
it returned condensed monoidal structures, Tor, localCohomology.diagram, and ordinary
AdicCompletion.ofTensorProduct, none the ringed-site theorem or added constructions.
I ran `msearch.py loogle` for `"GeneratingSections"`, opened the resulting Mathlib
structure and `IsFiniteType`, and confirmed that both are already reused. Direct `rg`
in Mathlib's sheaf-module and homological files, upstream WeilConjectures, project
lean/Sheaf, and the DAG used `cech.*(complet|localiz)`, `complet.*cech`,
`derived.*restrict`, and `overFunctor.*(additive|preserves)`. Related hits include
scheme/open restriction, `localized_restriction_adjunction` (which supplies an exact
left adjoint and assumes zero preservation, not the derived slice functor here),
and Hom-complex zero-preservation helpers. I opened that adjunction declaration and
Mathlib `overFunctor` and `HomologicalComplex.tensorObj`: none replaces the delivered
new notions, and the underlying existing constructions are reused. The worker's
LeanSearch unavailability is recorded without claiming a successful negative search.
No exact existing declaration replacing this item or a new node was found.

No mathematical mismatch was found, and no Lean or node statement was changed.
The main docstring reproduces all seven node proof steps and their dependency IDs;
all declarations have source/blueprint docstrings, and all theorem bodies in the
delivery are `sorry`. All eight files compiled cleanly through `scompile.py` on the
server with nice 19, two threads and 60 seconds per file. I also checked all eight
`lean.statement` fields verbatim and the 100-column bound. The second reading adds
this audit report only; there is no statement correction or unresolved dispute.
