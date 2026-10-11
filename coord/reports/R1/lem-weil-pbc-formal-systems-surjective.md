## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi` states
`AlgebraicGeometry.coherentFormalModule_epi_iff_first_component`, with proof `sorry`.
No definitions or dependency modules are added, and no statement correction is needed.
The declaration docstring supplies the node's four-step proof, with its proof dependencies.

Hypothesis and clause correspondence:

- "X a Noetherian scheme": `{X : Scheme.{u}} [IsNoetherian X]`. Mathlib's
  `IsNoetherian` extends `IsLocallyNoetherian X` and `CompactSpace X`, so both parts of
  Noetherianity are present, without strengthening to affineness or projectivity.
- "I a quasi-coherent ideal in O_X": `(I : X.IdealSheafData)`, the same bundled ideal
  used by the recorded formal-module definition. No extra ideal condition is imposed.
- "A morphism (F_n) -> (G_n) in Coh(X,I)":
  `{F G : CoherentFormalModule X I} (α : F ⟶ G)`. This uses the dependency's full
  subcategory of coherent adic inverse systems. Its morphisms are compatible natural
  transformations, with no additional component hypothesis.
- "which is abelian": this is the established categorical property recorded by
  `AlgebraicGeometry.coherentFormalModule_abelian`, not a new hypothesis on a selected
  Abelian structure. The module imports that dependency. `Epi` itself needs only the
  category instance, so the statement does not choose or redefine an Abelian structure.
- "is an epimorphism": `Epi α`, in the formal-system category itself.
- "if and only if its component F_1 -> G_1 is an epimorphism in Mod(O_X)":
  `↔ Epi (α.hom.app (op 0))`. The recorded category explicitly indexes positive level
  n+1 by `op n`. The `.hom` forgets the full-subcategory wrapper and `.app` takes the
  natural-transformation component, a morphism in `X.Modules`, at positive level 1.
  Both directions are asserted; no sectionwise surjectivity is substituted for sheaf epi.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` and
  `AlgebraicGeometry.IsNoetherian` (the latter supplies the exact Noetherian hypothesis).
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`:
  `AlgebraicGeometry.IsCoherentFormalModule`, `AlgebraicGeometry.CoherentFormalModule`.
  Read their full signatures, conditions, and indexing docstrings.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`:
  `AlgebraicGeometry.coherentFormalModule_abelian`. Read the full theorem: its first
  clause asserts existence of an Abelian structure, its second asserts termwise cokernels.
  This module is the direct import and imports the shared formal category.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`, the Mathlib match
  for `def-sp-abelian`; read its docstring and fields. No extra Abelian binder is needed.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `AlgebraicGeometry.Scheme.Modules`,
  with its category and Abelian instances. This is the component category, inherited
  through the formal-module import, rather than a private copy of O_X-modules.

Edge cases checked before writing: the empty scheme and zero systems are allowed;
I=0 gives constant coherent systems up to their transition isomorphisms, so the first
component detects epis. For I=O_X all positive terms are zero, so both sides hold.
No condition of properness, affineness, nonempty support, Jacobson containment on X,
or characteristic is added. The first component is positive level 1, never level 0.
Universe `u` is explicit and follows the recorded category's scheme and module universes.
Every binder is explicit; the theorem has no auto-bound implicits.

Source checked: local `literature/stacks-project/coherent.tex` is not available in this
clone, so opened https://stacks.math.columbia.edu/tag/087Y (Lemma 30.23.3). It states
exactly detection on the first component and gives the affine/Nakayama proof hint.
The node's four-step proof expands that hint. No source/statement discrepancy found.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py`, group R1, this item:

- LeanSearch: `coherent formal inverse systems epimorphism detected modulo ideal`.
  UNAVAILABLE: Internal Server Error; recorded as unavailable, without a match verdict.
- LeanFinder: `A morphism of coherent formal module systems is epimorphic if and only
  if its first component is epimorphic`. Eight hits: presheaf-of-modules epi component
  lemmas, ModuleCat forgetful functor, and condensed-module epi results. None concerns
  coherent adic systems or first-level detection, so none states this node.
- Loogle: `CategoryTheory.Epi, Nakayama`. Zero hits; unknown identifier `Nakayama`.
- Mathlib grep: `formal.*(epi|surject)|[Ee]pi.*[Ff]ormal|inverse-systems-surjective`.
  Twenty-three hits, mainly formal smoothness/etaleness of ring maps and an unrelated
  sheaf stalk comment; none is this theorem.
- `rg -n` with that pattern plus `lem-weil-pbc-formal-systems-surjective` and the
  proposed name `coherentFormalModule_epi` across the source `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`: project references to this
  lemma in GrothendieckExistenceProjective's proof docstring, a formal-module-kernel
  docstring about transition epis, and a pullback quotient epi statement. No matching
  declaration, and no collision for the proposed name.
- Read `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory` to check `.hom` is
  exactly the inclusion on morphisms; the inclusion's `ι_map` confirms it.

No STATEMENT-DISPUTED flag and no node faults.

## Second reading by R1

Independent reading of the node copy, the delivered Lean file, all five statement
 dependency records, and their declaration signatures. The source TeX is absent from
this clone. I read the upstream `coherent.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
labels `section-coherent-formal` and `lemma-inverse-systems-surjective`, and checked
https://stacks.math.columbia.edu/tag/087Y and the opening of Section 0EHN.
The section assumes precisely a Noetherian scheme and a quasi-coherent ideal; it
specifies coherent positive-level inverse systems with the adic quotient condition.
No statement correction is present or needed.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. Scheme X: `{X : Scheme.{u}}` introduces an arbitrary scheme, with explicit universe.
2. Noetherian X: `[IsNoetherian X]`. I opened Mathlib's Noetherian module:
   `IsNoetherian` extends `IsLocallyNoetherian X` and `CompactSpace X`. The dependency
   `pqf-def-locnoeth` records the former, not the stronger class alone; the latter
   supplies the quasi-compactness expressly required by the source and the category
   definition. No separation, properness, affine, or nonempty hypothesis is added.
3. Quasi-coherent ideal I in O_X: `(I : X.IdealSheafData)`. I opened its Mathlib
   structure: ideals on affine opens, localization compatibility, and their determined
   support. This is the dependency's ideal carrier, with no extra ideal restriction.
4. Formal systems F and G: `{F G : CoherentFormalModule X I}`. I opened the recorded
   `Sheaf.AlgebraicGeometry.CoherentFormalModule` module and its object predicate.
   Each `op n` term is coherent, killed by I^(n+1), and the transition from `op (n+1)`
   factors through the quotient by I^(n+1) as an isomorphism onto `op n`. This matches
   all object conditions in the node and Section 0EHN, shifted by one consistently.
5. Compatible family alpha: `(α : F ⟶ G)`. Mathlib's ObjectProperty full-subcategory
   category is the induced category, with inclusion mapping a morphism to `.hom`.
   Thus `α.hom` is the actual natural transformation of the underlying inverse
   systems, not an arbitrary collection of component maps.
6. The category is abelian: the imported recorded theorem
   `coherentFormalModule_abelian` asserts `Nonempty (Abelian (CoherentFormalModule X I))`
   and termwise cokernel coforks. I read that signature and Mathlib's `Abelian` class
   (preadditivity, normal monos/epis, finite products, kernels, cokernels). This is a
   known property, not an extra selected Abelian-instance hypothesis; `Epi` is
   intrinsically defined by cancellation in the existing category.
7. Epimorphism in Coh(X,I): `Epi α`, in exactly the formal-system full category.
8. First component epimorphism in Mod(O_X): `Epi (α.hom.app (op 0))`.
   Evaluation is in `X.Modules`, the recorded `Scheme.Modules` declaration, whose
   definition is `SheafOfModules.{u} X.ringCatSheaf` and whose Abelian instance I read.
   The exponent in the object predicate is `0+1`, so this is F_1 -> G_1.
   Categorical epi here is sheaf surjectivity, not surjectivity on every open's sections.
9. Both directions and quantifier order: `↔` after the binders X, I, F, G, alpha.
   There is no restriction on alpha, no existential replacement, and no extra conclusion.

Edge cases: the empty scheme and zero systems are permitted. I=0 forces transitions
 to be isomorphisms, so first-level epi detection has the expected constant-system
meaning. I=O_X forces all terms to be zero. There is no source level zero: Lean n=0
represents positive level 1. The index category is the specified natural-number
inverse system, so an arbitrary empty index set is not an object quantified over
by this lemma. Empty affine coverings on the empty scheme cause no exclusion.
All characteristics and arbitrary scheme universe u are allowed; modules use the
recorded dependency's universe convention. There is no independent small test
universe or omitted variable, and relaxed auto-implicit binding is not required.

Independent searches, with wording different from the worker's:

- LeanSearch via msearch: `Nakayama detects categorical epimorphisms of coherent
  adic sheaf inverse systems at level one`. Service returned Internal Server Error;
  recorded UNAVAILABLE, not a no-match verdict.
- LeanFinder via msearch: `epimorphism in adic coherent sheaves iff reduction to
  closed subscheme is epi`. Eight hits concerned light condensed limits, ordinary
  sheaf generating sections, structure sheaves, or sheafed-space epis. None states
  first-level detection for coherent adic systems.
- Loogle via msearch: `CategoryTheory.Epi, CategoryTheory.NatTrans.app`. Twelve hits,
  including `NatTrans.epi_of_epi_app` and `NatTrans.epi_iff_epi_app`: these concern
  all components in the full functor category, not one component in Coh(X,I), so
  they do not already state the item.
- rg on Mathlib, source WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json with
  `coherentformalmodule.*(epi|surject)|first.*component.*epi|inverse.systems.surjective|formal.*epimorphism|epimorphism.*formal`
  (case insensitive): only the formal-kernel transition docstring and the
  Grothendieck-existence proof reference appeared. No duplicate declaration or name
  collision was found. Existing algebraic Nakayama results are proof ingredients.

There are no new nodes or dependency modules in this delivery and no missing
notion. No H3/H4 mismatch was found. The source and statement are left unchanged.
The single named theorem still has proof `sorry`; no definition, instance, private
copy, local notation, or proof was added. The header, source/blueprint docstrings,
100-character line convention, and explicit universe/binders were checked.
The declaration docstring follows all four node proof steps: termwise cokernels,
affine completion and first-level surjectivity, Nakayama over the completed ring,
and vanishing on an affine cover. The node's lean.statement equals the file's
signature verbatim. This second reading adds only this review and independent
search evidence.
