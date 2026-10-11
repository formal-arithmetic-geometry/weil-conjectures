## Worker report

Existing declaration: `CategoryTheory.Sheaf.H'`, in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, lines 84–89. No new module.
The signature and docstring were read, together with `cohomologyPresheafFunctor`
and `cohomologyPresheaf`, which give its definition.
Only the item's `lean` field changes.

Source checked: [Stacks Section 01DZ](https://stacks.math.columbia.edu/tag/01DZ),
equation (the project server) and the sentence following it. The local literature checkout
is absent on this machine, so the official source page was opened. It defines
cohomology by an injective resolution and records a universal delta-functor.

Clause-by-clause correspondence:

- An arbitrary topological space is `X : Type u` with `[TopologicalSpace X]`.
  Set `C := TopologicalSpace.Opens X` and `J := Opens.grothendieckTopology X`.
  The latter's covering sieves cover every point, exactly open coverings.
- An abelian sheaf is `F : Sheaf J AddCommGrpCat.{u}`. There is no scheme,
  separation, finiteness, or ringed-space hypothesis.
- Nonnegative degree is the `n : ℕ` argument of `H'`.
- Global sections mean evaluation at `⊤ : Opens X`, so the expression is
  `F.H' p ⊤`. Its value is an abelian group object, not just an unstructured set.
- The abelian category and enough injectives use `sheafIsAbelian`,
  `Sheaf.instIsGrothendieckAbelian`, and `IsGrothendieckAbelian.enoughInjectives`.
  These are exactly the declarations recorded by the enough-injectives dependency.
  The local scratch check successfully synthesizes this instance.
- `H'` is Ext from the sheafified free abelian representable of the argument.
  For `⊤`, sheafification adjunction, the free/forgetful adjunction, and Yoneda
  identify Hom from this sheaf with `F.obj.obj (Opposite.op ⊤)`, naturally in F.
  Therefore its Ext is the right derived functor of global sections, with the
  same injective-resolution interpretation as the Zariski-cohomology dependency.
  This is a canonical isomorphism interpretation, not a claimed definitional
  equality between the Ext and injective-resolution constructions. The bridge
  is stage-3 work, as the existing Zariski dependency's record explicitly says.
- The natural long exact sequence is a property of these derived functors,
  supplied by `Functor.exists_universal_rightDerived_deltaFunctor` for global
  sections. Its `CohomologicalDeltaFunctor` has `delta`, `mono_zero`,
  `exact_middle`, `exact_right`, `exact_left`, and `naturality`, covering every
  position including the initial zero and naturality in morphisms of sequences.
  No extra topological long-exact-sequence definition is introduced. Independently,
  upstream `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
  already states the corresponding sequence for `Sheaf.H`: `H.δSucc`,
  `H.exact_map_map`, `H.exact_map_δSucc`, `H.exact_δSucc_map`, and
  `functorHδ_naturality`. This confirms the clause is supported by the existing
  cohomology API, rather than requiring a different cohomology object.
- For a scheme take X to be its underlying topological space. This uses exactly
  the same `CategoryTheory.Sheaf.H'` at the top open as the recorded
  `def-sc-zariski-cohomology`, so the final clause introduces no new definition.

Dependencies read and used:

- `def-sc-zariski-site`: `Opens.grothendieckTopology` in
  `Mathlib.CategoryTheory.Sites.Spaces`, and `TopCat.Sheaf` in
  `Mathlib.Topology.Sheaves.Sheaf` (the node's qualified spelling
  `TopologicalSpace.Opens.grothendieckTopology` resolves to this same Opens namespace).
- `def-sc-zariski-cohomology`: `CategoryTheory.Sheaf.H'` in the module above.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.rightDerived` and
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`; additivity and left exactness
  are the recorded `Functor.Additive` and `PreservesFiniteLimits`.
- `lem-weil-pbc-site-sheaves-enough-injectives`:
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, with
  the sheaf Grothendieck instance described above.
- `lem-weil-pbc-right-derived-universal-delta-functor`:
  `CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor` in
  `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`. Its full signature,
  docstring, and the delta-functor fields were read.

Edge cases: the empty space is permitted (its top open is empty and sheaf
sections there form the zero group); the zero sheaf is permitted in all degrees;
`p = 0` gives global sections by the adjunctions above; no positive-degree bound
is imposed. Universes may be enlarged to contain both the space and its groups.
A scratch local compile checks `EnoughInjectives` and `F.H' p ⊤` with
`hasExt_of_enoughInjectives`, without an assumed injectivity or HasExt hypothesis
on the input sheaf. No scratch file is part of the delivery.

Searches made with `msearch.py`:

- LeanFinder, `cohomology of abelian sheaves on topological space right derived
  global sections`: eight hits including `Sheaf.cohomologyPresheaf`,
  `cohomologyPresheafFunctor`, `H`, and the sheaf Grothendieck instance.
- Loogle, `CategoryTheory.Sheaf.H'`: twelve hits, including the exact declaration
  and its full type and docstring. An earlier accidentally escaped apostrophe
  queried an unknown identifier; the corrected query above succeeded.
- LeanSearch, `cohomology sheaf topological space`: service unavailable,
  Internal Server Error; no mathematical verdict based on that search.
- Mathlib grep, `abbrev H|globalSections|rightDerived` in
  `CategoryTheory/Sites/SheafCohomology`: `H` and `H'` in Basic.lean.
- Source grep for this item id: no declaration tagged with the item id.
  Source and project grep for topological/abelian cohomology and `H'` found
  the existing sheaf cohomology API and the separate module-sheaf cohomology
  definitions. Those module definitions are not abelian-sheaf cohomology.
- Further source grep for `functorHδ` and `functorHZeroIso` found the upstream
  long exact sequence and degree-zero identification cited above; signatures
  and docstrings were read.

No statement correction, new node, dependency module, or disputed statement.

## Second reading by M1

I reread the node statement clause by clause against the recorded declaration `CategoryTheory.Sheaf.H'` in `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

- The arbitrary topological space is represented by the site object
  `C := TopologicalSpace.Opens X` and topology
  `J := TopologicalSpace.Opens.grothendieckTopology X`; no separation,
  finiteness, scheme, ring, or characteristic hypothesis is added.
- The coefficient is exactly an abelian sheaf
  `F : Sheaf J AddCommGrpCat`, and the degree is the node's nonnegative
  `p : ℕ`.
- The cohomology value at the whole space is rendered by
  `F.H' p ⊤ : AddCommGrpCat`; this is the existing Mathlib sheaf-cohomology
  primitive (Ext from the free sheaf on the representable), canonically
  identified with the right-derived global-sections construction named in the
  node. No injectivity or `HasExt` assumption is placed on `F`; the ambient
  site instances supply these as recorded by the dependency.
- The node's natural long exact sequence clause is supplied by the recorded
  universal right-derived delta-functor result, whose delta functor has the
  zero, exactness, and naturality fields. It is a property of this same
  cohomology, not a second definition.
- The scheme specialization is the same construction on the opens site and
  therefore agrees with the recorded `def-sc-zariski-cohomology` declaration.

The empty space, empty open, zero sheaf, and degree `p = 0` remain allowed;
there is no hidden nonemptiness or positive-degree restriction. The universes
are those of the site and `AddCommGrpCat` and can be enlarged together. I
searched Mathlib, the source checkout, and `lean/Sheaf` for alternate
cohomology definitions (LeanFinder, Loogle, LeanSearch, and grep); only the
`H`/`H'` API was found. No mismatch was found, so no source, dependency, or
Lean declaration was changed in this second reading.
