## Worker report

The module `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso` states
`AlgebraicGeometry.Scheme.Modules.quasiIso_globalSections_pushforward_injectives`.
There is one theorem, with proof `sorry`, and no new definitions. The node statement
and all of its dependency fields are unchanged.

Clause-by-clause correspondence:

- A morphism of schemes is `{X Y : Scheme.{u}} (h : X ⟶ Y)`, with no properness,
  finiteness, nonemptiness, or field hypothesis.
- The two cochain complexes are `I : CochainComplex X.Modules ℤ` and
  `J : CochainComplex Y.Modules ℤ`. Their terms are sheaves of modules over the
  structure sheaves, and their chain-map structures contain the differentials and
  commutation relations.
- Every term is injective: `hI : ∀ n : ℤ, Injective (I.X n)` and the corresponding
  `hJ`. These hypotheses refer to the original module-sheaf categories, not to
  the category of abelian sheaves or to injectivity of the direct image.
- Vanishing below degree zero is `hI0 : ∀ n : ℤ, n < 0 → IsZero (I.X n)` and
  `hJ0`. Categorical zero is used rather than equality to a chosen zero object;
  this is invariant under isomorphism and expresses precisely that the terms vanish.
- Applying direct image termwise is
  `((pushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I`.
  Mathlib's `pushforward` uses the underlying continuous map and structure-sheaf
  map of `h`, including restriction of scalars; the differential is the image
  of the differential of `I`.
- The chain map called λ in the node is named `φ` in Lean (λ is a parser keyword).
  Its domain is this termwise direct image, its codomain is `J`, and its
  quasi-isomorphism hypothesis is `hφ : QuasiIso φ`.
- The local abbreviation `G` is the composite of the existing
  `toPresheafOfModules Y` and `PresheafOfModules.evaluation` at `op ⊤`.
  It is definitionally the existing `SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)`.
  Thus it is Γ(Y,−), valued in modules over `Y.ringCatSheaf.obj.obj (op ⊤)`,
  the underlying ring of O_Y(Y). No second definition of global sections is introduced.
- The first conjunct says `QuasiIso ((G.mapHomologicalComplex ...).map φ)`,
  the module-valued conclusion. The second says the same for `G ⋙ forget₂ ...
  AddCommGrpCat`, the abelian-group-valued conclusion.
- `QuasiIso` means that the actual induced homology map is an isomorphism in every
  integer degree; for modules and abelian groups this is exactly bijectivity of
  H^p(Γ(Y,φ)), including p = 0 and negative p. Neither conclusion asserts existence
  of some unrelated isomorphism between the homology objects.
- The source written Γ(Y,h_*I) = Γ(X,I) is the very complex in the domain:
  `pushforward_obj_obj` computes its degree n underlying group as
  `I.X n` evaluated at `h ⁻¹ᵁ ⊤`, and `pushforward_map_app` computes its differential
  as the original differential evaluated there. The inverse image of the whole
  space is the whole space. On the module side the O_Y(Y)-action is restriction
  along h's structure-sheaf map, so equality is understood with that action, not
  as equality of modules over different rings. These are existing pushforward
  formulas, not additional hypotheses or a weaker substitute for this source.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sp-injective-resolutions`: its injective-object clause is
  `CategoryTheory.Injective`, `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  `InjectiveResolution` in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`
  was read as well; the item assumes complexes of injectives, not resolutions of
  particular objects, so it uses the injective-object clause of this dependency.
- `def-pc-cochain-complex-modules`: `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`.
- `def-pc-module-pullback`: the recorded `tensorPullback` module
  `Sheaf.AlgebraicGeometry.TensorPullback` was read, including the signature and
  docstring of `nonempty_tensorPullbackAdjunction`. Its right adjoint is the
  exact Mathlib `AlgebraicGeometry.Scheme.Modules.pushforward` used here, in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`. This item uses only the direct-image
  clause, so no tensor-pullback declaration or unnecessary import is introduced.
- `def-pc-quasi-iso-modules`: `QuasiIso`, `Mathlib.Algebra.Homology.QuasiIso`.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`. Mathlib's `Scheme.Modules` is this
  very category for `X.ringCatSheaf`, with its canonical abelian instance.

Additional standard APIs are `Functor.mapHomologicalComplex`
(`Mathlib.Algebra.Homology.Additive`), module evaluation
(`Mathlib.Algebra.Category.ModuleCat.Presheaf`), and `forget₂` from modules to
abelian groups. `Mathlib.Algebra.Category.Grp.Abelian` supplies the abelian
structure and hence homology for the abelian-group conclusion. The theorem
introduces no category or derived-category instance choices.

Source reading: the literature checkout is absent on this machine, so the actual
Stacks source places were read online:
[01FB](https://stacks.math.columbia.edu/tag/01FB),
[01F0](https://stacks.math.columbia.edu/tag/01F0),
[01EX](https://stacks.math.columbia.edu/tag/01EX), and
[015E](https://stacks.math.columbia.edu/tag/015E).
The first describes the global-sections comparison arrow; 01F0 identifies its
source with Γ(X,I); 01EX gives acyclicity of direct images of injectives; 015E
computes derived global sections by these bounded below acyclic complexes.
The declaration docstring carries the node's five proof steps and their nodes.

Edge cases checked mathematically before writing: the empty scheme and zero
complex cause no failure (all relevant groups are zero); identity maps recover
comparison of injective complexes; degree zero is included; negative degrees
are included and vanish by the nonnegative-term hypotheses. Arbitrary schemes,
including non-Noetherian schemes, are allowed. There is no bounded-above
hypothesis and no assumption that pushforward preserves injectives. One arbitrary
universe `u` matches the dependency's canonical category `Scheme.Modules`.

Searches (2026-10-11):

- `msearch.py ... leanfinder`, query: “global sections of a quasi-isomorphism
  from pushforward of a bounded below complex of injective sheaves of modules
  to a bounded below complex of injectives is a quasi-isomorphism”. Eight hits
  included `InjectiveResolution.instQuasiIsoIntι'`, `cm5b.instQuasiIsoIntP`, and
  localization/K-injective results; none states this geometric comparison.
- `msearch.py ... loogle`, query `QuasiIso, Functor.mapHomologicalComplex`:
  zero hits, unknown identifier `Functor.mapHomologicalComplex` in that index.
- `msearch.py ... leansearch`, query “global sections preserves quasi-isomorphisms
  between bounded below complexes of acyclic sheaves of modules”: service
  unavailable, Internal Server Error; no verdict inferred from this failure.
- `msearch.py ... grep`, regex
  `quasiIso.*(sections|Sections|pushforward)|pushforward.*quasiIso`: zero hits.
- `rg` over `WeilConjectures` and `lean/Sheaf` for the same regex and the exact
  item id: no matching theorem. The broader search for `pushforwardSections` and
  `globalSectionsFunctor` found the existing evaluation/global-section definitions,
  not this statement. A further search for `quasiIso.*(Γ|global|Global|section|Section)`
  in Mathlib and the source found no exact match.
- Read `CategoryTheory.Functor.quasiIso_map_of_rightAcyclic` in the source module
  `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`: this is the general
  acyclic-complex tool recorded in the proof dependency, not this theorem with
  its geometric injectivity hypotheses. It is not redefined.
- Checked the proposed full declaration name in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No statement dispute, statement correction, new nodes, or dependency replacement
is needed. Only the named theorem is postponed with `sorry`. Server compilation
and the required delivery dry run are used for validation; nothing is built locally.

## Second reading by H1

Independent reading on 2026-10-11: the node and the delivered theorem agree. No
mismatch was found; the Lean module and node record were left unchanged.

Objects, hypotheses, and conclusions, in the node's order:

1. Schemes X, Y and an arbitrary morphism h: `{X Y : Scheme.{u}} (h : X ⟶ Y)`.
   Verdict: exact; no field, finiteness, properness, flatness, or separation assumption.
2. An integer cochain complex of O_X-modules: `I : CochainComplex X.Modules ℤ`.
   Verdict: exact. Read the dependency signatures: `Scheme`, `Scheme.Hom`,
   `CochainComplex`, and `SheafOfModules`; `Scheme.Modules` uses the canonical
   sheaf-of-modules category and abelian instance, with no chosen replacement.
3. Every I term injective: `hI : ∀ n : ℤ, Injective (I.X n)`.
   Verdict: exact. Read `CategoryTheory.Injective.factors`: extension against
   every mono, precisely the injective-object clause of def-sp-injective-resolutions.
   No augmentation or resolution of a particular object is required by this item.
4. I vanishes below zero: `hI0 : ∀ n : ℤ, n < 0 → IsZero (I.X n)`.
   Verdict: exact, invariant under choosing a zero object.
5. Termwise direct image: `((pushforward h).mapHomologicalComplex
   (ComplexShape.up ℤ)).obj I`. Verdict: exact. Opened TensorPullback's recorded
   declaration and its adjunction signature; its right adjoint is precisely this
   Mathlib `pushforward`, not a private direct image or the non-tensor pullback.
   Opened `pushforward_obj_obj` and `pushforward_map_app` in Modules.Sheaf:
   sections and differentials are computed on h's inverse image of the open.
6. An integer complex of O_Y-modules: `J : CochainComplex Y.Modules ℤ`.
   Every term injective and terms below zero vanish: `hJ` and `hJ0`.
   Verdict: exact, with the same category and zero conventions as I.
7. The specified quasi-isomorphism λ: `φ : ... ⟶ J`, `hφ : QuasiIso φ`.
   Verdict: exact. Read the dependency's `QuasiIsoAt`/homology-map characterization:
   it concerns the actual induced homology morphisms in the module-sheaf category.
8. Sections on Y: the local `let G` is definitionally Mathlib's
   `SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)`; opened its definition.
   Verdict: exact module-valued sections, with no new notion. The existing
   Scheme.Modules.globalSectionsFunctor is abelian-group-valued; the composite
   with `forget₂` here computes the same underlying sections and their maps.
9. Γ(Y,h_*I) = Γ(X,I): at the top open the inverse-image formula in item 5
   gives exactly I's sections and differentials on X, with scalars restricted
   along h's structure-sheaf map. Verdict: exact identification of the displayed
   source, not an extra hypothesis or an unrelated isomorphism. The formula is
   built into the source of the mapped φ; no separate comparison assertion is needed.
10. The result for O_Y(Y)-modules is the first `QuasiIso` conjunct; the result
    for abelian groups is the second, using `G ⋙ forget₂ ... AddCommGrpCat`.
    Verdict: exact. Every integer p is included in QuasiIso, so these express
    bijectivity of the actual induced H^p maps, with the same quantifier order.

Source verification: independently read the Stacks .tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
at remark-explain-arrow (01FB), lemma-before-Leray (01EZ),
remark-elucidate-lemma (01F0), and lemma-pushforward-injective (01EX), and
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex
at lemma-leray-acyclicity (015E). These concern arbitrary ringed-space morphisms,
so their specialization to schemes imposes no additional geometric hypotheses.
01EX supplies acyclicity, not preservation of injectives; the Lean makes that
correct distinction. 015E's definedness of RF is available from enough injectives
in this setting and need not be an additional theorem hypothesis. The docstring
faithfully retains all five proof steps of the node, including this setting.

Edge cases: zero complexes and empty schemes are admitted; the zero ring of
sections is admitted by ModuleCat. Integer degree 0 is unrestricted and negative
degrees are covered by the vanishing hypotheses. No characteristic is excluded.
There is no variable index set to require a nonemptiness assumption. The arbitrary
universe u is the standard universe of the dependency Scheme.Modules; it does not
force schemes or sections into a fixed small universe or quantify over a smaller
universe of test objects. No bounded-above restriction is present.

Independent searches used different wording from the first worker:

- LeanFinder through msearch.py: “Applying sections at the terminal open to a
  quasi-isomorphism between direct image of injective complexes and injective
  complexes”: eight hits, including InjectiveResolution.quasiIso,
  InjectiveResolution.instQuasiIsoIntι', and isKInjective_of_injective; none is
  this statement with geometric hypotheses.
- Loogle through msearch.py: `QuasiIso, SheafOfModules`: zero hits.
- LeanSearch through msearch.py: “The sections functor sends a quasi-isomorphism
  from the direct image of an injective complex to an injective complex to a
  quasi-isomorphism”: unavailable (Internal Server Error); no negative verdict
  is inferred from service failure.
- rg on Mathlib's AlgebraicGeometry and ModuleCat, source RightDerived, and
  project CategoryTheory with case-insensitive quasi-isomorphism/evaluation,
  sections, and pushforward patterns: no matching geometric theorem. Broader
  searches over WeilConjectures and lean/Sheaf found section functors and étale
  section comparisons, not this Zariski module statement. Opened the source
  `Functor.quasiIso_map_of_rightAcyclic` signature and docstring: it is the
  general proof tool, with acyclicity assumptions, not an existing declaration
  of this item's statement.

No new definition nodes, dependency modules, or statement correction are present
or needed. There is one named theorem with only `sorry`, no hollow definition,
no private category or functor definition, and all variables and universes are
bound. The node's lean.statement is verbatim the theorem signature. Server
single-file compilation and deliver2 preflight validate the delivery.
