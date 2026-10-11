## Worker report

The module Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent states
AlgebraicGeometry.finiteSurjectiveSetDescent, with its proof `sorry`. The two fully
written section-map definitions only render the maps already specified in the node;
they introduce no replacement inverse image or fibre product.

Hypotheses and objects:
- Schemes X, X′: `{X X' : Scheme.{u}}`; the morphism is `f : X' ⟶ X`.
- Finiteness: `[IsFinite f]`; surjectivity: `[Surjective f]`.
- X″ is the chosen `pullback f f`, and p₁,p₂ are `pullback.fst f f` and
  `pullback.snd f f`. Their common composite is the first projection followed by f;
  `pullback.condition` identifies the second composite with it.
- The sheaf G is `Sheaf X.smallEtaleTopology (Type (u + 1))`.
- Γ(X,G) is `G.obj.obj (op (Scheme.Etale.mk (𝟙 X)))`. For the other global sections,
  evaluation uses the base change of this identity neighbourhood, which is canonically
  X′, and its iterated/composite base changes, which are canonically X″. These are exactly
  the fibre-product identifications explicitly allowed by the node.

Maps and conclusions:
- `etaleSetDescentUnit` is the actual unit of the adjunction whose left adjoint is
  `Scheme.etaleSetPullback`. Its value at the identity neighbourhood is f* on sections.
- `etaleSetDescentComparison f g G U s` first uses the unit for g on f⁻¹G, then
  applies the composition isomorphism chosen from
  `etaleSetInverseImageCompositionUnits.2.2`, and finally uses the presheaf map
  of the canonical `MorphismProperty.Over.pullbackComp` to identify iterated
  with composite base change. The choice is from the recorded existential statement;
  the uniqueness clause there makes it the specified unit-compatible comparison.
- The first conjunct is `Function.Injective` of f* at the identity neighbourhood.
- The quantified iff says that a section s′ lies in the image (`∃ s, f* s = s′`)
  exactly when its two projection pullbacks, followed by c, agree. `eqToHom` of
  `congrArg` applied to `pullback.condition.symm` transports the second section
  to the first composite's section type. This is equality in Γ(X″, f₁⁻¹G), not
  merely existence of an unspecified comparison. Injectivity plus this iff is
  precisely the equalizer assertion.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: AlgebraicGeometry.Surjective.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback, pullback.fst, pullback.snd, pullback.condition.
  The schemes' pullback instance is imported transitively.
- Mathlib.CategoryTheory.Sites.Sheaf: CategoryTheory.Sheaf; the dependency is a
  Mathlib leaf whose mathlib_match supplies this declaration.
- Mathlib.AlgebraicGeometry.Sites.Etale: Scheme.smallEtaleTopology.
- Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits:
  AlgebraicGeometry.etaleSetInverseImageCompositionUnits (signature and docstring read).
- Sheaf.AlgebraicGeometry.EtaleSheaves: Scheme.etaleSetPullback, used through the
  recorded composition dependency; its complete definition was read.

Edge cases checked: empty X forces empty X′ by the existence of f; all evaluations
remain defined, and global sections of a sheaf on the empty scheme are singleton.
For nonempty X, surjectivity prevents empty X′. No nonemptiness, connectedness,
Noetherianity, field, or étaleness of f was imposed. Identity f and disconnected finite
covers are included. G may be the initial/empty sheaf. All universes and variables
are explicit, and the coefficient universe agrees with the recorded inverse image.
No statement correction, disputed statement, new node, or dependency repair is needed.

Searches (2026-10-11):
- msearch.py leansearch: “finite surjective scheme morphism equalizer global sections
  etale sheaf of sets”; service unavailable (Internal Server Error), recorded without
  a mathematical verdict.
- msearch.py leanfinder: “finite surjective morphism of schemes descent global sections
  of etale sheaves of sets equalizer”; eight hits concern affine transition limits,
  scheme pullback carriers, coherent topology, and standard étale algebras; no match.
- msearch.py loogle: “AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective,
  CategoryTheory.Sheaf”; zero hits.
- msearch.py grep: “finite.*descent|surjective.*descent|09Z3”, AlgebraicGeometry;
  one hit in Morphisms/FlatDescent.lean is descent of the surjective morphism property,
  not descent of sheaf sections.
- rg on WeilConjectures and lean/Sheaf for the node id, 09Z3 and our declaration names:
  only GabberH0EtaleCriterion's proof docstring invokes this node; no declaration.

Source checked directly at https://stacks.math.columbia.edu/tag/09Z3 and
https://stacks.math.columbia.edu/tag/09Z2 because this machine does not carry the
literature/stacks-project/etale-cohomology.tex file. Remark 09Z3 gives exactly the
sets equalizer; Lemma 09Z2 assumes precisely finite and surjective.

Validation: server scompile.py compiles the module with no errors or warnings.


## Second reading by G1

I independently opened the node, its five statement-dependency nodes, the delivered
module, the composition-units module and the definition of `Scheme.etaleSetPullback`.
The local Stacks .tex file is absent; I read [Remark 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
and [Lemma 09Z2](https://stacks.math.columbia.edu/tag/09Z2) directly. The former is
exactly the sets equalizer; the latter supplies precisely finite and surjective,
with no ambient Noetherian, separation, field or characteristic hypothesis.

Object/hypothesis/conclusion checklist, with verdicts:
- Schemes X and X′: `{X X' : Scheme.{u}}`. Same unrestricted schemes; PASS.
- Map f:X′→X: `(f : X' ⟶ X)`. Direction and quantification agree; PASS.
- Finite f: `[IsFinite f]`. I read Mathlib's class: affine plus finite section
  ring map on every affine open, exactly the finite clause of the dependency; PASS.
- Surjective f: `[Surjective f]`. I read `surj : Function.Surjective f`,
  underlying topological points, exactly the dependency; PASS.
- X″ and p₁,p₂: `pullback f f`, `pullback.fst f f`, `pullback.snd f f`.
  I read the chosen limit/projection declarations; schemes have pullbacks; PASS.
- Common composite f₁: first branch uses `pullback.fst f f ≫ f` through the
  comparison definition; the second uses `pullback.snd f f ≫ f`. The `eqToHom`
  applies `congrArg` to `pullback.condition.symm`, transporting from the second
  composite to the first, including its sheaf and evaluation object; PASS.
- Sheaf of sets G: `Sheaf X.smallEtaleTopology (Type (u + 1))`. The topology is
  Mathlib's small étale topology, generated by jointly surjective étale families,
  and `Sheaf` is the dependency's existing notion; PASS.
- Γ(X,G): `G.obj.obj (op (Scheme.Etale.mk (𝟙 X)))`; identity is terminal
  on the small site. Γ(X′,f⁻¹G) is evaluated at its base change along f, a
  terminal étale neighbourhood canonically isomorphic to X′. The conclusion
  uses this identification expressly allowed in the node; PASS.
- Inverse images: `Scheme.etaleSetPullback`, read as the actual left Kan
  extension followed by sheafification, not another chosen functor; PASS.
- f* and p_j*: `etaleSetDescentUnit` expands to the very adjunction unit
  appearing in the composition dependency; the comparison applies this unit
  to the section of f⁻¹G. No arbitrary section map is assumed; PASS.
- c and fibre-product identifications: `Classical.choose
  etaleSetInverseImageCompositionUnits.2.2` selects the dependency's existential
  natural isomorphism. Its fixed-sheaf uniqueness and unit equation characterize
  the source's comparison. I checked `Over.pullbackComp`: its hom goes from
  composite to iterated base change. Presheaf evaluation on its opposite thus
  sends the comparison's iterated section to the composite evaluation. This is
  the canonical pasting identification with the correct direction; PASS.
- Injectivity: the first conjunct is `Function.Injective` of f* at the
  identity neighbourhood, exactly the node's first conclusion; PASS.
- Image exactly the agreement set: `∀ s', comparison₁ s' = transported
  comparison₂ s' ↔ ∃ s, unit s = s'`. Both implications and all sections are
  included, with no chosen lift and no extra compatibility hypothesis; PASS.
  Together with injectivity this is the asserted equalizer of sets, without
  strengthening it to descent of other objects.

Edge cases: the empty scheme is included; a map to the empty scheme forces its
source empty, and empty-cover sheaf conditions make their global sections terminal.
No nonemptiness is imposed on the schemes or sheaf sections. The initial sheaf,
identity maps, disconnected finite covers, nonflat finite covers and every
characteristic are covered. There is no variable index set, degree n, or coefficient
ring to restrict; the double fibre product is the n=0 equalizer case. The single
explicit universe u is arbitrary, and set values in Type (u+1) match the recorded
inverse-image construction. Larger scheme/set sizes can be accommodated by enlarging
u; no test-object universe hypothesis can become vacuous. All variables and
universes are explicitly bound.

Independent searches used different terms from the worker:
- LeanSearch: “descent of sections of sheaves of sets under finite surjective
  scheme maps”; unavailable with Internal Server Error (no mathematical verdict).
- LeanFinder: “equalizer of sections for a finite covering of schemes in the
  small etale topology”; eight affine-transition-limit hits, none this statement.
- Loogle: `Function.Injective, CategoryTheory.Sheaf`; two general local-injectivity
  and monomorphism lemmas, neither finite-surjective descent.
- rg over Mathlib AlgebraicGeometry, WeilConjectures and the project's lean/Sheaf
  for cohomological descent, equalizer with finite/étale, 09Z3 and the three full
  declaration names; no existing exact statement or existing section-map wrapper.
  I opened `EtaleSectionsFpqcDescent`: it assumes an fpqc family, so its singleton
  case requires flatness absent here. I also opened upstream `Finite/PieceEqualizer`:
  it equalizes two neighbourhood morphisms after shrinking, not sheaf sections.
  The upstream-name registry contains none of the delivered declaration names.

No mismatch found; no Lean, node statement or dependency changes made. There are
no new nodes, dependency modules, or stage-2 statement corrections to review.
The two definitions are transparent compositions of existing maps with no sorry
in their data. The sole theorem is left `sorry`, as stage 2 requires. The module
and every declaration carry the exact source/blueprint reference; the theorem's
numbered docstring matches all ten node proof steps and their cited tools.
No local notation, private definition, hidden let binder, or unused assumptions
are introduced in this delivery. The theorem signature in the node is unchanged
and agrees verbatim with the module.

Second-reader validation: scompile.py compiled the complete delivery in 2.1 s,
exit 0, with no warnings. A literal signature comparison passed, and every Lean
line is within 100 columns.
