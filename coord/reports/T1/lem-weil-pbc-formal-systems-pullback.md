## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FormalSystemsPullback.lean` states
`AlgebraicGeometry.exists_formalSystemsPullback`. Its only proof is `sorry`; it introduces
no definitions, instances or private notation. No node correction or dependency repair was needed.

Hypotheses and clauses, with the node and all three statement dependencies read:

- A morphism of Noetherian schemes: `{X Y : Scheme.{u}}`, `[IsNoetherian X]`,
  `[IsNoetherian Y]`, and `(f : X ⟶ Y)`. No properness, finite-type or flatness assumption
  is imposed on f.
- A quasi-coherent ideal J of O_Y: `(J : Y.IdealSheafData)`. The extended ideal I is
  `J.comap f`, Mathlib's ideal of the inverse image closed subscheme. The recorded
  declaration of `def-nagata-extended-ideal` is precisely this `comap`. No second ideal
  extension is defined.
- (1) The pulled-back system is an object of Coh(X,I), and this defines a functor:
  `P : CoherentFormalModule Y J ⥤ CoherentFormalModule X (J.comap f)` together with
  `P ⋙ ObjectProperty.ι (IsCoherentFormalModule (J.comap f)) =
  ObjectProperty.ι (IsCoherentFormalModule J) ⋙
  (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj (Scheme.Modules.tensorPullback f)`.
  This equality fixes every object, transition and compatible family of morphisms to
  the termwise tensor pullback. Membership in the full subcategory asserts coherence,
  annihilation by I^(n+1), and the transition quotient isomorphisms. Functor structure
  includes identities and composition.
- (2) For coherent G the isomorphism is natural in G:
  `Nonempty (completion Y J ⋙ P ≅ C ⋙ completion X (J.comap f))`.
  Here `C : CoherentModules Y ⥤ CoherentModules X` is constrained by its equation
  after inclusion to be the same tensor pullback on coherent modules. It is the
  necessary typed restriction of f*, not an extra hypothesis or an arbitrary functor.
  A functor isomorphism supplies compatible level isomorphisms and naturality for every
  coherent module morphism, rather than only separately chosen object isomorphisms.
- For inclusion of an open U, f* is restriction:
  `∀ U : Y.Opens, Nonempty (Scheme.Modules.tensorPullback U.ι ≅
  Scheme.Modules.restrictFunctor U.ι)`.
- The final equality of restricted completions is the second `Nonempty` under that
  quantifier. Its left functor is completion followed by termwise restriction; its
  right functor is restriction followed by `formalCompletionFunctor (J.comap U.ι)`.
  Both have domain `CoherentModules Y`, so naturality is retained. On an open subscheme
  `J.comap U.ι` is the restricted ideal J|_U. The comparison is expressed in the
  ambient inverse-system category; all these systems are coherent adic systems by
  the first clause applied to U.ι and the restriction/pullback isomorphism. Because
  Coh(U,J|_U) is a full subcategory, this is equivalent to an isomorphism in Coh.
  The node's final equality is interpreted as its stated natural identification,
  not literal equality of independently chosen cokernel objects.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.CoherentModules`,
  `IsCoherentFormalModule`, `CoherentFormalModule`, `completion`,
  `formalCompletionFunctor`. Read the complete file, including the cokernel quotients,
  reductions, and the positive-level index convention.
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, with its full signature, tensor
  object/map definitions, functor laws and adjunction docstrings read.
- `Sheaf.AlgebraicGeometry.Coherent` (through the formal-module import):
  `AlgebraicGeometry.RingedSpace.IsCoherent`, full definition read. This is the actual
  finite-type plus finite-type-kernels predicate recorded by `pqf-def-coherent`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`; read its definition and `comapIso`.
- Mathlib's `Scheme.Modules.restrictFunctor`, `Functor.whiskeringRight`, and
  `ObjectProperty.ι`; their definitions/docstrings were read in the local checkout.

Edge cases checked before writing: zero coherent modules and zero systems are included;
J=0 gives constant systems and ordinary pullback; J=O_Y gives zero completions and only
zero formal systems; no condition excludes empty X or Y, the empty open U, or U=Y.
Level `op 0` means mathematical level 1, so no unwanted level-0 condition is added.
No characteristic is excluded. Both schemes and their module sheaves use the shared
universe u of the recorded dependencies, with u explicitly declared and all variables
explicitly bound. No quantification over smaller test objects or independent index
universe is introduced. The inverse-system index is the existing ℕᵒᵖ encoding.

Sources checked: the local `literature/stacks-project/coherent.tex` is absent on this
machine, so the actual source places were opened at
[Stacks 0887](https://stacks.math.columbia.edu/tag/0887) and
[Stacks 088B](https://stacks.math.columbia.edu/tag/088B).
0887 gives termwise pullback; the proof of 088B gives the completion identification.
The node intentionally omits 0887's right-exactness and flat exactness assertions, and
this statement omits them too. The seven node proof steps are carried in the theorem
 docstring, including naturality and the open restriction argument.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "pullback coherent adic inverse systems completion commutes
  with pullback"`: eight hits, involving algebraic AdicCompletion and unrelated
  geometric pullback isomorphisms; no coherent formal-system functor statement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.IdealSheafData.comap"`: twelve hits;
  confirmed the existing extended-ideal operation and its functorial properties.
- `msearch.py ... leansearch "pullback of coherent formal modules commutes with
  completion"`: service unavailable, Internal Server Error, recorded as unavailable.
- `msearch.py ... grep 'formal.*pullback|pullback.*formal|completion.*pullback'
  AlgebraicGeometry`: two unrelated formally-unramified morphism hits, no match.
- `rg -n 'formal.*[Pp]ullback|[Pp]ullback.*formal|completion.*pullback'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: unrelated Fourier-transform and
  étale topological invariance hits only.
- `grep -rn 'lem-weil-pbc-formal-systems-pullback'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg` over `lean/Sheaf` for extended ideals, formal pullback, and coherent tensor
  pullback: ideal base-change and unrelated lifting statements; no statement of this
  node. Searching `formalCompletion|CoherentFormalModule` finds only the shared
  definition module, which is imported rather than duplicated.
- Collision check for `FormalSystemsPullback|exists_formalSystemsPullback` in
  `dag/lean_names_upstream.json`, Mathlib, the source project, and `lean/Sheaf`:
  no pre-existing declaration or module.

Validation: the server single-file compile passed cleanly in 2.8 s after correcting
`whiskeringRight` to its actual namespace `Functor.whiskeringRight`. No extra warnings.
The delivery dry run is run as the final worker check; no push and no self-written
second-reading section.

## Second reading by T1

I independently read the node statement, its source places (Stacks 0887 and 088B),
the three statement dependencies, and `FormalSystemsPullback.lean`.

- The objects and hypotheses match: Lean binds schemes `X Y : Scheme.{u}`,
  `[IsNoetherian X]`, `[IsNoetherian Y]`, a morphism `f : X ⟶ Y`, and
  `J : Y.IdealSheafData`; `J.comap f` is the recorded extended ideal.
  No properness, finite type, flatness, characteristic, or extra universe
  restriction is assumed.
- Clause (1) is rendered by the existential `P` with codomain
  `CoherentFormalModule X (J.comap f)` and the equality after full-subcategory
  inclusion to termwise `Scheme.Modules.tensorPullback f`.  This fixes the
  pulled-back objects, transitions, and morphisms and therefore states the
  functor assertion exactly.
- Clause (2) is rendered by the existential coherent-module functor `C`, its
  inclusion equality with tensor pullback, and
  `Nonempty (completion Y J ⋙ P ≅ C ⋙ completion X (J.comap f))`.  This is the
  natural isomorphism for every coherent module, with the required typed
  restriction of pullback.
- The open-subscheme clause is rendered for every `U : Y.Opens` by the natural
  isomorphism between `tensorPullback U.ι` and `restrictFunctor U.ι`, followed by
  the natural isomorphism between restricted completion and completion for
  `J.comap U.ι`.  The ambient inverse-system functors and full-subcategory
  inclusion preserve the node's natural identification.

Edge cases remain covered: zero systems and zero modules, `J = 0`, `J = O_Y`,
empty schemes and opens, `U = Y`, positive levels encoded by `op n` with `n+1`,
all characteristics, and the shared universe `u`. No index universe or test-object
case is lost.

Searches found no existing statement or declaration in Mathlib, `WeilConjectures`,
or `lean/Sheaf`; the only matches were the shared definitions and unrelated
pullback/completion results. LeanSearch was unavailable (internal server error),
while LeanFinder/Loogle and grep searches were completed as recorded in the
worker report. The dependency declarations were checked at their source files,
including `IdealSheafData.comap`, `tensorPullback`, `CoherentFormalModule`, and
`RingedSpace.IsCoherent`.

No mismatch was found. The module compiled cleanly with `scompile.py`; no repair was
needed.
