## Worker report

The module `Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity` states
`AlgebraicGeometry.coproduct_fpqc_effectivity`, with its sole proof `sorry`.
The node's natural-language statement and all its dependencies are unchanged.
No helper definitions, additional nodes, or dependency repairs are needed.

Clause-by-clause correspondence:

- Schemes X and V and the morphism p: `{X V : Scheme.{u}}` and `(p : V ⟶ X)`.
  The affine chart hypothesis is `[IsAffine V]`.
- The singleton fpqc covering is precisely
  `hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage X`.
- An arbitrary label set is `S : Type v` with `[Small.{u} S]`. This is the
  explicit size bound for the chosen category `Scheme.{u}`, not finiteness or
  nonemptiness: Mathlib's chosen coproduct accepts any u-small label type,
  including a type presented in another universe v. Enlarge u to include any
  chosen label set under the node's size convention.
- T is Mathlib's chosen `∐ fun _ : S => V`, and its structure map is
  `Sigma.desc (fun _ : S => 𝟙 V)`. The binder `D` is any
  `Over.DescentDatum p (Over.mk ...)`, using exactly the recorded upstream
  transport-form descent datum, equivalent by Yoneda to the isomorphism and
  cocycle on the double and triple fibre products.
- Every affine open B of V is `∀ (B : V.Opens), IsAffineOpen B → ...`.
  Every open K of T ×_V B is the binder with type
  `(pullback (Sigma.desc (fun _ : S => 𝟙 V)) B.ι).Opens`.
  Its quasi-compactness is the hypothesis `IsCompact (K : Set ...)`.
- The finite subset is `∃ (J : Finset S)`. D in the mathematical statement
  (distinct from the Lean datum named D) is `∐ fun _ : J => B.toScheme`.
  Its affineness is the first `IsAffine` conjunct. Containment of K as an
  open subscheme is the existential morphism j and `IsOpenImmersion j`.
  The two displayed equalities specify its composites to T and to B:
  component s is mapped to T by `B.ι ≫ Sigma.ι (fun _ : S => V) s.val`,
  and to B by its identity. Thus j expresses the actual inclusion in the
  indicated finite subcoproduct, rather than an unrelated open embedding.
- Every smaller affine open is
  `∀ (B' : B.toScheme.Opens), IsAffineOpen B' → ...`, with the SAME J.
  D' is `∐ fun _ : J => B'.toScheme`; its affineness is asserted.
  K' is the literal `pullback (K.ι ≫ pullback.snd ... B.ι) B'.ι`.
  `CompactSpace` on that scheme asserts quasi-compactness without any
  Hausdorff assumption. The existential j' is its open immersion into D'.
  Its two equalities give the canonical restriction of j into D and the
  projection to B'; these are exactly the base-change inclusion over B'.
- The final local conjunct is
  `IsQuasiAffineHom (K.ι ≫ pullback.snd ... B.ι)`, the quasi-affine morphism
  K → B in the dependency's recorded sense. Mathlib's absolute notion
  `Scheme.IsQuasiAffine` includes quasi-compactness, as the node requires.
- The final outer conjunct `D.IsEffective` says that there is an X-scheme
  with a pullback identification with T inducing this very datum. The
  recorded definition is an existential invariant morphism with an
  `IsPullback` square; its universal property yields the stated isomorphism
  Y ×_X V ≅ T over V. It includes compatibility with the datum, not just
  an isomorphism of underlying schemes.
- No finiteness of S, quasi-compactness of T → V, Noetherian assumption,
  or nonemptiness hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (available through the public imports).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
- `Mathlib.AlgebraicGeometry.Limits`: the small-index scheme coproduct
  instance, `AlgebraicGeometry.sigmaOpenCover`, and
  `AlgebraicGeometry.disjoint_opensRange_sigmaι`; the statement uses its
  chosen coproduct and `CategoryTheory.Limits.Sigma.ι` / `Sigma.desc`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and its `IsEffective` definition.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (publicly available through Limits).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` and `IsCompact`.
- The finite affine coproduct instance is in
  `Mathlib.AlgebraicGeometry.Limits`. The affine scheme compact-space
  instance is in `Mathlib.AlgebraicGeometry.AffineScheme`; the affine
  quasi-separated-space instance is in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (proof import).
- `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent` (proof import):
  `CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc`.
  Its full signature has exactly the local quasi-affine condition proved
  here and the same singleton covering and effectiveness encoding.
- `def-weil-size-convention` is metatheoretic, with no declaration;
  universes u, v and the explicit smallness bound implement it.

Sources checked: the current blueprint scheme proof (2); Stacks
more-morphisms, definition-ind-quasi-affine and
lemma-ind-quasi-affine-alternative-definition; more-groupoids,
lemma-ind-quasi-affine (Gabber). The blueprint's claim that the whole
infinite coproduct is quasi-affine is not used: the accepted node already
correctly states the finite-open and ind-quasi-affine version.

Edge cases checked before writing: S empty (T and each K are empty; choose
J empty, and the finite coproduct is the affine empty scheme); V empty
(the fpqc covering forces X empty); K empty (J empty allowed); B or B'
empty; S infinite with V = Spec k (K lies in finitely many components,
while T need not be quasi-compact). The smaller affine open uses the same
finite labels, and its intersection is computed inside the SAME affine D.
No extra assertion that T itself is quasi-affine occurs.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “Any descent datum on an arbitrary
  coproduct of copies of an affine scheme is effective for an fpqc
  covering”: eight hits, consisting of affine-transition-limit auxiliary
  declarations and generic effective-epimorphism lemmas. None asserts
  scheme descent effectivity with the finite-component clauses.
- `msearch.py loogle`, query `AlgebraicGeometry.Scheme, "descent"`:
  zero hits.
- `msearch.py grep`, query
  `ind.?quasi.?affine|effective.*descent|descent.*effective` restricted to
  Mathlib AlgebraicGeometry: zero hits.
- `rg` in both live `WeilConjectures` and `Sheaf`, queries
  `coproduct.*[Ee]ffect|[Cc]oproduct.*[Ff]pqc|indQuasiAffine` and the item
  id: the general ind-quasi-affine theorem and permanence definition were
  found, but neither is this coproduct theorem with all its conclusions.
- Name-clash search in both source roots and the upstream-name index for
  `coproductFpqc|coproduct_fpqc|finiteComponent|finite_component` found
  only unrelated finite-component declarations.

No statement dispute or node fault was found. All variables are explicitly
bound; `set_option autoImplicit false` enforces this in the delivered file.

## Validation

The initial compiler pass required explicit `(C := Scheme.{u})` on
pullbacks used as underlying types in `Set` and `CompactSpace`. These
annotations repair category inference without changing the mathematical
statement. The module is compiled individually with the prescribed
`scompile.py`; dry run and delivery use only `deliver2.py`.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
