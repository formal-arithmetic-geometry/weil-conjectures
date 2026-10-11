## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFinitePushforward` states
`AlgebraicGeometry.Scheme.exists_dense_open_lisse_finite_directImage`, with proof `sorry`.
It introduces no definitions. The node statement is unchanged.

Hypotheses and conclusion, clause by clause:

- “S a scheme”: `(S : Scheme.{u})`, with explicit universe `u`.
- “integral”: `[IsIntegral S]`, Mathlib's nonempty integral scheme predicate.
- “Noetherian”: `[IsNoetherian S]`, Mathlib's quasi-compact locally Noetherian scheme.
- “affine”: `[IsAffine S]`.
- “g:Z→S finite”: `{Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]`.
- “E an abelian etale sheaf on Z”: `(E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- “constructible”: `hE : IsConstructibleEtaleSheafOfSets ((sheafCompose
  Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E)`. This is the recorded
  dependency's constructibility of the underlying sheaf of sets: a finite constructible
  locally closed stratification, with finite locally constant restrictions. It includes
  finiteness of geometric stalks, as the node's definition of constructibility requires.
- “there is an open S°⊂S”: `∃ U : S.Opens`.
- “dense”: `Dense (U : Set S)`.
- “the direct image g_*E”: `(Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E`.
- “on S°”: apply `(etaleSetPullback U.ι).obj` to the underlying set-valued sheaf of this
  direct image, obtained with `sheafCompose S.smallEtaleTopology (forget AddCommGrpCat)`.
- “is lisse”: `IsLisseEtaleSheafOfSets` of that restriction. This is exactly finite
  locally constant, not merely locally constant with finitely generated abelian stalks.
  Local constancy of an underlying finite group sheaf is equivalent to local constancy
  as a group sheaf: after a set trivialization, shrink etale locally to fix the finitely
  many values of its multiplication, inverse, and identity operations.

Dependencies read and used:

- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`. Read its docstring and signature: continuous
  pushforward along base change, objectwise E(V×_S Z), with the Grothendieck abelian
  coefficient category specialized to `AddCommGrpCat.{u+1}`. The derived declaration in
  this node is not needed for this underived statement.
- `def-weil-pbc-etale-sheaves`: `Sheaf.AlgebraicGeometry.EtaleSheaves`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`,
  `IsLisseEtaleSheafOfSets`, and `etaleSetPullback`; their definitions and docstrings
  were read in full. This module transitively imports the direct-image module.
- `def-weil-pbc-scheme-conventions`: a convention node with no declaration of its own.
  Its explicit record directs users to Mathlib's `Scheme`, `IsAffine`, `IsFinite`, etc.
  These are used, with `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
  `Mathlib.AlgebraicGeometry.Noetherian`. Mathlib's `IsIntegral` was read in
  `Mathlib.AlgebraicGeometry.Properties`; it includes nonemptiness, as required.
- `CategoryTheory.sheafCompose` (Mathlib, Sites/Whiskering) was read, and composes
  a sheaf with the usual forgetful functor; it does not redefine an etale sheaf.

The source blueprint file was absent from this read-only clone's literature tree.
Read the entire original file at the identical path on the server over SSH instead.
Its statement is word for word the node's statement. Its proof explicitly uses finite
locally constant sheaves, confirming the finite-stalk interpretation. The declaration
has a docstring carrying all six DAG proof steps and their dependency identifiers.

Edge cases checked before writing:

- Empty Z is allowed, and the direct image is the zero group sheaf; its underlying
  singleton sheaf is finite locally constant. No nonemptiness or surjectivity of g
  is imposed.
- E=0 is allowed, with the same conclusion, and U=S is possible.
- The empty S is excluded by integral, exactly as Mathlib and the source require;
  over a nonempty S a dense open is automatically nonempty. No separate nonempty
  hypothesis is added.
- Components not dominating S may all disappear after shrinking; the statement
  imposes no dominance or reducedness on Z.
- Purely inseparable finite maps and nilpotent thickenings are allowed in every
  characteristic; no etaleness of g or invertibility of torsion orders is assumed.
- Dimension-zero integral affine bases and arbitrary positive-characteristic
  residue fields are included. The dense open can be the whole base.
- The universe is arbitrary; sheaf values use the established small-etale-site
  convention `u+1` and no finite-cardinality bound is imposed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "finite morphism pushforward constructible abelian etale
  sheaf lisse on dense open"`: eight hits, all about constructibility of scheme/ring
  images and preimages; none is a sheaf direct-image theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.lowerStar, Dense"`: zero hits;
  unknown identifier `AlgebraicGeometry.Etale.lowerStar` in the Mathlib search index.
- `msearch.py ... grep "finite.*pushforward|lowerStar.*dense|generic.*constructible"
  AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "finite pushforward constructible etale sheaf locally
  constant dense open"`: service unavailable, Internal Server Error.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for the node id and generic/direct-image
  expressions: no exact statement. Source `ConstructibleSheaf/GenericConstancy.lean`
  gives generic constancy of a sheaf already known constructible, not this finite
  direct-image statement. `ConstructibleSheaf/FinitePushforward.lean` gives embeddings
  into finite sums, not this result. `NormalGenericConstant.lean` concerns the reverse
  direction (pushforward from a generic point on a normal base), not this theorem.
- Read the source's `ConstructibleSheaf/Defs.lean` in full. Its abelian-category
  `IsFiniteLocallyConstantSheaf` uses finitely generated stalks, so it is not the
  finite-stalk predicate of this node. Reuse the recorded set-valued predicates
  rather than redefining lisse or weakening it.
- Searched `lean/Sheaf` for the recorded predicates: the landed
  `ConstructibleFiniteSelection.lean` uses the same underlying-set construction for
  constructible abelian sheaves, confirming the project's convention.

No statement correction, new node, dependency replacement, or disputed statement.

## Second reading by E1

I independently read the node statement and the theorem signature in
`Sheaf/AlgebraicGeometry/GenericFinitePushforward.lean` clause by clause. The objects
and hypotheses match as follows:

- The integral Noetherian affine base is `S : Scheme.{u}` with instances
  `[IsIntegral S] [IsNoetherian S] [IsAffine S]`. `IsIntegral` supplies the
  nonempty integral scheme condition; no extra reducedness or dominance is assumed.
- The finite morphism is `{Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g]`, with the
  same universe as `S` and no etaleness, surjectivity, or characteristic hypothesis.
- The abelian etale sheaf is
  `E : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Constructibility is exactly the recorded set-valued convention, expressed by
  `hE : IsConstructibleEtaleSheafOfSets ((sheafCompose Z.smallEtaleTopology
  (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)`; this is the underlying
  sheaf of the abelian object, rather than a private abelian constructibility notion.
- The conclusion is `∃ U : S.Opens, Dense (U : Set S) ∧ ...`; the restricted direct
  image is the underlying set sheaf of
  `(Etale.lowerStar AddCommGrpCat.{u + 1} g).obj E`, pulled back by
  `(etaleSetPullback U.ι).obj`, and the final predicate is exactly
  `IsLisseEtaleSheafOfSets`.

Quantifier order and all conjunctions agree with the node. The lower star is the
recorded `AlgebraicGeometry.Etale.lowerStar`, and the lisse, constructible, and
set-pullback predicates are the declarations in `Sheaf.AlgebraicGeometry.EtaleSheaves`;
no duplicate notions were introduced. The file compiles cleanly with
`scompile.py`; the only proof placeholder is the theorem's required `sorry`.

Edge cases checked: empty `Z` and zero `E` are allowed; the direct image is then a
finite locally constant singleton sheaf. The integral hypothesis excludes an empty
base, while `U = ⊤` is allowed. Components of `Z` need not dominate `S`; finite
purely inseparable maps and nilpotent thickenings are included. Dimension-zero and
positive-characteristic bases are included, and the explicit universe `u` with sheaf
values in `u + 1` imposes no additional restriction.

I repeated the existing-definition searches using LeanFinder/Loogle/grep and `rg` in
both the source checkout and `lean/Sheaf`, including searches for lower-star finite
pushforward, generic lissity, and constructible direct images. No exact declaration
exists besides this delivery. The source `Etale.lowerStar` and the project's
set-valued predicates were inspected and match the uses above. No mismatch was found,
so no statement, dependency, or node field was changed.
