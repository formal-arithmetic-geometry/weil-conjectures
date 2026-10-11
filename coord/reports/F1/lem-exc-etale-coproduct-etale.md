## Worker report

The module states `AlgebraicGeometry.etale_sigmaDesc_spec_of_finite_separable`
with a `sorry` proof. Source: Stacks Project, Morphisms, Lemma 02GL, converse
direction, read in `/home/ubuntu/c1-stacks-review/morphisms.tex:8175` because
the repository's `literature/stacks-project/` checkout is absent here.

Statement correspondence:

- Base field K: `(K : Type u) [Field K]`.
- Arbitrary index set I: `(I : Type u)`, with polymorphic `u`; no nonempty or
  finite restriction.
- Field extension L_i/K: `(L : I → Type u)`, `[∀ i, Field (L i)]`, and
  `[∀ i, Algebra K (L i)]`, using the Mathlib field-extension convention.
- Finiteness of each extension: `[∀ i, Module.Finite K (L i)]`.
- Separable algebraicity of each extension: `[∀ i, Algebra.IsSeparable K (L i)]`.
  The Mathlib class includes algebraicity through separability of the minimal
  polynomial.
- The coproduct scheme and its map to Spec K: `Sigma.desc (fun i : I =>
  Spec.map (CommRingCat.ofHom (algebraMap K (L i))))`. `Sigma.desc` has source
  the categorical coproduct of the schemes `Spec (CommRingCat.of (L i))` and
  target `Spec (CommRingCat.of K)`; its restriction to each coprojection is
  the algebra-map-induced spectrum morphism.
- The conclusion that this morphism is etale: `Etale (...)`.

Dependency declarations read in full:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`, with
  `algebraMap` the ring map; `RingHom.toAlgebra` for a supplied map.
- `def-weil-pbc-separable-algebraic-extension`:
  `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable`.
- `def-weil-etale-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `lem-weil-pbc-scheme-coproduct-family`:
  `Mathlib.AlgebraicGeometry.Limits`, `instHasColimitsOfShapeDiscreteSchemeOfSmall`,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι`.

Edge cases: `I = Empty` is allowed; its source is the empty coproduct and the
statement remains meaningful. A singleton `I` gives one spectrum map. No
restriction is placed on the characteristic of K. Each `L i` is a field, so
zero rings are excluded exactly as in the node. The universe is polymorphic;
the index and field types lie in the scheme universe needed for the coproduct.

Searches for an existing statement or duplicate notion:

- `msearch.py leanfinder`, query "coproduct of spectra of finite separable
  field extensions is etale over the base field": eight hits, including
  `Algebra.Etale.iff_exists_algEquiv_prod` for finite products, but no exact
  arbitrary coproduct statement.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Etale, IsZariskiLocalAtSource.sigmaDesc,
  Algebra.IsSeparable`: no hit; the service reported the latter coproduct
  lemma as an unknown identifier for that query.
- `msearch.py grep` in `AlgebraicGeometry`, query
  `sigmaDesc|finite.*separable.*[Ee]tale|[Ee]tale.*[Cc]oprod`:
  found `IsZariskiLocalAtSource.sigmaDesc` and generic coproduct APIs,
  but no theorem with the component finiteness/separability hypotheses.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `coprod.*Etale|Etale.*coprod|finite.*separable|sigmaDesc`: found binary
  `Etale.coprodDesc` and uses of the generic `sigmaDesc` lemma, not this
  statement. `grep -rn "lem-exc-etale-coproduct-etale"` found nothing.
- `rg` in the repository's `lean/Sheaf` for etale coproduct and finite
  separable patterns found nothing. An exact search for the new declaration
  in Mathlib, source, and Sheaf also found nothing.

The server compiler reported a clean compile, exit code 0.

## Second reading by F1

Independent reading of the node, its four statement dependencies, the Lean
module, and Stacks Project, Morphisms, Lemma 02GL (converse direction), at
`/home/ubuntu/c1-stacks-review/morphisms.tex:8175`. Verdict: the signature
states the node exactly; no signature or node repair was needed.

- Base field: node `K` a field; Lean `(K : Type u) [Field K]`. The source
  places no restriction on characteristic, and neither does Lean.
- Index set: node any set `I`; Lean `(I : Type u)`, with no `Finite` or
  `Nonempty` instance. Its universe varies with `u` and is small enough for
  the coproduct in `Scheme.{u}`; no cardinality bound is fixed.
- Extensions: node each `L_i/K` a field extension; Lean `(L : I → Type u)`,
  `[∀ i, Field (L i)]`, `[∀ i, Algebra K (L i)]`. The last instance provides
  `algebraMap K (L i)`, exactly the field-extension map of dependency
  `def-pc-field-extension` (`Algebra`, Mathlib/Algebra/Algebra/Defs.lean).
- Finite: node each extension finite over `K`; Lean
  `[∀ i, Module.Finite K (L i)]`. This is module finiteness, not finiteness
  of the index set or a Noetherian assumption.
- Separable algebraic: node each extension separable algebraic; Lean
  `[∀ i, Algebra.IsSeparable K (L i)]`. Dependency
  `def-weil-pbc-separable-algebraic-extension` identifies this Mathlib class;
  `Algebra.IsSeparable.isAlgebraic` confirms that algebraicity is included.
- Source and map: node `coprod_i Spec L_i → Spec K`; Lean
  `Sigma.desc (fun i : I => Spec.map (CommRingCat.ofHom
  (algebraMap K (L i))))`. `Spec.map` reverses the algebra map, and
  `Sigma.desc` has source the scheme coproduct. Dependency
  `lem-weil-pbc-scheme-coproduct-family` records Mathlib's scheme
  coproduct and its universal property, including this `Sigma.desc` map.
- Conclusion: node says that very coproduct morphism is etale; Lean
  `Etale (Sigma.desc ...)`. Dependency `def-weil-etale-morphism` identifies
  `AlgebraicGeometry.Etale` with the source's etale-morphism notion. This is
  one conclusion and has no omitted clause or changed quantifier order.

Edge cases: `I = Empty` is allowed and gives the empty coproduct scheme;
`I = Unit` gives the single finite separable spectrum map. Field hypotheses
exclude zero rings as the node does. There is no numeric `n`, so `n = 0`
adds no case. Positive characteristic and characteristic zero are both
included. The one polymorphic universe is the universe of the schemes and
their indexing type; any particular set and family of fields can be placed
in a sufficiently large such universe. No `Small`, `Finite`, or `Nonempty`
hypothesis is imposed beyond the type's placement in that universe.

Independent searches with different wording from the worker's:

- `msearch.py leanfinder "disjoint union of spectra of separable field
  extensions is an etale scheme"`: found
  `Algebra.Etale.iff_exists_algEquiv_prod`, which describes a *finite*
  product algebra and is not this arbitrary scheme coproduct statement.
- `msearch.py loogle "AlgebraicGeometry.Etale
  (CategoryTheory.Limits.Sigma.desc _)"`: zero hits.
- `msearch.py grep "isEtale.*finite.*separable|finite.*separable.*isEtale|
  etale.*Sigma.desc"`: zero hits.
- `rg` for etale coproducts and separable spectra in Mathlib,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the repository's
  `lean/Sheaf`: `IsZariskiLocalAtSource.sigmaDesc` is the generic coproduct
  step; upstream `Etale.coprodDesc` is binary; upstream
  `etale_SpecMap_algebraMap_tfae` concerns finite product algebras. None
  states this node. An exact declaration-name search found no collision.

The declaration has a `sorry` proof only, and its module and declaration
docstrings give the source and blueprint identifier. The declaration
docstring follows the node's three proof steps: coproduct construction and
open cover (Schemes 01JB), etaleness of each finite separable component
(Morphisms 02GL), then source locality (Morphisms 02GJ). All variables and
the universe are bound; no line exceeds 100 characters. `scompile.py`
compiled the unchanged module with exit code 0 and no warnings.
