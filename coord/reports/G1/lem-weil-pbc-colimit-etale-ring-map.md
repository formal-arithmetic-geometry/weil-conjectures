## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent` states
`AlgebraicGeometry.Etale.exists_stage_of_directedColimit`, with only `sorry` as its proof.
No definitions, auxiliary nodes, or dependency modules were needed. The node is unchanged
except for its `lean` record.

The source is Stacks Algebra Lemma 10.168.7, Tag 07RI,
https://stacks.math.columbia.edu/tag/07RI, opened and read together with its proof.
The local Stacks TeX is absent on this machine. The source agrees with the node.

Correspondence for every hypothesis and clause:

- The directed set is `{I : Type v} [PartialOrder I] [IsDirected I (· ≤ ·)]`.
  The distinguished element called `0` in the node is `(i₀ : I)`; this is an arbitrary
  index, not a bottom element or an additive zero. Its existence supplies nonemptiness.
- The compatible directed ring system is `(F : I ⥤ CommRingCat.{u})`. The category
  structure on the partial order has a unique arrow for each inequality, and the functor
  identity and composition laws supply the transition-map compatibility.
- `[HasColimit F]` expresses existence of the specified colimit. The ring `A` is
  `(colimit F : CommRingCat.{u})`; `colimit.ι F i₀` is its canonical coprojection.
  Choosing this canonical colimit loses no generality: any other colimit is uniquely
  isomorphic with the coprojections preserved.
- `B₀ C₀ : Type u` with `[CommRing B₀] [CommRing C₀]` are the two commutative rings.
  `[Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]` are precisely their `A₀`-algebras.
- `(φ₀ : B₀ →ₐ[F.obj i₀] C₀)` is the homomorphism of `A₀`-algebras. The hypothesis
  `(hfp : φ₀.FinitePresentation)` means finite presentation of the underlying ring
  homomorphism, i.e. of `C₀` as a `B₀`-algebra using `φ₀`, exactly the node's finite
  generators and finite relations. It does not assume `B₀` or `C₀` is finitely presented
  over `A₀`.
- The first `letI` equips `A` with the `A₀`-algebra induced by the coprojection.
  `Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (colimit F)) φ₀` has domain
  `A ⊗[A₀] B₀` and codomain `A ⊗[A₀] C₀`, sending `a ⊗ b` to `a ⊗ φ₀ b`.
- The antecedent is `Etale (Spec.map (CommRingCat.ofHom ...toRingHom))` for that map.
  Since `Spec.map` is contravariant, this is exactly `Spec C → Spec B` induced by `φ`.
- The conclusion `∃ (i : I) (hi : i₀ ≤ i)` is the required later index `i ≥ 0`.
  Its `letI` equips `F.obj i` with the `A₀`-algebra from `F.map (homOfLE hi)`.
  The tensor-product map is again identity on the left and `φ₀` on the right, now on
  `Aᵢ ⊗[A₀] B₀ → Aᵢ ⊗[A₀] C₀`. Its spectrum is asserted to be `Etale`, exactly the
  final clause of the node.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `colimit.ι` and
  `HasColimit`, from `Mathlib.CategoryTheory.Limits.HasLimits`, available through
  `Mathlib.Algebra.Category.Ring.Colimits`. The arbitrary-choice colimit docstring
  and the coprojection signature were read; the source uses generated `to_dual` names.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; read its full class signature and
  docstring. It is the node's affine-local etale condition on scheme morphisms.
- Standard existing notions used directly: `AlgHom.FinitePresentation`
  (`Mathlib.RingTheory.FinitePresentation`), `Algebra.TensorProduct.map`
  (`Mathlib.RingTheory.TensorProduct.Maps`), and `AlgebraicGeometry.Spec.map`
  (`Mathlib.AlgebraicGeometry.Scheme`). Their signatures and docstrings were read.

Edge cases checked: an empty directed set is impossible because of `i₀`; no least index
is imposed. A singleton system is allowed, as are directed sets without a least element.
The zero ring is allowed for every ring, and consequently empty spectra are allowed.
No field, characteristic, Noetherianity, or nonzero hypothesis is introduced.
Presentations with zero variables or zero relations are included in finite presentation.
The index universe `v` is independent of the common ring universe `u`; arbitrary ring
sizes can be put in a common universe. `[HasColimit F]` imposes only the colimit's existence
already stipulated in the node, including for a larger indexing universe.

Searches made:

- `msearch.py ... leanfinder "Etaleness of a finitely presented algebra map descends
  along a directed colimit of base rings"`: eight hits, including
  `Algebra.Etale.exists_subalgebra_fg` (a different model-existence statement), etale
  composition and ring-map conversion. No match for descent of this fixed map.
- `msearch.py ... loogle "Algebra.Etale, CategoryTheory.Limits.IsColimit"`: zero hits.
- `msearch.py ... leansearch "finitely presented algebra map etale after base change
  to directed colimit descends to a stage"`: service unavailable (HTTP internal server
  error), recorded as unavailable; no verdict is inferred from it.
- `msearch.py ... grep "07RI|[Ee]tale.*[Cc]olimit|[Cc]olimit.*[Ee]tale"`: zero hits.
- `rg` over upstream `WeilConjectures` and the project's `lean/Sheaf` for colimit-etale,
  etale-descent and related patterns found only other colimit statements or etale model
  and local-lift results. The upstream finite-presentation-colimit file handles existence
  of finitely presented models, not descent of etaleness for a fixed map.
- `rg` for this exact node id in upstream `WeilConjectures` found no result.
  The proposed declaration name was checked against Mathlib, upstream, project Lean
  and `dag/lean_names_upstream.json`; no name clash was found.

Server compile: `scompile.py G1 lem-weil-pbc-colimit-etale-ring-map` on the module
completed with exit code 0 in 1.9 seconds and no warnings. The declaration docstring
records all five proof steps and their DAG dependencies for stage 3.
No statement dispute or node fault was found.


## Second reading by G1

I independently read the node, its five proof steps, both statement-dependency nodes,
and the delivered Lean module. I also fetched the Stacks `algebra.tex` into the item's
scratchpad: `lemma-colimit-etale`, lines 47626–47663, is exactly Tag 07RI. The section
opening at line 47319 adds no standing hypotheses; the lemma itself assumes only the
directed ring colimit, the algebra map, finite presentation, and etaleness after base
change. The public source is https://stacks.math.columbia.edu/tag/07RI.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. Directed set I: `{I : Type v} [PartialOrder I] [IsDirected I (· ≤ ·)]`.
   The node's chosen `0 ∈ I` is `(i₀ : I)`, supplying nonemptiness without a least
   element. This is the usual directed-poset indexing category.
2. Compatible commutative ring system: `(F : I ⥤ CommRingCat.{u})`; objects are
   `F.obj i`, transition maps are `(F.map (homOfLE hi)).hom`, and functor laws give
   the required compatibility.
3. Colimit A with coprojections: `[HasColimit F]`, `colimit F`, and `colimit.ι F i₀`.
   These use the recorded `CategoryTheory.Limits.colimit` dependency. I opened its
   generated-definition source in `Limits.HasLimits`: the dual of `limit` chooses
   the colimit cocone and the dual of `limit.π` supplies its coprojections. Specifying
   the chosen colimit represents an arbitrary colimit up to its unique compatible
   isomorphism; the node already stipulates that a colimit exists.
4. Commutative A₀-algebras B₀ and C₀: `(B₀ C₀ : Type u)`, their `[CommRing]`
   instances, and `[Algebra (F.obj i₀) B₀]`, `[Algebra (F.obj i₀) C₀]`.
5. A₀-algebra homomorphism φ₀: `(φ₀ : B₀ →ₐ[F.obj i₀] C₀)`.
6. Finite presentation of φ₀: `(hfp : φ₀.FinitePresentation)`. I read
   `AlgHom.FinitePresentation`, `RingHom.FinitePresentation`, and
   `Algebra.FinitePresentation.out`. Together these mean a surjective map from
   `MvPolynomial (Fin n) B₀` to C₀ with finitely generated kernel, using the
   B₀-algebra structure induced by φ₀. This is exactly the finite generators and
   relations in the node; neither algebra is required finitely presented over A₀.
7. Scalar extension to A: the first `letI` uses the coprojection's `toAlgebra`.
   `Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (colimit F)) φ₀` gives
   `A ⊗[A₀] B₀ → A ⊗[A₀] C₀`. I read `map` and `map_tmul`: it sends
   `a ⊗ b` to `a ⊗ φ₀ b`, exactly id ⊗ φ₀.
8. Etaleness hypothesis: `Etale (Spec.map (CommRingCat.ofHom ...toRingHom)) →`.
   I read `Spec.map`, whose signature reverses the ring arrow, and the recorded
   `AlgebraicGeometry.Etale` class plus `Etale.iff_flat_and_formallyUnramified`.
   These are precisely the induced `Spec C → Spec B` and the dependency node's
   etale morphism notion, not a different algebra or scheme condition.
9. Later index: `∃ (i : I) (hi : i₀ ≤ i)`. No universal stage or bottom index is
   imposed; the existential follows the etaleness hypothesis as in the node.
10. Scalar extension at that index and conclusion: the second `letI` is induced
    by `F.map (homOfLE hi)`; the final tensor map is id ⊗ φ₀ on
    `Aᵢ ⊗[A₀] B₀ → Aᵢ ⊗[A₀] C₀`, and its reversed spectrum map is `Etale`.

Edge cases: empty I is already excluded by the source's chosen index; singleton
systems and directed sets without a least element are allowed. Zero rings and their
empty spectra are allowed everywhere. `n = 0` and zero relations are included by the
finite-presentation definition. There are no field, nonzero, characteristic, finite,
or Noetherian assumptions. `u` is arbitrary and `v` independent; rings of different
sizes may all be placed in a common universe, and the existence of that colimit is
explicitly assumed. All variables and universes are bound.

Independent searches used different wording from the first reader:

- LeanFinder: "A fixed finitely presented ring homomorphism becomes etale after
  extension to a filtered direct limit; it is etale over a later base ring" returned
  eight related declarations. I opened `Algebra.Etale.exists_subalgebra_fg` in
  `Smooth.NoetherianDescent`: it chooses a new model over a finite type subalgebra,
  not a stage of a given system for a fixed map. It is not this statement.
- Loogle: `RingHom.Etale, RingHom.FinitePresentation` returned only
  `RingHom.Etale.iff_flat_and_formallyUnramified`, not descent to an index.
- LeanSearch: "etale property of a fixed finitely presented morphism descends from
  a filtered colimit of base rings to one index" was unavailable (Internal Server
  Error); no absence verdict is inferred from that service failure.
- `msearch.py grep` for `formallyEtale.*(limit|Limit)|[Ee]tale.*(stage|filtered|Filtered)|07RI`
  found no match. Independent `rg` on upstream `WeilConjectures`, project
  `lean/Sheaf`, and the name index found related sheaf-colimit and gluing results,
  but no matching theorem or name collision. I opened upstream
  `exists_isPushout_of_finitePresentation`: it descends a newly chosen finitely
  presented algebra model, not etaleness of this fixed map. Mathlib's
  `Etale.Descent` instead assumes faithfully flat scalar extension.

No new definition nodes, dependency modules, or statement correction are present or
needed. There are no private definitions or hollow data. The sole theorem has only
`sorry`; its docstring follows all five node proof steps and cites each dependency.
The imports serve the ring colimit, etale scheme morphism, and tensor map. Header,
namespace, source markers and line widths meet the conventions. The node's
`lean.statement` is verbatim equal to the declaration signature (checked directly).

Mismatches found: none. Changes: appended this independent reading only; the correct
Lean and node record were retained. The server single-file compile completed in
1.9 seconds with exit code 0 and no warnings.
