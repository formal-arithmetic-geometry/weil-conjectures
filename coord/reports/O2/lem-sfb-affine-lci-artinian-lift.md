## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLciArtinianLift` states
`AlgebraicGeometry.exists_affine_lci_artinian_lift`, with `sorry` as its entire proof.
There are no new definitions, helper theorems, dependency repairs, or statement changes.
The source is Stacks examples-defos.tex, Tag 0DZH (`lemma-lci-unobstructed`), translated
by Tag 0DYX (`lemma-affine`) and `example-schemes`; the coefficient identifications
are those of formal-defos.tex, `definition-CLambda`. I read those source passages.
The node has no released repair note.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`.
- The coefficient ring is `(Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
  [IsLocalRing Λ]`. `[Algebra Λ k]` and
  `eΛ : IsLocalRing.ResidueField Λ ≃ₐ[Λ] k` specify its residue-field identification.
  `IsLocalRing.ResidueField Λ` is exactly the quotient by its maximal ideal.
  The algebra structure on that quotient is the canonical one. There is no
  field embedding into Λ or completeness assumption.
- The Artinian local coefficient algebras are `A' A : Type u` with commutative
  ring, `IsArtinianRing`, `IsLocalRing`, and `Algebra Λ` instances for each.
  Mathlib's Artinian predicate means DCC on submodules of the ring over itself,
  hence on ideals; its local-ring predicate is the nontrivial unique-maximal-ideal
  convention in the node.
- `eA'` and `eA` are the specified Λ-algebra isomorphisms from those residue fields
  to k. The map is `π : A' →ₐ[Λ] A`; `[IsLocalHom π.toRingHom]` and
  `hπ : Function.Surjective π` express locality and surjectivity.
- `hπk` says that the residue map of A composed with π is the specified residue
  map of A'. Since both residue maps identify their quotient fields with k, this
  says exactly that π induces the identity on k. It neither chooses nor requires
  a section of either residue map.
- `V = Spec P` is written directly as `Spec (.of P)`. The ring P has `[CommRing P]`,
  `[Algebra k P]`, `[Algebra.FiniteType k P]`, and
  `hP : Algebra.IsLocalCompleteIntersection k P`. This is the dependency's actual
  lci predicate, which includes the zero algebra and imposes no dimension bound.
- The deformation is `(Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) [Flat f]`.
  Its specified isomorphism is `ι` from the pullback along
  `Spec.map (ofHom (eA.toRingHom.comp (IsLocalRing.residue A)))` to `Spec (.of P)`.
  `hι` says its composite with `Spec (algebraMap k P)` equals the second
  pullback projection, expressing that ι is an isomorphism over k.
- The existential `Y'`, its structure map `f'`, and `Flat f' ∧ IsAffine Y'` give
  the flat affine A'-scheme; no further finiteness or smoothness is demanded.
- `α` is an isomorphism from `pullback f' (Spec.map (ofHom π.toRingHom))` to Y.
  `hα` is its equality over Spec A, so α is precisely an A-isomorphism.
- `ι'` is the specified isomorphism of the special fibre of Y' to `Spec P`.
  Its following projection equality says it is over k. For its source, the residue
  arrow is written as `Spec k → Spec A → Spec A'`. This is the residue arrow
  from eA' because `hπk` and `Spec.map_comp` identify them. Thus this is exactly
  the same special fibre as the node's, with no hypothesis or object changed.
- The last equality is `ι ∘ α_k = ι'` in Lean's forward composition notation:
  the inverse of `pullbackLeftPullbackSndIso` first identifies the direct special
  fibre with the iterated one; `pullback.map` then base-changes α with identity
  on Spec k and Spec A; finally it composes with `ι.hom`. Its two commutativity
  proofs use `hα` and identity laws. All arrows are Mathlib's canonical maps;
  there is no arbitrary comparison or mere isomorphism-class assertion.
- There is no dimension hypothesis, `Smooth` hypothesis, nonempty hypothesis,
  reducedness hypothesis, or characteristic restriction. The only coefficient
  local rings are nonzero; the algebra P and schemes may be zero/empty.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`), inherited through
  the public dependency imports.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`, and
  `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `.Spec.map`, all in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, with its stalkwise equivalence read.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The scheme
  existence instance and `pullbackSpecIso` are in `Mathlib.AlgebraicGeometry.Pullbacks`.
  The canonical pasting iso is in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`.
- `def-weil-pbc-complete-intersection-over-field`:
  `Algebra.IsLocalCompleteIntersection` in
  `WeilConjectures.RingTheory.CompleteIntersectionOverField`; I read its full
  signature and the global complete intersection predicate it uses.

The proof imports follow the accepted six-step plan: `Mathlib.RingTheory.HopkinsLevitzki`
(Artinian Noetherianity and maximal-ideal nilpotence),
`WeilConjectures.AlgebraicGeometry.NilpotentBaseChangeIdempotents`
(`nilpotent_baseChange_idempotents`),
`WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme`
(`isAffine_of_isThickening`), the publicly imported affine flatness and fibre-product
formulas, `WeilConjectures.Algebra.FiniteTypeLiftNilpotent`
(`finiteType_of_quotient_finiteType_nilpotent`),
`Mathlib.RingTheory.FinitePresentation` (`Algebra.FinitePresentation.of_finiteType`), and
`Sheaf.RingTheory.SyntomicAlgebraSurjectionLift`
(`Algebra.exists_syntomic_algebra_lift_of_surjective`). Those proof-only imports
are plain imports. Their declarations and source docstrings were read, including
the syntomic theorem's actual quotient isomorphism and scalar-compatibility equation.
The theorem docstring carries all six proof steps and their DAG references.

Edge cases checked before drafting:

- P = 0: the existing lci predicate allows the empty cover of the empty spectrum;
  a nilpotent thickening forces Y empty, and the empty Y' works. No `Nontrivial P`
  or point of Y is required anywhere in the signature.
- π the identity: the same flat affine deformation is a lift; the canonical
  pullback identifications preserve the chosen marking.
- Singular P = k[x]/(x²): lci does not imply smoothness, and no smoothness binder
  accidentally excludes this case.
- Polynomial algebras of any finite dimension: no degree/dimension restriction.
- Mixed characteristic Λ and A': only Λ-algebra residue identifications occur;
  there is no `[Algebra k A']` or `[Algebra k A]`.
- Arbitrary markings: the last equation uses the supplied ι itself, not a fresh
  existential identification of its isomorphism class.
- Universes: k, A, A', P and Y belong to the ambient scheme universe u; Λ has an
  independent universe v. There is no quantification over tests in a smaller
  independent universe and no extra universe equality on coefficients.

Searches actually run on 2026-10-24 using the prescribed msearch wrapper:

- LeanFinder: "Flat deformations of an affine local complete intersection lift across
  surjective Artinian local coefficient ring maps". Eight results concerned
  formal smoothness, flatness and ordinary smooth schemes; none lifts the marked
  scheme deformation of an arbitrary lci algebra.
- Loogle: `Algebra.FormallySmooth, Function.Surjective`. Twelve results, including
  `Algebra.FormallySmooth.liftOfSurjective`, concerned lifting homomorphisms from a
  fixed formally smooth algebra, not lifting the algebra or scheme deformation.
- Mathlib grep: `Artinian.*lift|lift.*Artinian|[Dd]eformation|[Ss]yntomic`.
  Only an unrelated perfectoid deformation-theory comment was found.
- Direct rg of `lean/Sheaf` and `lean/WeilConjectures` for Artinian/lci lifting
  and deformation/lifting found smoothness criteria, coefficient enlargement,
  and curve formal-lifting material, not this statement. It did find the existing
  syntomic-algebra lifting proof dependency, which is imported, not restated.
- `grep -rn 'lem-sfb-affine-lci-artinian-lift' lean/WeilConjectures` found no match.
  The chosen declaration name was also searched in both project roots and
  `dag/lean_names_upstream.json`, with no existing declaration found.

Validation: the delivered module compiled cleanly via scompile.py, both as its
sandbox module and its actual library module. An initial elaboration error from
anonymous `.ofHom` notation was repaired by opening CommRingCat and using `ofHom`;
no diagnostic commands remain. No statement fault or dispute was found.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
