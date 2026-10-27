## Worker report

The module `Sheaf.RingTheory.IndEtaleDomainGenericField` states
`Algebra.indEtale_domain_genericField`, with one postponed theorem and no definitions.
The node is unchanged outside its `lean` record; there are no new or dependency nodes.

The statement was compared with the source in `literature/stacks-project/pione.tex`,
section-ramification (Tag 0BSD), including its displayed fraction-field diagram,
and with more-algebra.tex, lemma-absolutely-flat-over-field (092Q), and
algebra.tex, lemma-etale-over-field (00U3). The theorem's docstring includes all six
steps of the node's proof, with the cited DAG lemmas identified explicitly.

Hypothesis and clause correspondence:

- The commutative integral domains are `A : Type u`, `C : Type v`, with
  `[CommRing A] [IsDomain A] [CommRing C] [IsDomain C]`.
- The unital homomorphism `A → C` is `algebraMap A C` for `[Algebra A C]`.
  Every commutative ring homomorphism gives exactly such an algebra structure.
  Its injectivity is the explicit hypothesis `hinj`.
- Its ind-étaleness is exactly the recorded predicate
  `hind : RingHom.IndEtaleAcrossUniverses (algebraMap A C)`.
- `K = Frac(A)` and `L = Frac(C)` are arbitrary field models given by
  `[Field K] [Algebra A K] [IsFractionRing A K]` and
  `[Field L] [Algebra C L] [IsFractionRing C L]`. Their universes `k`, `l`
  are independent of `u`, `v`.
- `[Algebra A L] [IsScalarTower A C L]` specify the composite `A → C → L`.
  `[Algebra K L] [IsScalarTower A K L]` specify its induced fraction-field
  inclusion. These are compatible structure data, not additional mathematical
  restrictions: the injective composite extends uniquely along the fraction field,
  by `IsFractionRing.lift` and its uniqueness. The algebra map from a field is injective.
- The canonical map `K ⊗[A] C → L` is the actual Mathlib tensor-product lift
  of `Algebra.ofId K L` and `IsScalarTower.toAlgHom A C L`.
  It sends `k ⊗ c` to `algebraMap K L k * algebraMap C L c`.
  `Commute.all` only supplies the commutation proof for these specified images.
  `Function.Bijective` says that this particular algebra homomorphism is an isomorphism,
  rather than asserting existence of an unspecified isomorphism.
- The notation `(A \ {0})⁻¹C = K ⊗[A] C` names the standard localization description
  of this same generic fibre. Since `A` is a domain, its nonzerodivisors are precisely
  its nonzero elements. Mathlib's `IsLocalization.tensorRight` in
  `Mathlib.RingTheory.Localization.BaseChange` identifies the tensor product as
  localization at `Algebra.algebraMapSubmonoid C (nonZeroDivisors A)`; its right-algebra
  structure is canonical. No second localization notion or comparison map is needed.
- `Algebra.IsSeparable K L` is the dependency's exact separable-algebraic predicate.
  Its definition requires every minimal polynomial to be separable. The nonalgebraic
  minimal polynomial is zero and is not separable, so algebraicity is included;
  `Algebra.IsSeparable.isAlgebraic` confirms this in the source.
- Every field `F` is quantified as `∀ (F : Type w) [Field F]`; `w` is independent.
  A unital map is `f : C →+* F` and the injective restriction is exactly
  `Function.Injective (f.comp (algebraMap A C))`.
- The final conclusion states `Function.Injective f` and
  `∃! g : L →+* F, g.comp (algebraMap C L) = f`.
  A unital homomorphism between fields is injective, so these are precisely the
  field embeddings extending `f`, with uniqueness including all possible extensions.

Dependency declarations used:

- `Sheaf.RingTheory.IndEtaleUniverseTransport`, `RingHom.IndEtaleAcrossUniverses`:
  read its full definition, which applies the original predicate to the canonical
  `RingHom.ulift` into the common universe; imported publicly.
- `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable`: read its class definition
  and docstring and the algebraicity instance; imported publicly.
- Proof dependency `Sheaf.RingTheory.IndEtaleStability`,
  `RingHom.indEtale_principalZariski_stability`: read its full signature and proof
  docstring; imported without `public`.
- Proof dependency `Sheaf.RingTheory.WeaklyEtaleField`, `Algebra.weaklyEtale_field`:
  read its full signature and proof docstring; imported without `public`.
- Proof dependency `Mathlib.RingTheory.Etale.Field`,
  `Algebra.Etale.iff_exists_algEquiv_prod`: read its signature and docstring;
  imported without `public`, as its node's mathlib_match prescribes.
- Mathlib's `IsFractionRing`, tensor-product lift, `Algebra.ofId`, and
  `IsScalarTower.toAlgHom` supply fraction fields and the canonical map.

Edge cases checked before writing:

- The zero ring is excluded exactly by the two `IsDomain` hypotheses, as in the node.
- Identity maps and the case where `A` is already a field are included: the generic
  fibre is `C`, which must itself be a separable algebraic field in this case.
- No finite type, finite degree, Noetherian, normal, local, or characteristic
  hypothesis is introduced; infinite separable algebraic extensions are included.
- Arbitrary characteristic, nonalgebraic target fields `F`, and distinct universes
  for all rings, fraction fields, and target fields are included.
- A map `C → F` not injective on the base is outside exactly the last implication's
  premise; it is not incorrectly claimed injective.
- The field-product proof includes the empty product and excludes it by nontriviality.

Searches (2026-10-24):

- `msearch.py ... leanfinder`, query: "An injective ind etale homomorphism of integral
  domains has generic fibre equal to its fraction field and separable algebraic fraction
  field extension". Eight hits: finite-type/formally-etale results including
  `RingHom.Etale.ofLocalizationSpan`, `RingHom.Etale.ofLocalizationSpanTarget`,
  `Algebra.FormallyEtale.of_isSeparable_aux`, `Algebra.Etale`,
  `Algebra.Etale.iff_exists_algEquiv_prod`, `RingHom.Etale`,
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, and `RingHom.Etale.toAlgebra`.
  None states the domain generic-fibre result or its extension clause.
- `msearch.py ... loogle`, query `IsFractionRing.lift, Algebra.IsSeparable`:
  zero hits.
- `msearch.py ... leansearch`, query: "The fraction field of an ind etale domain is
  the generic fibre and is separable algebraic over the base fraction field".
  Eight hits: `FractionRing.isSeparable_of_isLocalization`,
  `Algebra.IsSeparable.isAlgebraic`, `Ring.instIsGaloisFractionRingNormalClosure`,
  `Field.isSeparable_algebraMap`, `IsFractionRing.toField`, and the three formally
  etale classification/separability declarations. None states this theorem;
  localization transfer of an already separable extension is a different hypothesis.
- `msearch.py ... grep`, query
  `[Ii]nd.?[Ee]tale.*([Ff]raction|[Ff]ield)|[Ff]raction.*[Ii]nd.?[Ee]tale`
  in `RingTheory`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for ind-etale/fraction and
  generic-field patterns, and the item id in `lean/WeilConjectures`: no full match.
  The Sheaf normalization comparison cites this item in its proof, but does not
  state it. Searching `IndEtaleAcrossUniverses` found the recorded definition and
  other consumers, which are reused rather than duplicated.
- `rg` for `indEtale_domain_genericField` in Mathlib, both project source roots,
  and `dag/lean_names_upstream.json`: no existing declaration with the proposed name.

Validation: `scompile.py Q88 lem-dl-a1-ind-etale-domain-generic-field <module>`
passes sandbox and library compilation, with no errors or non-sorry warnings.
One preliminary elaboration failure concerned commutation of the source elements;
corrected to commutation of their images in `L`, and used the canonical `K`-algebra
map from the left tensor factor. No node faults or statement disputes were found.

## Second reading by Q88

I reread the node and completed module clause by clause after compilation. This is a
worker self-check; the dispatcher brief prohibits starting other agents and assigns
independent review to the maintainer. I checked that both domain assumptions and
injectivity occur, that the universe-transported ind-etale predicate is the recorded
one, that the scalar towers force the canonical field inclusion, and that bijectivity
refers to the canonical tensor map. I checked that separability entails algebraicity
and that the unique extension is quantified over every field map with injective
restriction. In particular uniqueness is not weakened to uniqueness of a chosen lift.
No mathematical mismatch or node correction was needed; only the preliminary tensor
commutation elaboration was repaired as described above.
