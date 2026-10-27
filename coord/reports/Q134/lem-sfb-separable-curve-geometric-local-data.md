## Worker report

States `AlgebraicGeometry.separable_curve_geometric_local_data` in
`Sheaf.AlgebraicGeometry.SeparableCurveGeometricLocalData`. Its only theorem proof is
`sorry`. There are no definitions, new nodes, dependency repairs, statement changes,
or changes to the accepted stage-1 split. The node copy changes only `lean`.

The inherited BLOCKED ending concerned stage-1 re-splitting. The live node has a
passing Q154 stage-1 review dated 2026-10-23 and no Lean record. The stage-handoff
paragraph in coord/brief-stage2.md explicitly permits the current stage-2 task;
coord/queue.tsv lists this item at stage 2. No repair note exists for this item.

Source checked: Stacks curves.tex, lemma-nodal (0C4D), especially the arbitrary-field
paragraph and the local flat base-change argument; varieties.tex,
lemma-dimension-locally-algebraic (0A21), clauses (2) and (5). The current latest
blueprint direct-images proof invokes proper base change and compactification;
this node is an inherited auxiliary reduction, as its accepted split_report says.
The accepted six-step affine/local proof is reproduced in the theorem docstring.

Hypotheses and notation, clause by clause:

- A field k: `{k : Type u} [Field k]`.
- A scheme over k locally of finite type: `{C : Scheme.{u}}`,
  `f : C ⟶ Spec (.of k)`, `[LocallyOfFiniteType f]`. No global quasi-compactness,
  separatedness, irreducibility, smoothness or reducedness assumption is added.
- Pure dimension d: `d : ℕ`, `hdim : C.IsPureDimension d`; the landed definition
  quantifies every irreducible component with its subspace topology.
- A closed point: `x : C`, `hx : IsClosed ({x} : Set C)`.
- F is the actual residue field: `C.residueField x`, not an independent field.
  Its k-structure is `f.residueFieldAlgebraMap x`. `hfin` is finiteness of this
  ring map; `hsep` is `Algebra.IsSeparable` for exactly its `toAlgebra` instance.
  Thus finite separable residue extension is assumed without an unrelated action.
- An algebraic closure: `K : Type u`, `[Field K] [Algebra k K] [IsAlgClosure k K]`.
- C_K with both projections: `Y`, `π : Y ⟶ C`, `g : Y ⟶ Spec (.of K)`, and
  `hcart : IsPullback π g f (Spec.map ... (algebraMap k K))` name an arbitrary
  representative of the specified fibre product. This is its universal-property
  encoding, equivalent to the chosen categorical pullback, not an extra geometric
  hypothesis. In particular the standard chosen pullback is a permitted instance.
- The given geometric point: `y : Y`, `hy : π y = x`. The embedding below is
  obtained for this y, rather than selecting an unrelated point of the fibre.
- Every affine open neighbourhood: universally quantified `S : Type u`,
  `[CommRing S] [Algebra k S]`, `i : Spec (.of S) ⟶ C`, `[IsOpenImmersion i]`,
  `hi : i ≫ f = Spec.map ... (algebraMap k S)`, and `p : PrimeSpectrum S`,
  `hp : i p = x`. This is an arbitrary affine presentation of the open and its
  point. `hi` specifies the induced k-algebra structure; it does not restrict the
  affine opens covered. Any affine open of C containing x has such a presentation.
- A and B throughout mean the actual `C.presheaf.stalk x` and
  `Y.presheaf.stalk y`. Their local-ring structures are supplied by Scheme;
  m and n are their `IsLocalRing.maximalIdeal`, with no arbitrary ideal choices.

Conclusions, clause by clause (existential names are those of the Lean theorem):

- S finitely generated: `(algebraMap k S).FiniteType`.
- p maximal: `p.asIdeal.IsMaximal`.
- Noetherian local A and B: the two `IsNoetherianRing` conjuncts together with
  the existing Scheme stalk local-ring instances.
- A essentially finite type over k: `EssFiniteType` of the actual composite
  `ΓSpecIso.inv ≫ f.appTop ≫ C.presheaf.Γgerm x`, after taking its ring hom.
- Dimension: `ringKrullDim (C.presheaf.stalk x) = (d : WithBot ℕ∞)`.
- Germ identification A = S_p: `eA : A ≃+* Localization.AtPrime p.asIdeal` is
  equal to the composite of `stalkCongr hp.symm`, the inverse open-immersion
  stalk isomorphism, and `Spec.stalkIso`. Hence it is the germ identification,
  not merely existence of an uncharacterized abstract isomorphism.
- S/p = F: `eF : (S ⧸ p.asIdeal) ≃+* C.residueField x`, with its value on each
  quotient generator equal to the residue of the corresponding germ via `eA`.
  The next equality of ring homomorphisms says this identification respects k.
- U_K is the inverse image of U: an open immersion
  `j : Spec (.of (S ⊗[k] K)) ⟶ Y` with
  `Set.range j = π ⁻¹' Set.range i`.
- U_K = Spec(S tensor_k K), compatibly with projections: this is the source of
  j, and the following two morphism equalities identify `j ≫ π` and `j ≫ g`
  with Spec of `Algebra.TensorProduct.includeLeft` and `includeRight`.
- y corresponds to q: `q : PrimeSpectrum (S ⊗[k] K)` and `hq : j q = y`.
  `q.asIdeal.IsMaximal` is explicit.
- The k-embedding F into K is `ι : C.residueField x →+* K` with
  `ι.comp (f.residueFieldAlgebraMap x) = algebraMap k K`. A unital homomorphism
  between fields is injective, so this is an embedding, without a weaker map.
- The displayed evaluation map is `ε : S ⊗[k] K →+* K` with the equation
  `ε (s ⊗ₜ[k] l) = ι (eF (Ideal.Quotient.mk p.asIdeal s)) * l` for all s,l.
  `q.asIdeal = RingHom.ker ε` is exactly the stated kernel formula.
- Structural residue field K: `eK : Y.residueField y ≃+* K`, with
  `eK.toRingHom.comp (g.residueFieldAlgebraMap y) = RingHom.id K`.
  Its value on the residue of each tensor generator through eB is ε.
- Germ identification B = (S tensor_k K)_q: `eB` is required to equal the
  analogous canonical stalk composite for j and hq.
- Compatibility with A → B: the local map is the actual scheme stalk map
  `(stalkCongr hy.symm).hom ≫ π.stalkMap y`; its effect on every s in S after
  eA and eB is localization of `s ⊗ₜ[k] 1`. Localization uniqueness determines
  the entire local-ring map from this equality.
- Compatibility of residue maps: the subsequent universally quantified equation
  says `eK(residue_B(localMap a)) = ι(residue_A a)` for every a in A.
- Faithfully flat: `Module.FaithfullyFlat A B` explicitly uses the module
  structure induced by this same actual local-ring map, via `toAlgebra.toModule`.
- mB = n: `Ideal.map localMap (IsLocalRing.maximalIdeal A) =
  IsLocalRing.maximalIdeal B`.
- B/mB = K: mB = n identifies this quotient with the actual residue field of B;
  eK supplies its isomorphism with K and the displayed structural compatibility.
  Thus this clause is encoded by the preceding ideal equality and eK, not omitted.
- The two completion isomorphisms: `EA`, `EB` are ring equivalences between
  `AdicCompletion` of the respective maximal ideals, in the node's directions.
  Each final universally quantified implication identifies its n-th quotient
  coordinate with the quotient of `eA a` or `eB b`, for every representative a,b.
  Every quotient class has a representative. Consequently these formulas say
  precisely that the completion maps are induced by the germ isomorphisms;
  they do not allow arbitrary ring isomorphisms of the completions.
- Quotient rings, algebra maps, tensor products, ideal extension, and powers
  are the existing Mathlib constructions throughout, with no copied definitions.

Dependency declarations read and used (all source signatures and docstrings checked):

| Dependency | Module and declarations used |
| --- | --- |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `AlgebraicGeometry.LocallyOfFiniteType` |
| def-weil-pure-dimension | Sheaf.AlgebraicGeometry.PureDimension: `AlgebraicGeometry.Scheme.IsPureDimension` |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`; WeilConjectures.ZetaSeries: `Scheme.Hom.residueFieldAlgebraMap` |
| def-weil-pbc-separable-algebraic-extension | Mathlib.FieldTheory.Separable: `Algebra.IsSeparable` |
| def-weil-algebraic-closure | Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosure` for an arbitrary supplied algebraic closure |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`, `pullback.snd`; Mathlib.AlgebraicGeometry.Pullbacks supplies scheme pullbacks; `IsPullback` is the equivalent universal-property interface |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map` |
| def-weil-pbc-finite-type-algebra | Mathlib.RingTheory.FiniteType: `RingHom.FiniteType` |
| def-weil-pbc-localization-at-prime | Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime` |
| def-weil-pbc-module-tensor-product | Mathlib.LinearAlgebra.TensorProduct.Defs: `TensorProduct`, supplied with its algebra ring structure and inclusions by Mathlib.RingTheory.TensorProduct.Basic/Maps |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` |
| def-weil-pbc-essentially-finite-type-algebra | Mathlib.RingTheory.EssentialFiniteness: `RingHom.EssFiniteType`, the bare-map wrapper of the recorded `Algebra.EssFiniteType` |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim` |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic/Algebra: `AdicCompletion`, `AdicCompletion.evalₐ` |
| def-weil-pbc-faithfully-flat-ring-map | Mathlib.RingTheory.Flat.FaithfullyFlat.Basic: `Module.FaithfullyFlat` |
| def-weil-pbc-algebra-hom-quotient | Mathlib.Algebra.Algebra.Hom: `AlgHom`; Mathlib.RingTheory.Ideal.Quotient.Operations: `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`; their underlying quotient and ring-map forms |

Proof-only imports retain the already stated proof dependencies:
Mathlib.RingTheory.LocalRing.ResidueField.Ideal,
Mathlib.RingTheory.TensorProduct.Quotient,
Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
(`Algebra.separable_tensor_algebraicallyClosed_equiv_pi`),
WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
(`AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`),
WeilConjectures.Mathlib.Topology.KrullDimension (`IsOpen.topologicalKrullDimAt_eq`),
and WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
(`AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal`).
The other Mathlib proof dependencies are exposed by the public imports already
needed for the statement. `lem-trf-separable-evaluation-local-base-change` has no
recorded declaration yet, so no module can currently be imported for it; its use
is preserved in the proof docstring and unchanged DAG proof_deps. It is not needed
to type this statement and is not duplicated here.

Searches for the complete statement (logs in searches.jsonl):

- LeanFinder: affine geometric stalks at a finite separable closed point on an
  equidimensional scheme; eight hits on stalk maps, closed-point stalks and
  SpecToEquivOfField, none stating this simultaneous geometric-local result.
- LeanSearch: separable closed-point algebraic-closure base change, faithful
  flatness, maximal-ideal extension and residue field; eight hits on individual
  residue-field, flatness and unramifiedness facts, none on this full statement.
- Loogle: `"AdicCompletion", "IsSeparable"` returned zero hits. An earlier
  query `AlgebraicGeometry.Scheme.stalk, AdicCompletion` reports the unknown
  identifier Scheme.stalk and therefore was not treated as positive search evidence.
- Mathlib grep: `separable.*stalk|stalk.*separable|geometric_local_data` in
  AlgebraicGeometry returned eight unrelated uses of `Inseparable.of_eq`.
- rg of lean/WeilConjectures and lean/Sheaf for the proposed declaration name,
  node id, and `separable.*stalk|stalk.*separable`: no matching theorem; nearby
  geometric field descent and normalization results concern different objects.
  The existing separable tensor and evaluation localization results supply pieces,
  not the arbitrary geometric-point and affine-neighbourhood statement here.

Edge cases checked before retaining the statement:

- C empty: there is no x, so the statement makes no assertion; the pure-dimension
  definition correctly accepts the empty scheme in every d.
- d = 0, C = Spec F with F/k finite separable: A = F, B = K, the maximal ideals
  vanish, both completions are the fields, and the dimension equality is 0.
- F = k: the embedding is the structural k-map, and the evaluation formula
  specializes to the rational-point case.
- Nonreduced zero-dimensional example k[t]/(t^2): local rings and the ideal
  equality remain correct; no reducedness was silently imposed.
- Reducible pure-dimensional schemes and arbitrary characteristic, including 2,
  are permitted. No curve-specific d = 1 or characteristic restriction appears.
- Purely inseparable residue extensions are deliberately excluded by hsep;
  for those the closed fibre may be nonreduced and mB = n can fail.
- An affine neighbourhood S cannot be the zero ring because it contains p;
  similarly no field, stalk or localization is silently allowed to be trivial.
- All schemes and affine presentations are in the same ambient scheme universe u;
  no independent smaller test-object universe creates a vacuous hypothesis.

Validation: the retained module passed the prescribed server scompile.py in both
sandbox and library module contexts (2.6 and 2.5 seconds), with no warnings/errors.
`set_option autoImplicit false` makes all variable/universe bindings explicit.
All Lean lines satisfy the 100-character limit. No STATEMENT-DISPUTED issue found.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
