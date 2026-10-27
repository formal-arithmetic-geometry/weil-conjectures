## Worker report

The module `Sheaf.RingTheory.FormallySmoothCompletedLocalTensorSquare` states
`RingTheory.formallySmoothAdic_completedLocalTensorSquare`, with its proof `sorry`.
The theorem docstring contains all eleven accepted proof steps and their dependency ids.
No statement, statement dependency, proof, or proof dependency was changed.

The helper declarations abbreviate the exact standard constructions and define their
canonical maps. `LocalCompletionAtResidue ε` is the maximal-ideal-adic completion of
`Localization.AtPrime (Ideal.comap ε ⊥)`; `Ideal.comap ε ⊥` is the kernel of ε, written
this way so Mathlib infers primality from the field target without a new proof lemma.
The localization's maximal ideal is precisely the extension of this prime by
`Localization.AtPrime.map_eq_maximalIdeal`, so this is the node's inverse limit.
Mathlib indexes completion by all natural numbers; the zero coordinate is the zero
quotient, so this is exactly the positive-index inverse limit in the statement.
`toLocalCompletionAtResidue` is the composite of the localization algebra map and
completion algebra map, with no choice of data from an unproved theorem.
`tensorSquareResidue` is residue composed with Mathlib's multiplication map.
`CompletedLocalTensorSquare`, `completedTensorLeft`, and `completedTensorRight`
therefore use the specified diagonal point and canonical inclusions.
`LocalClosedFiber` is the ordinary quotient by the extended maximal ideal of A;
`localClosedFiberResidueAlgebra` applies Mathlib's canonical quotient algebra
constructor `Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map`.
`LocalClosedFiberTensor` is the node's F. `completedTensorSecondIdeal` is J, defined
using `Ideal.map`, which is the generated ideal, rather than the set-theoretic image.
These are helpers for this node's constructions, not new independent notions.
No new nodes or dependency modules are needed.

Hypothesis and clause correspondence:

- The local homomorphism A → R is `[Algebra A R]` and
  `[IsLocalHom (algebraMap A R)]`; an algebra structure on commutative rings is
  precisely a ring homomorphism, so this adds no hypothesis or choice of map.
  A and R have independent universes u and v.
- Commutativity is `[CommRing A] [CommRing R]`. Noetherianity is
  `[IsNoetherianRing A] [IsNoetherianRing R]`. Locality is `[IsLocalRing A]`
  and `[IsLocalRing R]`. Completeness is the two displayed `IsAdicComplete`
  instances for their respective maximal ideals, including separation.
- k and l are `IsLocalRing.ResidueField A` and `IsLocalRing.ResidueField R`.
  The residue extension is the canonical instance induced by the local algebra
  map, read in `Mathlib.RingTheory.LocalRing.ResidueField.Basic`.
  `[Module.Finite k l]` states exactly that the residue extension is finite.
- The formal smoothness hypothesis is `hfs : Algebra.FormallySmoothAdic A R
  (IsLocalRing.maximalIdeal R)`, using the recorded upstream definition.
- P is `TensorProduct A R R`. Its residue map is `tensorSquareResidue A R`,
  and sends r ⊗ s to residue(r) residue(s). The ideal q is its kernel, used
  directly by `LocalCompletionAtResidue`; E is the actual completion of P_q.
- The first conjunct is `IsNoetherianRing E`. The existential local-ring
  instance and `IsAdicComplete (IsLocalRing.maximalIdeal E) E` give the other
  asserted ring properties. Locality of the uncompleted P_q is supplied by
  Mathlib, without assuming P_q is Noetherian.
- The map `ρ : E →+* l`, its surjectivity, and `RingHom.ker ρ = maximalIdeal E`
  give exactly the residue-field identification E/m_E ≅ l. The equations
  `ρ.comp j = IsLocalRing.residue R` for both canonical j identify their
  induced residue maps with the identity on l, not an unspecified automorphism.
- Both inclusions are covered by `∀ j, (j = completedTensorLeft A R ∨
  j = completedTensorRight A R) → ...`. This finite enumeration adds no
  quantification over unrelated maps. For each, `IsLocalHom j` is locality,
  equivalently the inverse-image maximal-ideal equality by
  `IsLocalRing.maximalIdeal_comap`; `j.FaithfullyFlat` is faithful flatness;
  and `@Algebra.FormallySmoothAdic ... j.toAlgebra (maximalIdeal E)` is
  formal smoothness for precisely that inclusion's algebra structure.
- The existential ring homomorphism μ is continuous for the explicitly supplied
  `Ideal.adicTopology` on the two maximal ideals and satisfies `IsLocalHom μ`.
  Its composite with the canonical P → E map is Mathlib's tensor multiplication,
  so it extends the specified multiplication. Both `μ.comp j_i = RingHom.id R`
  equations give the asserted retraction identities.
- J is `(maximalIdeal R).map (completedTensorRight A R)`. The map β has domain
  `LocalClosedFiber A R` and codomain E/J. Its value on every quotient class
  is specified as the class of j₁(r), making it precisely the induced map.
  `β.FaithfullyFlat` states the final faithful flatness claim.
- F is `LocalClosedFiberTensor A R`. The map ε : F → l is characterized on all
  pure tensors: ε([r] ⊗ a) = residue(r) a. Every element of B is represented
  by an r, so this determines ε uniquely on every pure tensor and hence on F.
  `LocalCompletionAtResidue ε` is the completion of F at r = ker ε.
- The ring equivalence e : E/J ≃+* LocalCompletionAtResidue ε is characterized
  by e([j₁(r)j₂(s)]) = image([r] ⊗ residue(s)). Setting s = 1 is the exact
  compatibility with β and the canonical B → completed F_r map. This also
  specifies the original tensor map into the comparison completion. The
  residue map R → l is surjective, so these formulas cover all pure tensors;
  complete Noetherian local rings and their local isomorphisms have the adic
  continuity needed for the canonical completed comparison.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (196),
  `isNoetherianRing_iff`; every ideal finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (56),
  `AdicCompletion` (171), `AdicCompletion.of` (364). The algebra structure
  and canonical algebra map are from `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `WeilConjectures.RingTheory.FormallySmoothAdic`: `Algebra.FormallySmoothAdic`:
  the square-zero lifting definition, with test algebras in max u v and a
  positive power killed. This is the dependency's recorded declaration.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`,
  `LinearMap.baseChange` (661), `TensorProduct.AlgebraTensorModule.distribBaseChange`
  (441), and `TensorProduct.mk`; the tensor construction is reused, with its
  algebra structure from Mathlib's tensor modules, not copied.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` (57),
  its local-ring instance and maximal-ideal identification. The dependency's
  companion `Ideal.ResidueField` and `Ideal.Fiber` were read in their recorded
  Mathlib files; this node uses the local ring's ordinary residue field.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat` (63),
  and `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat` (25),
  the latter using the module structure induced by the specified ring map.

All stated proof-dependency modules are imported without `public`, including the
recorded upstream adic base-change, completion and flatness interfaces, the completion
Noetherian criterion, tower exactness, and the Mathlib modules of the remaining leaves.
The public imports supply the statement's constructions. No theorem other than the
item is postponed; no definition contains `sorry` or uses a choice from a sorried
existence theorem. The single item theorem is the only `sorry`.

Edge cases checked before writing:

- A = R: E = R canonically and J = m_R; the final B = l → E/J = l map is the
  identity. Both canonical maps and the retraction have the expected meaning.
- A = k a field and R = k[[x]]: E is k[[x,y]], J = (y), and the last comparison
  is k[[x]] → k[[x]]; the retraction sends both x and y to x.
- A = k and R = l a finite separable field extension: localization of l ⊗_k l
  at the multiplication point is the diagonal field factor. The definition
  selects that point; it does not complete the whole tensor product instead.
- No separability or characteristic assumption is inserted. The finite residue
  degree is retained, including degree one and mixed characteristic.
- The zero ring is excluded by the given local-ring assumption itself:
  Mathlib `IsLocalRing` extends `Nontrivial`, agreeing with a local ring having
  a maximal ideal and residue field. No extra nonzero hypothesis is imposed.
- The original tensor square and its localization are not assumed Noetherian;
  only the conclusion for E asserts this. This is essential for power-series inputs.
- Ideal powers at zero occur only in Mathlib's harmless zero quotient coordinate;
  there is no extra positivity hypothesis or dropped positive coordinate.
- Explicit `autoImplicit false` and `relaxedAutoImplicit false` check that every
  type, universe and variable is bound. No universe equality is imposed.

Searches actually run (2026-10-24):

- msearch LeanFinder: "Completed local tensor square of an adically formally smooth
  complete Noetherian local algebra". Eight hits, headed by
  `Algebra.FormallySmooth.instTensorProduct` and ordinary formally smooth lifting
  into completions; none supplies the local completed tensor square or its
  closed-fibre comparison.
- msearch LeanSearch: "completion of localized tensor square formally smooth complete
  local rings finite residue extension". Eight hits on ordinary formal smoothness,
  localization and completion lifting; no exact combined statement.
- msearch Loogle: "Algebra.TensorProduct, AdicCompletion, FormallySmoothAdic".
  The service reported unknown identifier Algebra.TensorProduct; this query was
  unusable, not evidence of absence.
- msearch Loogle: "AdicCompletion, IsLocalRing". Twelve hits in Mathlib's
  AdicCompletion.LocalRing: localness, maximal ideal, completeness and residue
  bijectivity for a local completion. These do not give the tensor square or
  faithful flatness of the completed closed-fibre comparison. Their signatures
  and the relevant source were read.
- msearch grep: "completedTensor|completed_tensor|formallySmooth.*tensor" in
  RingTheory. Hits concern ordinary algebraic formally smooth tensor products;
  there is no exact lemma.
- Direct rg in the project's `lean/WeilConjectures/RingTheory` and
  `lean/Sheaf/RingTheory`: "completedLocalTensor|CompletedLocalTensor|tensor.square|
  tensorSquare|completed.*tensor". Hits include finite-extension completion
  comparisons, cotangent tensor squares and Hopf constructions, with different
  hypotheses and conclusions; no match for this statement.
- Direct search for the exact node id in `lean/WeilConjectures`: no occurrence.
  Direct search for the newly used helper and theorem names in Mathlib,
  WeilConjectures and Sheaf found no pre-existing declaration with those names.

Source read: the node's EGA references and eleven-step accepted argument, Mathlib
completion and localization interfaces, and the online English EGA 0_I §7
(https://jcreinhold.github.io/ega/i/00-07-adic-rings.html), particularly 7.7 on
completed tensor products. The attempted guessed English EGA IV chapter URL was
unavailable; no mathematical claim was inferred from that failed request.
No statement fault or statement dispute was found. The inherited blueprint ancestor
is null; its existing precise from.place and via chain were left unchanged.

Validation: `scompile.py Q144 lem-sfb-formally-smooth-completed-local-tensor-square`
compiled this module as both sandbox and its intended library module, cleanly.
The initial compile exposed missing automatic primality for the opaque `RingHom.ker`
expression; changing its definitional presentation to `Ideal.comap ε ⊥` fixed that
without adding a hypothesis, lemma, or axiom. All lines have at most 100 characters.
The required deliver2 dry-run and push follow.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
