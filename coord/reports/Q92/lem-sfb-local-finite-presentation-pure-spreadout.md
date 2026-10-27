## Worker report

The module `Sheaf.RingTheory.LocalFinitePresentationPureSpreadout` states
`Module.exists_projective_pureSpreadout_of_finitePresentation`, with a single `sorry`
and no new definitions. The natural-language node and its dependency lists are unchanged.
The source was read in `literature/stacks-project/flat.tex`, equation-star and
lemma-find-pure-spreadout (Tag 0AT8, including the principal localization in its proof).

Hypotheses and clauses, matched individually:

- The commutative local base is `{R : Type u} [CommRing R] [IsLocalRing R]`.
  Its unique maximal ideal is `IsLocalRing.maximalIdeal R`; no separately named
  ideal or additional hypothesis is needed.
- The finitely presented ring map is `[CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]`.
- `S : Submonoid B` includes precisely the multiplication and unit conditions on Sigma;
  it is not assumed to avoid zero.
- `N : Type w` has `[AddCommGroup N]`, `[Module (Localization S) N]`, and
  `[Module.FinitePresentation (Localization S) N]`. The explicit `Module B N`,
  `Module R N` and the two scalar towers are the restrictions of that action,
  not additional mathematical conditions. They allow the literal quotient by `IN`.
  No flatness hypothesis on N appears.
- `∃ I : Ideal R, I.FG ∧ I ≤ IsLocalRing.maximalIdeal R` is exactly the finitely
  generated ideal contained in the maximal ideal.
- `∃ s : S` supplies an element of the original multiplicative subset.
- The concrete coefficient ring of P is
  `Localization.Away (Ideal.Quotient.mk (I.map (algebraMap R B)) s)`.
  Thus `I.map (algebraMap R B)` is IB and this ring is exactly `(B/IB)[1/sbar]`.
  `Module.FinitePresentation` over that ring is the node's finite presentation of P.
- The existential B-module structure on P and `IsScalarTower B D P` specify
  restriction of its D-action. The existential R/I-module structure on P is fixed
  by the equation `Ideal.Quotient.mk I r • p = algebraMap R D r • p`.
  Surjectivity of `R → R/I` makes this structure unique; no unrelated action is allowed.
- `Module.Projective (R ⧸ I) P` is projectivity over the requested base quotient,
  without imposing finite generation or finite rank over that quotient.
- The target is the actual quotient `N ⧸ (I • ⊤ : Submodule R N)`.
  Mathlib supplies its canonical R/I-action. The B-action is existentially supplied
  with the equation `b • [n] = [b • n]`, fixing it uniquely on every quotient class.
  These two equations specify scalar structures, rather than adding conditions
  to the mathematical conclusion.
- `j : P →ₗ[B] N/IN` and `IsLocalizedModule S j` give the isomorphism theta and
  its composite with localization at once. By Mathlib's characteristic predicate
  and `IsLocalizedModule.iso`, the induced B-linear equivalence sends `p/1` to
  `j p`. It is automatically linear over the localized D: B-linearity extends
  across B/IB because I acts by zero, across s because it is inverted, and across
  the image of S because every member acts invertibly on both localized modules.
  Localizing at S on B-modules is the same as localizing at its image in D.
  Conversely the node's theta composed with `p ↦ p/1` satisfies this characteristic
  predicate. Thus this renders exactly the existence of the specified theta,
  without replacing it by an unconstrained map or a mere abstract isomorphism.
- `jA : P →ₗ[R ⧸ I] N/IN` with `∀ p, jA p = j p` is the very same map with base
  scalars. Finally `∀ T ... Function.Injective (jA.rTensor T)` is precisely the
  injectivity of `j ⊗ 1_T : P ⊗_(R/I) T → (N/IN) ⊗_(R/I) T`.
  T lives in `Type (max u v w z)`, with arbitrary explicit z, so test modules
  are never forced into a smaller universe. P can be chosen in `Type (max u v w)`:
  finite presentation over D gives a quotient of a finite free D-module there.

Dependency declarations used:

- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, recorded
  by def-weil-pbc-finitely-presented-algebra; its class signature and docstring
  were read and it is imported publicly.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, recorded by
  def-weil-pbc-projective-module; its direct-summand implementation and docstring
  were read and it is imported publicly.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Map`: `TensorProduct` and
  `LinearMap.rTensor`, the Mathlib match of def-weil-pbc-module-tensor-product.
  Their full definitions/docstrings were read; `.Map` is imported publicly.
- Other standard interfaces are `Module.FinitePresentation`, `Localization.Away`,
  `Ideal.map`, `Submodule.Quotient`, the canonical quotient action in
  `Mathlib.Algebra.Module.Torsion.Basic`, and `IsLocalizedModule` from
  `Mathlib.Algebra.Module.LocalizedModule.Basic` (its three characterization
  fields and its induced equivalences were read).
- Stated proof dependencies are imported: right exactness, localization/tensor
  base change, finite-type Noetherianity, Noetherian submodule finiteness,
  localization and base change of finite presentations, projective vector spaces,
  projective tensor products, projective flatness, and
  `Sheaf.RingTheory.LocalUniversalInjectiveResidue` with
  `Module.universallyInjective_of_residueField_injective`.
  The proof-only node lem-sfb-local-algebra-module-noetherian-subring-model has no
  recorded Lean statement in the read checkout; it has no module to import.
  It is not needed to type the present statement. Its mathematical use remains
  explicit in proof step 4 and the unchanged proof_deps.

Edge cases checked before writing: N=0 allows P=0; S containing zero is allowed
and then N=0, with s=0 and zero localization allowed; B=0 is allowed too. Empty
presentation matrices use denominator one as the proof specifies. I=0 is allowed.
No finite-rank assertion on the projective R/I-module is made. The zero base ring
is already excluded by the node's requirement of a unique maximal ideal, exactly
as by IsLocalRing. No Noetherianity or flatness of R, B or N was added.

Searches made on 2026-10-24:

- msearch.py LeanFinder: "A finitely presented module over a localization of a
  finitely presented algebra over a local ring has a projective pure spreadout
  modulo a finitely generated ideal". Eight hits, including
  Module.projective_of_localization_maximal',
  Module.FinitePresentation.exists_free_localizedModule_powers, and
  IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation.
  None constructs a finite quotient and a pure projective spreadout.
- msearch.py Loogle: "Module.Projective, IsLocalizedModule". Two hits,
  Module.projective_of_isLocalizedModule and
  Module.projective_of_localization_maximal'; both concern projectivity already
  present before localization or at maximal localizations, not this conclusion.
- msearch.py LeanSearch: "A finitely presented module over a localized finitely
  presented algebra has a projective pure spreadout modulo a finite ideal".
  Eight hits on projectivity/finiteness/localization, no exact statement.
- msearch.py grep: "pure.*spread|spread.*pure", RingTheory. Zero hits.
- rg on lean/WeilConjectures for pure/spread and universallyInjective found
  unrelated scheme-theoretic spreadouts and radicial morphisms. The item-id search
  there found no match. rg on lean/Sheaf found residue and fibre-injectivity
  statements and unrelated purely inseparable spreading; none states this lemma.
- Exact new declaration-name search of Mathlib, WeilConjectures and Sheaf found
  no match. The upstream name index contains no pureSpreadout declaration.

The theorem docstring includes all seven proof steps and their dependency ids.
The prescribed scompile.py compiled the module successfully in sandbox and
library modes. No statement correction, new node, dependency repair, or disputed
mathematical statement is needed.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
