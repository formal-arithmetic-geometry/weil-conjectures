## Worker report

The module `Sheaf.Paper.DualizingLocallyClosedInheritance` defines the canonical
`etaleEvaluationBiduality` component and states
`AlgebraicGeometry.Etale.exists_dualizing_of_isImmersion`, with one postponed proof.
No mathematical hypothesis or conclusion of the node is changed.

Hypothesis-by-hypothesis and clause-by-clause:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient field is
  `ULift.{u + 1} (ZMod ℓ)`, the usual universe-lifted prime field. The lift is required
  by the existing ordinary-etale coefficient API, not an extension of coefficients.
- The ambient scheme is `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's `IsNoetherian`
  means locally Noetherian and quasi-compact, equivalently a finite Noetherian affine cover.
- The auxiliary commutative Noetherian F_ell-algebra is `(A : Type a) [CommRing A]
  [IsNoetherianRing A] [Algebra (ZMod ℓ) A]`. Its universe `a` is independent.
  No finiteness or dimension assumption on A is added. A does not occur in the conclusion,
  exactly as noted in Step 8 of the DAG proof.
- The ordinary small-etale module derived categories are `DerivedCategoryModule`:
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} ...))`, and similarly on T.
  These are neither the pro-etale categories nor finite-Tor-amplitude subcategories.
- Bounded constructible means `DerivedCategory.isBoundedConstructible`. This is the landed
  finite-coefficient predicate: all homology sheaves admit a finite locally closed
  stratification and local constant finite module descriptions, and vanish outside one
  bounded integer interval. Over F_ell, finite modules are exactly finitely generated
  modules. On the Noetherian X and every immersed T, the additional constructibility of
  the strata in that predicate is automatic. Thus it has exactly the node's meaning.
- `hX : ∃ Q, ...` is existence of a dualizing object on X. Its first conjunct puts Q
  in D^b_c. The universal clause quantifies over every M of the ordinary derived category,
  conditional only on M being bounded constructible. Its first conjunct says RHom(M,Q)
  is bounded constructible. The second says that the canonical evaluation-transpose
  arrow is invertible, using `IsIso`, not mere existence of an unrelated isomorphism.
- RHom is the existing `Etale.derivedHom` exposed by the recorded
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` module. Evaluation is the counit
  of `derivedTensorHomAdjunction`. The pairing first applies `derivedTensorSymmetry` to
  swap M and RHom(M,Q) with the canonical cochain Koszul sign, then evaluates. Applying
  the tensor-Hom `homEquiv` gives M -> RHom(RHom(M,Q),Q).
- `(T : Scheme.{u}) (f : T ⟶ X) [IsImmersion f]` quantifies over every locally closed
  subscheme, including nonreduced ones. Mathlib's `IsImmersion.isImmersion_iff_exists`
  is precisely factorization as a closed immersion followed by an open immersion.
  No separate hypothesis that T is Noetherian is imposed; it follows from X and f.
- The conclusion is `∃ Q` on T with exactly the same three conditions: Q belongs to
  D^b_c, internal Hom preserves D^b_c, and every canonical biduality arrow is invertible.
  There is no excellence, dimension bound, cohomological-dimension bound, invertibility
  of ell on X, base field for the schemes, or reducedness assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness meaning.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`
  and the ordinary derived-category interfaces, publicly imported by its recorded module.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (finite, without constructible-stratum axiom).
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules`. Its site-level definition uses
  covering sieves and constant finitely generated coefficient modules. The ordinary-etale
  finite-coefficient constructibility interface already packages the equivalent condition;
  the theorem does not attempt to use this `SheafOfModules` object as a `Sheaf ModuleCat`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `Etale.derivedHom`, `Etale.derivedTensorHomAdjunction`, the recorded ordinary-etale
  presentation. Its complete generic ringed-site construction is retained unchanged.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` and its factorization.
- Additional landed dependencies cited in stmt_deps:
  `def-weil-pbc-constructible-complexes` gives
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `Etale.DerivedCategory.isBoundedConstructible`;
  `lem-kun-tensor-sym` gives `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`,
  `Etale.derivedTensorSymmetry`. Both additions are acyclic.

Every recorded proof dependency module is imported for stage 3. The as-yet unstated
`lem-per-relative-bidual-triangles` and `lem-per-finite-exceptional-internal-hom` have no
module to import. Mathlib proof tools are imported directly. The declaration docstring
contains all eight natural-language proof steps, including the normalized comparison
of the actual biduality maps in the closed case.

Source checked directly: ILO PDF printed p.311 (PDF page 317), proof of Proposition 7.6.3,
which states that j^*K is dualizing, and printed p.313 (PDF page 319), proof of
Proposition 7.6.9, which states that existence is preserved on subschemes.

Edge cases checked: the empty subscheme (zero derived category and zero dualizing object),
identity immersion, pure open and pure closed immersions, nonreduced closed subschemes,
characteristic ell, degree-zero complexes, and schemes without any dimension bound.
The finite-stratification predicate allows zero strata for the empty scheme. Boundedness
is a property of each complex, not a common bound imposed on all complexes. All universe
variables are explicitly bound, and `autoImplicit` is false.

Searches for an existing statement:

- `msearch.py leanfinder`, query "A dualizing complex on bounded constructible etale
  sheaves restricts to locally closed subschemes": 8 generic scheme/open-restriction hits,
  including `isRetrocompact_basicOpen` and `exists_of_res_zero_of_qcqs`; no matching theorem.
- `msearch.py loogle`, query "dualizingComplex, IsImmersion": 0 hits, unknown identifier
  dualizingComplex in the Mathlib search service.
- `msearch.py grep`, query "dualizing|Dualizing|biduality": 10 unrelated Mathlib hits
  (duality of categories, homotopy fibres, and comments); no matching statement.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for dualizing,
  biduality, bounded constructible and the proposed declaration name; upstream Verdier
  results require a finite-type morphism over a field with invertible exponent and do
  not state this arbitrary-Noetherian inheritance assertion. The explicit upstream
  `grep -rn` for the item id found no declaration.
- `CoefficientChangeDualizing.biduality` supplies the same evaluation transpose downstream,
  but its owning theorem reaches this item via coefficient comparison and condition (B).
  Importing that module would create a cycle; it is not imported. The owning-node
  helper `etaleEvaluationBiduality` exposes the canonical map for arbitrary ordinary-etale
  Q and M by the existing adjunction and symmetry, as authorized for canonical-map helpers.
  It introduces no independent mathematical notion, no extra hypothesis, and no data from
  a sorry. Its defining expression is the same canonical evaluation transpose. Factoring
  the typed generic component is necessary for elaboration: a fully expanded prime-field
  expression times out at 60 seconds, while the typed component and statement compile in
  about three seconds. No time limit was raised.

No statement correction, new DAG node, dependency replacement, or disputed statement.

## Second reading by Q62

Author's second pass, with the JSON statement and Lean file open; the maintainer supplies
independent review. Checked each binder against the node: the prime, Noetherian X, unused
auxiliary Noetherian algebra A, ordinary-etale coefficients, existence assumption, and
arbitrary immersion are all present. In each existence clause the boundedness of Q,
preservation under Hom, and invertibility of the actual transpose are separate conjuncts.
Checked the order of the symmetry and counit: the pairing begins M tensor D(M), swaps to
D(M) tensor M, and evaluates into Q; the adjunction is for D(M), so its transpose has
exactly the double-dual target. There are no extra assumptions on T. The two landed
statement-dependency additions provide existing definitions and create no dependency cycle.
No mathematical mismatch was found. All postponed proof content is in the named theorem;
there is no hollow object or choice of an arbitrary isomorphism.
