## Worker report

This is the stage-2 statement of `lem-per-open-closed-constructible-test` in
`Sheaf.AlgebraicGeometry.OpenClosedConstructibleTest`, declaration
`AlgebraicGeometry.Etale.isBoundedConstructible_iff_open_closed_exceptional`.
Its only proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement changes.

The predecessor's blocker confused the reviewed stage-1 split with a Lean delivery:
Q25's report explicitly says that no Lean code was written, and the current node has no
`lean` record. This delivery retains the nine reviewed proof steps and every other node
field. It neither splits the node again nor re-pushes Q25's branch.

I read the item, every statement dependency's statement and binding, the full declarations
and their docstrings, the example CompactObject module and record, the worker and stage-2
rules, and delivery-errors section H. The current source of the derived-category dependency
and of the closed-ambient adjoint was also obtained with `scompile.py --source`.

The source is the local PDF *Travaux de Gabber*, Expose XVII, Lemma the project server (printed
page 294). I read its statement and its proof citing XIII-1.1.1, together with Q25's
reviewed expansion using XIII-1.1.1 and paragraph 1.1.2. The source says exactly that a
bounded-below complex is bounded constructible iff its ordinary open restriction and
exceptional closed restriction are. No finite-type-over-a-field or Krull-dimension bound
is added.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The exponent is `(n : ℕ) (_hn : 1 ≤ n)`.
- The coefficient ring Z/ℓ^n is `ULift.{u + 1} (ZMod (ℓ ^ n))`. This is the canonical
  universe lift with the transported ring structure, allowing the coefficient and module
  universes required by the recorded small-etale interface. It adds no ring parameter,
  scalar map, or algebra hypothesis. Primality supplies nonzero modulus and finiteness.
- The schemes are `{X Z U : Scheme.{u}}`; `[IsNoetherian X]` is exactly Noetherian X.
- Excellence of X is `_hexc : ∀ V : X.affineOpens, IsExcellent Γ(X, V)`, applying the
  recorded excellent-ring notion to each affine coordinate ring. This is the same
  formula as the existing `Orgogozo.IsExcellentScheme`; it is an expanded hypothesis,
  not a second definition of excellence. No additional conditions on Z or U are assumed.
- Invertibility of ℓ on X is `_hinv : ∀ x : X, IsUnit (ℓ : X.presheaf.stalk x)`.
  Invertibility in every local ring is exactly invertibility of the constant integer
  section; it also handles the empty scheme.
- `(i : Z ⟶ X) [IsClosedImmersion i]` and `(j : U ⟶ X) [IsOpenImmersion j]` use the
  recorded Mathlib predicates. `_hij : Set.range i.base = (Set.range j.base)ᶜ` expresses
  that j is complementary to i, with no choice of reduced structure on Z.
- `K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat ...))` is
  exactly K in D+(X_et,Λ). `K.obj` is its inclusion in the ordinary derived category.
- The left side is `DerivedCategory.isBoundedConstructible ... X K.obj`, using exactly
  the recorded finite-stratification constructible-cohomology predicate and bounded
  cohomology interval, not a private copy or the distinct upstream predicate.
- The first right-hand conjunct applies that same predicate on U to
  `((upperStar (ModuleCat ...) j).mapDerivedCategory).obj K.obj`: exact ordinary
  small-etale inverse image induces the required j* on the derived category.
- The second right-hand conjunct applies the predicate on Z to
  `(R(lowerStar (ModuleCat ...) i)).rightAdjoint.obj K.obj`. The existing instance
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` supplies this adjoint;
  its universal property determines it. It is not an arbitrary chosen map or a new
  hollow definition. Exact closed direct image agrees with Ri_*, and for a closed
  immersion with Ri_!. The ambient adjoint on a bounded-below input agrees with the
  bounded-below adjoint: in the closed-support triangle the other terms are bounded
  below, hence i_*Ri^!K is bounded below; i*i_* ≅ id then gives the assertion on Z.
  This is precisely step 7 of the node, reproduced in the declaration docstring.
- The biconditional `↔` and conjunction `∧` give both directions and both restrictions.

Dependency declarations used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (and its actual quasi-excellent and
  universally-catenary definitions), at the affine coordinate rings of X.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient
  interface: `AlgebraicGeometry.Etale.DerivedCategoryModule`, `_root_.DerivedCategory`,
  `_root_.DerivedCategory.Plus`, and `_root_.DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, the recorded
  ordinary module-coefficient compact-support convention. The theorem uses the closed
  direct-image adjoint supplied by the next dependency rather than rebuilding Rf_!.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
  Mathlib's `Functor.rightAdjoint` selects the right adjoint characterized by this theorem.

The module imports every recorded proof-dependency module, with plain imports for
proof-only inputs, including the Mathlib exact-functor homology, closed-is-finite, and
complex-short-exact-sequence leaves. The Gabber open-immersion sheaf-finiteness node has
no recorded Lean declaration, so it has no module to import. The declaration docstring
contains all nine proof steps, including coefficient forgetting, the finite powers-of-ell
filtration, truncation induction, the bounded-below restriction of the adjunction, and
both implications.

Edge cases checked: U empty, Z empty, X empty, n=1, K=0, a complex with one nonzero
cohomology sheaf in any integer degree, and a nonreduced closed subscheme. There are no
nonempty binders, dimension bounds, reducedness, finite-type or regularity assumptions.
The complementary-image condition gives the expected identity/zero criterion in the
empty-open and empty-closed cases. The exponent boundary n=1 gives F_ℓ coefficients;
n=0 is intentionally excluded exactly as the node requires. The scheme universe u is
arbitrary and the module universe is u+1, as in the recorded dependency interfaces.

Searches actually run:

- `msearch.py`, LeanFinder, query: "A bounded below complex of etale Z mod prime power
  sheaves is bounded constructible if and only if its open restriction and exceptional
  closed restriction are bounded constructible". Eight results concerned constructible
  topological subsets and affine coordinate rings; none states this derived criterion.
- `msearch.py`, Loogle, query: `"constructible", "DerivedCategory"`. Zero hits.
- `msearch.py`, grep, query:
  `constructible.*(rightAdjoint|upperShriek)|exceptional.*constructible`. Zero hits.
- `rg` in both the source project and `lean/Sheaf` for the node id, exceptional
  constructibility, and `isBoundedConstructible_iff`: no exact theorem. The upstream
  `ConstructibleSheaf/OpenClosed.lean` is about ordinary restrictions of sheaves.
  `SixFunctors/Etale/Derived/Stability/UpperShriekConstructible.lean` only gives a
  preservation assertion with a finite-type-over-a-field hypothesis, not this theorem
  over arbitrary Noetherian excellent schemes.
- `rg` for `IsExcellentScheme` found the existing expanded affine-ring formula in
  `Sheaf.Paper.OrgogozoInductionData`; this is why no second excellent-scheme definition
  is introduced. `rg` for derived adjoints and the constructibility predicate found
  the dependency interfaces used above.

No `STATEMENT-DISPUTED` issue or mathematical node fault was found. The stage-1 PASS
is retained; this delivery only supplies its missing Lean statement.

Additional search: `msearch.py`, LeanSearch, query "Bounded constructible complexes on
excellent schemes detected by open inverse image and exceptional closed inverse image".
Eight results concern constructible topological subsets and their images/preimages; none
states the derived étale criterion.

Validation: `scompile.py Q03 lem-per-open-closed-constructible-test` compiled the delivered
file cleanly, both as its isolated sandbox module (6.0 seconds) and as the intended library
module (5.7 seconds), within the default 60-second limit. The first elaboration caught
whitespace before field-projection dots; those expressions were corrected and the clean
compile is for the final signature. The node differs from the live node only in `lean`;
the signature is copied verbatim from the theorem, and every line is at most 100 characters.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
