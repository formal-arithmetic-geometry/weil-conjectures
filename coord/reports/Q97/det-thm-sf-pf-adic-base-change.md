## Worker report

The delivery states `det-thm-sf-pf-adic-base-change` in
`Sheaf.Paper.IntegralLocalizingProperBaseChange`, declaration
`AlgebraicGeometry.ProEtale.CondensedRing.integralLocalizing_properBaseChange`.
Its only theorem proof is `sorry`, with the node's six-step proof in its docstring.
The statement of the node is unchanged. The stage-1 repair note is resolved and asks
that this statement remain unchanged; its split proof is retained verbatim in JSON.

Hypothesis-by-hypothesis and clause-by-clause reading:

| Source | Lean |
| --- | --- |
| Fixed prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field k of positive characteristic different from ell | `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`; the characteristic of a field is zero or prime, and the prime condition excludes zero |
| Finite coefficient extension E/Q_ell, inside an algebraic closure | `(E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra E (PadicAlgCl ℓ)] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]` |
| Valuation-ring coefficients O_E with their ell-adic topology | `Profinite.padicIntegersRingObj ℓ E`, the published continuous-map condensed ring underlying `PadicAlgCl.integers ℓ E` |
| Four schemes over k | `{X' X Y' Y : Scheme.{u}}` and four `.Over (Spec (.of k))` instances |
| All four separated and finite type over k | for each corner T, `[LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]` |
| The four arrows are k-morphisms | `p`, `g`, `p'`, `g'` have the displayed domains and codomains and `.IsOver (Spec (.of k))` instances |
| p is proper | `[IsProper p]`; properness of p' is not assumed separately |
| Cartesian square, including the chosen identification | `sq : ChosenCartesianSquare g' p' p g` |
| Ordinary unbounded module-object derived category | K is in `DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj ... X))` |
| Source Loc(Dbc(X,O_E)) | `hK : CategoryTheory.localizingClosure (constantModelBoundedConstructible ... X) K` |
| g* Rp* lands in Loc(Dbc(Y',O_E)) | first conjunct applies the same closure predicate at Y' to `(lowerStar ... p).rightDerivedFunctor ⋙ (upperStar ... g).leftDerivedFunctor` evaluated at K |
| Rp'* g'* lands in Loc(Dbc(Y',O_E)) | second conjunct applies that predicate to `(upperStar ... g').leftDerivedFunctor ⋙ (lowerStar ... p').rightDerivedFunctor` evaluated at K |
| The specified base-change map is an isomorphism of these functors | final conjunct is `IsIso ((condensedAmbientExchange ... sq).app K)` for every K satisfying hK |

The last three clauses are an exact pointwise encoding of the stated isomorphism
between full subcategories: the two landing clauses permit restriction of the
ambient functors and transformation, and a natural transformation is invertible
precisely when all its components are. They do not assert preservation by the
individual edges, an extra theorem not stated in the item. The closure uses Dbc
itself, not a replacement by Dctf or by the derived-complete category. The existing
generic `CategoryTheory.localizingClosure` is necessary because the convenience
`localizingClosureProEtale` specifically closes Dctf. Both use exactly the same
published intersection construction and ambient coproduct size convention.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, with its inherited `CommSq`, chosen
  pullback isomorphism and two projection equations.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  its locally-finite-type/closed/separated definition is finite type because
  universally closed implies quasi-compact, as the recorded dependency explains.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing field/scheme binder convention and `compactificationOverField`.
  No compactification is used by the ordinary proper exchange. All setting
  hypotheses are explicit binders; no new setting predicate is introduced.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`, with its
  boundedness and constant-scalar-model constructible cohomology conditions.
- `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.localizingClosure`, the
  intersection over full replete triangulated coproduct-closed subcategories.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `CondensedRing.derivedUpperStarLowerStarAdjunction`,
  `CondensedRing.leftDerivedUpperStarComp`, and the generic total
  `Functor.leftDerivedFunctor` and `Functor.rightDerivedFunctor` applied to
  the entire published `CondensedRing.upperStar` and `lowerStar` composites.
- The repaired ambient-exchange dependency is described below. Its module
  publicly retains `Scheme.proEtaleAmbientRingedExchange` and
  `Scheme.pbcActualCompletedAmbientExchange`, and supplies
  `CondensedRing.condensedAmbientExchange` for the category actually used here.
- Already stated proof-dependency modules are imported: the recorded
  right-derived convention module, integral finite pullback-composition module,
  ordinary pro-etale pushforward-composition module, and the module-object
  upper/lower-star module. Adjunction conjugacy and properness
  permanence use the existing Mates and Proper Mathlib imports. The bounded
  integral theorem, integral models theorem, localizing proper-image theorem,
  unbounded pullback theorem, and unbounded extension theorem have no recorded
  declaration or closed upstream audit on this base; they are proof inputs only,
  not additional assumptions of this stage-2 statement.

Edge cases checked by inspecting the quantifiers and canonical construction:

- K=0 and empty schemes are permitted; no nonempty or positive-rank assumption.
- g is arbitrary: no flatness, smoothness or etaleness is assumed.
- Identity edges and the identity square remain in the domain. The middle
  equality transport is `congrArg` on the actual scheme-morphism equality; it
  does not require a chosen arbitrary comparison.
- The closure includes arbitrary ambient coproducts, including the empty one;
  no boundedness, Tor-amplitude, completeness, or finite support is imposed on K.
- Every corner has the same scheme universe u, and the sheaf values use Ab.{u+1}
  on the small pro-etale site. No equality of the site object and morphism
  universes is imposed. E is the ordinary small finite extension used by the
  existing p-adic coefficient API (every finite extension of the small Q_ell is
  isomorphic to such a small field); the profinite testing universe is still u.
- No condition that the two pullback routes use separately chosen coefficient
  isomorphisms occurs: all are the published pullbacks of one condensed ring
  from the point. The composition API retains this canonical choice.

Searches performed on 2026-10-18:

- `msearch.py ... leanfinder "proper base change on the localizing closure of
  bounded constructible integral pro-etale module objects"`: 8 hits, on source
  local closures and stability of geometric morphism properties; no match.
- `msearch.py ... leansearch "Proper base change is an isomorphism on the
  localizing category generated by bounded constructible integral pro-etale
  sheaves"`: 8 hits, on properness/base-change stability and Kan extension;
  no integral derived-sheaf match.
- `msearch.py ... loogle "CategoryTheory.NatTrans, CategoryTheory.IsIso"`:
  0 hits.
- `msearch.py ... grep "localizing|proper.*baseChange" CategoryTheory`:
  21 hits, mainly base-change stability and Verdier localizing subcategories;
  no integral derived-sheaf theorem.
- `rg` in the upstream WeilConjectures tree and `lean/Sheaf` for
  `localizingClosure`, the item id, `proper.*localizing`, `baseChange`,
  `condensedAmbientExchange`, and `integralLocalizing_properBaseChange`:
  the only localizing definition is the dependency; the upstream bounded
  constructible base-change definition is not a theorem on Loc(Dbc).
  No collision for the new declaration names. Checked the name registry too.
- Read the exact module-object base-change definition in the published side
  framework, the derived composition and adjunction signatures and docstrings,
  the coefficient ring construction, and the blueprint statement/proof files.
  No existing unbounded condensed module-object exchange was found. The older
  `ProEtale.derivedBaseChangeMap` concerns a fixed external coefficient category,
  not internal modules over this condensed-ring pullback.

No statement correction, disputed statement, or new DAG node.

## Dependency modules

`def-weil-pbc-ambient-ringed-exchange`: repaired under section 1(B) in
`Sheaf.Paper.CondensedAmbientExchange`. The prior record's primary declaration
`Scheme.pbcActualCompletedAmbientExchange` uses a completed coefficient datum
and `SheafOfModules`; the general `Scheme.proEtaleAmbientRingedExchange` it
reexports uses arbitrary sheaves of commutative rings and the same external
module encoding. Neither has the signature on the ordinary internal module
objects over `condensedRingObj` required by this item. Publicly importing the
recorded module preserves the entire general notion, including arbitrary
compatible ring-sheaf squares and the existing completed specialization.
The added internal-module form supplies the missing interface without replacing
the node's general statement by this specialization.

`condensedAmbientPullbackComparison` is the composite of
`leftDerivedUpperStarComp Λ p' g` inverse, equality transport along the square,
and `leftDerivedUpperStarComp Λ g' p`. The component maps of these published
isomorphisms are induced by the canonical ordinary tensor pullback composition,
not arbitrary equivalences. `condensedAmbientExchange` is literally `mateEquiv`
of that comparison for `derivedUpperStarLowerStarAdjunction Λ p` and its p'
version. These are definitions with complete data; no existence theorem or
Nonempty choice is added. They render exactly the dependency's displayed
unit/comparison/counit construction in the ordinary internal module-object
presentation; no extra proposition or postponed comparison theorem is asserted.
Only `lean` changes in the dependency node, with the required explanatory note.

## Second reading by Q97

I reopened the node, its blueprint statement, both delivered files and the
recorded dependency interfaces after drafting. This is an in-thread second pass,
not a claim that another worker reviewed it: the dispatch brief prohibits
starting agents and the maintainer performs the independent review.

The four scheme/arrow types and the chosen square have the stated orientation.
The two endpoint functors are in diagrammatic order Rp* then Lg*, and Lg'* then
Rp'*. The comparison runs Lg* then Lp'* to Lp* then Lg'*, so taking its mate
inserts the p' unit and contracts the p counit, as required. The field and finite
extension hypotheses are exactly the standing setting. The localizing source
and target close the constant-model Dbc predicates directly. In particular I
checked that using the convenience Dctf closure would have silently substituted
an equality that belongs in the later proof, so the file uses the generic
closure instead. Both landing clauses and pointwise invertibility are present.
No hypothesis on g, on p', or on completeness of arbitrary sums was added.
No mismatch requiring a statement correction was found.

## Validation

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q97
 det-thm-sf-pf-adic-base-change
 lean/Sheaf/Paper/CondensedAmbientExchange.lean
 lean/Sheaf/Paper/IntegralLocalizingProperBaseChange.lean` completed with exit 0:
both modules compiled separately in dependency order, in sandbox and library
positions, with no errors or warnings. The first attempt exposed the missing
published `CategoryTheory.Obj` scoped instance for the coefficient monoid object;
the final file explicitly opens that scope. No universe or mathematical
hypothesis was added to solve the elaboration issue.
