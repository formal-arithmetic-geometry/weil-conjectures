## Worker report

The module `Sheaf.AlgebraicGeometry.BoundarySheafConstructible` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_boundary_of_openImmersion_over_field`.
Its sole proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections.

Source checked: the node and its full proof; the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-fin-boundary-sheaf.md`
and `.proof.md`, and that unit's `_section.md`. The current statement is identical to the
node's older source statement. The proof docstring includes the reviewed node's extra
Noetherian argument ensuring that the pulled-back strata are constructible subsets.

Hypothesis and clause correspondence:

- The base field `k` is `{k : Type u} [Field k]`.
- The schemes are `{X U Z : Scheme.{u}}`. The structure over `k` is
  `[X.Over (Spec (.of k))]`.
- Finite type of `X` over `k` is
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together with
  `[QuasiCompact (X ↘ Spec (.of k))]`.
- The open immersion is `(j : U ⟶ X) [IsOpenImmersion j]`.
- The closed immersion of the complement is `(i : Z ⟶ X) [IsClosedImmersion i]`
  with `hcomplement : Set.range i.base = (Set.range j.base)ᶜ`.
  This retains exactly the complementary closed-support condition, with no extra
  reducedness hypothesis or chosen subscheme construction.
- The inherited coefficient convention is `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`,
  `(N : ℕ)` and `hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ X`.
  The recorded predicate means `0 < N`, finiteness of `Λ`, `(N : Λ) = 0`, and
  `IsUnit (N : Γ(X, ⊤))`. Its finiteness clause is also supplied as the instance needed
  to elaborate the recorded constructibility predicate. Invertibility on `U` and `Z`
  follows by pullback; no separate assumptions on those schemes are added.
- The module sheaf is `F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`;
  its constructibility is `hF : IsConstructibleEtaleModuleSheaf F`.
- The boundary sheaf is exactly
  `(Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F)`.
  The conclusion applies `IsConstructibleEtaleModuleSheaf` to this sheaf on `Z`.
  No derived functor, exceptional inverse image, or abelian-group forgetful functor
  replaces either coefficient-linear functor.

Dependency declarations read and used:

- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and its adjunction,
  in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`, same module.
- `sbc-def-coefficient-conventions`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`,
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`.
- `def-weil-pbc-constructible-complexes`:
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` publicly imports
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
  Read the current published source through `scompile.py --source` as well as the
  local side-project files: the recorded predicate uses finite constant module values
  on a finite constructible locally closed stratification. No duplicate predicate is defined.
- `def-weil-pbc-scheme-conventions` is a convention collector, with no declaration;
  the finite-type, open-immersion, and closed-immersion notions use Mathlib's definitions.
- Proof-only imports cover `thm-fin-open-degree-zero`
  (`Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible`),
  `prop-constructible-pullback`, `def-constructible-finite-locally-constant`, and
  `def-constructible-constructible` (`WeilConjectures.ConstructibleSheaf.Pullback`
  and its public dependency `Defs`), the finite-type Noetherian and minimal-closed-set
  matches (`Mathlib.AlgebraicGeometry.Noetherian` and its dependencies), and
  `def-weil-constructible-subset` (`Mathlib.Topology.Constructible`).

Edge cases checked before drafting: `U = X` leaves empty `Z`; empty `U` gives the zero
boundary sheaf; empty `X` is permitted; `F = 0` and the zero coefficient ring are permitted.
`N = 0` is excluded exactly by the positive-annihilator convention, while `N = 1` allows
only the zero coefficient ring. No separateness, smoothness, density, reducedness,
nonemptiness, or dimension assumption occurs. Arbitrary field characteristic is permitted
subject to the source coefficient convention. Schemes are in universe `u` and coefficients
and module values in `u + 1`, exactly as in the recorded small-etale-site interfaces.

Searches for an existing statement:

- `msearch.py` LeanFinder: “The inverse image on the closed complement of the pushforward
  of a constructible etale module sheaf under an open immersion is constructible”. Eight
  hits about constructible subsets or restrictions of structure-sheaf modules; no matching
  etale sheaf theorem.
- `msearch.py` Loogle: `"Sheaf", "constructible"`: zero hits.
- `msearch.py` grep: `ConstructibleSheaf|constructibleSheaf|constructible.*sheaf`:
  zero hits in Mathlib.
- `msearch.py` LeanSearch: “The closed boundary restriction of an open direct image of a
  constructible etale sheaf is constructible”. Eight hits about constructible subsets,
  scheme restrictions, and structure-sheaf modules; none matches.
- `rg` of the upstream `WeilConjectures/`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `lem-fin-boundary-sheaf`,
  `boundary.*[Cc]onstructible`, and `[Cc]onstructible.*boundary` found only unrelated
  boundary blow-ups, finite-boundary reconstruction, and curve cohomology results.
  The requested node-id search in the upstream tree found no declaration.
- A further search of upstream Etale and ConstructibleSheaf files for
  `IsConstructibleEtaleModuleSheaf`, `isConstructible.*lowerStar`, and boundary terms
  found no exact theorem. The open direct-image theorem alone does not state the
  boundary conclusion, and generic pullback constructibility alone does not include
  this open direct image.

Validation: `scompile.py Q32 lem-fin-boundary-sheaf` compiled the delivered module cleanly,
including the wrapper's sandbox and library-path checks. All universes and variables are
explicitly bound. Only the named theorem's proof is postponed. No statement dispute found.

## Second reading by Q32

A separate second pass by this same worker (the dispatcher brief prohibits other agents)
reopened the node and module and matched each clause: field and finite type, open `j`,
closed complementary `i`, the inherited coefficient convention, constructible module
sheaf on `U`, and constructibility of the literal composite `i^*j_*F` on `Z`.
The conclusion uses the finite-constant-value constructibility predicate that the recorded
complexes module imports, rather than substituting the general finite-stalk class.
The source has no separatedness or reducedness requirement. The coefficient assumptions
come from the explicitly named coefficient-convention dependency. The complement equality
has the correct orientation and involves the underlying point maps. Empty schemes and
zero coefficients remain allowed. No mismatch was found and no statement changed during
this second pass. The maintainer's independent review remains the external second reader.
