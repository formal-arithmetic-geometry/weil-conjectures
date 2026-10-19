## Worker report

The delivered item and its mathematical statement are retained. The theorem
`AlgebraicGeometry.OrientedNearbyCycles.exists_proper_surjective_constructible`
in `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` says the following.

- `X S : Scheme.{u}` and `[IsLocallyNoetherian S] [CompactSpace S]` give the arbitrary
  Noetherian base. There is no finite-dimensionality or excellence assumption.
- `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` express finite
  presentation under the recorded Stacks 01TP convention. No separatedness is imposed.
- `Λ : Type (u + 1)`, `[CommRing Λ] [Finite Λ]`, `m : ℕ`, `1 ≤ m`, `(m : Λ) = 0`,
  and `IsUnit (m : Γ(S, ⊤))` express exactly the finite coefficients and invertible
  positive annihilator. Annihilating 1 is equivalent to annihilating the whole ring.
- `K : EtaleDerived X Λ` and `IsBoundedConstructible X Λ K` require bounded constructible
  cohomology, without finite Tor amplitude or nonnegative amplitude.
- `q : ℤ`, `0 ≤ q` precede the existential `T,p`; the cover may depend on q.
- `IsProper p ∧ Surjective p` impose precisely the requested cover properties.
- `pullback.fst f p` is p_X, `pullback.snd f p` is f_T, `etaleModules(...).pull` is
  canonical derived inverse image, and `nearbyCycles` is the recorded Rψ_*.
  `DerivedCategory.homologyFunctor ... q` gives H^q. Constructibility now uses the
  existing canonical vanishing-site transport of the general oriented predicate.
- There is no comparison with RΨ_f K and no Ψ-goodness hypothesis.

The bounded-constructible helper is retained. It uses recorded `IsBounded` and, in every
integer degree, the recorded `Scheme.IsConstructibleEtaleModuleSheaf` after canonical
`orgogozoModuleSections` scalar restriction and `AsSmall.down` site transport. Its
`Nonempty` contains a module-linear isomorphism with a constructible sheaf, rather than
an arbitrary map or functor. The actual section groups and restriction maps are retained.

## Dependency modules

`def-weil-pbc-constructible-complexes`: retain `BoundedConstructibleTransport.lean`.
The original recorded fixed-ring small-etale derived predicate cannot be applied directly
to `EtaleDerived`, an intrinsic-module derived category on the transported site. This
helper states the same bounded-cohomology and constructibility conditions after the
canonical scalar/site identification. Its source-place docstrings have been made explicit.

`def-trf-oriented-constructible-sheaf`: omit Q73's dependency-record change and its
`TransportedConstructibleSheaf.lean`. Reuse the already landed
`Sheaf.Paper.OrientedConstructibleSheafVanishing`, with its canonical
`vanishingNormalization`, `vanishingModuleTransport`, and
`AlgebraicGeometry.OrientedConstructibleSheaf.IsConstructibleVanishing`. That definition
applies the existing general `IsConstructible` unchanged, preserving the two-map notion.
The retained item imports this existing module directly. No definition is duplicated.

## Second reading by Q73

This replacement section records the maintainer's independent correction to the
delivered second reading. I read the immutable item, all eight statement dependencies, all three delivered
Lean files, the original bounded-constructible interface, the general oriented predicate,
and the canonical vanishing-site transport. The hypothesis/conclusion correspondence is
listed above. The main theorem's signature is unchanged and its recorded statement remains
verbatim. The sole theorem proof remains `sorry`; both retained definitions have real data.

The delivered constructibility helper duplicated the finite-stratum/local-constancy formula
and reused an already occupied fully qualified declaration name. Replace it by the landed
canonical transport, leaving the general dependency record intact. This removes the need to
import the downstream `PsiGoodOrientedCohomologyStrata` theorem just to obtain helpers.
The theorem docstring now contains all 19 DAG proof steps, with their named dependencies;
the delivered one-paragraph summary omitted those details. Direct non-public imports of
the recorded, already stated proof dependencies have also been restored for stage 3.

Sources read: Lu--Zheng arXiv:1712.10216v7, Theorem 4.27 and its proof (printed pp.37–38),
including the finite-ring specialization and the last application to bounded input;
Orgogozo author draft, Theorems 1.1 and 7.1, §§2.1,8.1,9.1–9.3. These give finite
constructible locally closed partitions and finite local module values, without extra
Tor, excellence, dimension or Ψ-goodness hypotheses on the item.

Edge cases: empty X or S and zero complex are admitted; q=0 is included; m=1 forces
Λ=0 and is admitted; zero coefficient ring is permitted; negative input cohomology is
allowed; infinite-dimensional Noetherian bases and nonseparated finite-presentation maps
are allowed; empty strata impose no unwanted nonemptiness. The coefficient size follows
the recorded small-etale module convention, with canonical `Coeff` ULift; no new size
equality is imposed. The reused vanishing predicate supports independent universes.

Searches: the worker's LeanFinder, Loogle and Mathlib grep searches found no main theorem.
Independent rg searches of Mathlib, WeilConjectures and lean/Sheaf found ordinary bounded
constructibility, the general oriented predicate and the already landed canonical
`OrientedConstructibleSheafVanishing` interface. The latter is reused, not redeclared.
No new DAG node or source-based statement correction is introduced.

Compiler evidence: the immutable three-file delivery reproduced cleanly via scompile.py,
using its private side overlay and server confirmation. The retained fixed files were
also checked separately through scompile.py; see the independent review for exact times.
Only prescribed per-file compilation was used; no global build or live Lean edit.

Final fixed-file scompile check (with all proof imports) returned exit 0 with no errors
or warnings: bounded transport 2.6 s, theorem 4.6 s in server-confirmed library checks;
the separate private-overlay sandbox checks took 2.6 s and 4.5 s. Apply this report with
`--revert-nodes def-trf-oriented-constructible-sheaf` so the duplicate dependency module
and record are omitted and the landed canonical transport remains authoritative.
