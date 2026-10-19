## Worker report

The module `Sheaf.SixFunctors.EtaleInternalHomDevissage` states
`AlgebraicGeometry.Etale.isBoundedConstructible_finiteTor_derivedHom_by_devissage`.
Its sole theorem has proof `sorry`; it introduces no definitions. The ten-step DAG proof,
including all named inputs, is copied into its source docstring. Only the item's `lean`
field changes. No statement correction, new nodes, dependency repairs, or mathematical
statement disputes are needed.

Hypothesis and clause mapping:

- Separably closed field k: `(k : Type u) [Field k] [IsSepClosed k]`.
- The prime ell different from the characteristic: `(ℓ : ℕ) [Fact ℓ.Prime]`
  and `(_hℓ : (ℓ : k) ≠ 0)`. In a field, for a prime ell, its image is nonzero
  exactly when ell differs from the characteristic (including characteristic zero).
- Finite commutative ell-primary A: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  and `(_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)`. An ell-power annihilates 1 and hence
  every element. Conversely, a finite ell-primary additive group has a uniform
  ell-power annihilator. No presentation of A or nontriviality is assumed.
- Finite-type k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. This is exactly the recorded convention
  for finite type. There is no separatedness hypothesis.
- K and L in the ordinary ambient derived category: `(K L : DerivedCategoryModule A X)`.
  This unfolds to `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`,
  the recorded fixed-scalar presentation of modules over the constant ring sheaf.
- Bounded constructibility of each: `_hKc` and `_hLc` use the recorded
  `DerivedCategory.isBoundedConstructible A X`. This demands constructible
  cohomology in the finite-constant-module sense and a nonempty bounded interval
  outside which cohomology vanishes.
- Finite Tor amplitude of each: `_hKt` and `_hLt` are
  `∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K`
  (respectively L). The existing predicate tests *every* degree-zero module sheaf.
- Ambient internal Hom: `((derivedHom (ModuleCat A) X).obj (op K)).obj L`.
  This is the existing unbounded etale derived Hom, not a Hom of a constructible
  subcategory or a site-perfect specialization.
- Conclusion: the conjunction of `isBoundedConstructible` of that same Hom object
  and `∃ a b, a ≤ b ∧ hasTorAmplitudeIn ...` of that same object. There is no
  specified sharp bound or extra site-perfect assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its quasi-compactness counterpart
  `AlgebraicGeometry.QuasiCompact` is in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.Etale` and `Scheme.smallEtaleTopology` (inside the
  recorded derived-category abbreviation).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, read through
  `scompile.py --source`, and `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`, read through
  `scompile.py --source`: `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, and its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its full signature and its
  K-injective model/comparison docstrings were read. That interface uses
  `SheafOfModules` over a ring sheaf. The node's recorded ordinary etale category
  instead uses fixed-scalar `Sheaf ... (ModuleCat A)`. The already existing
  `AlgebraicGeometry.Etale.derivedHom` in
  `WeilConjectures.SixFunctors.Etale.Derived.Hom` is the ambient internal Hom
  in this presentation, also used by the etale clause of the recorded proof
  dependency `lem-weil-stratum-ambient-hom`. No second Hom construction is made.
  Its implementation was read down to
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`:
  `internalHomQhObj` right derives the sheaf Hom complex by K-injectives, and
  `monoidalClosed` transports it from a representative to an arbitrary derived
  object. Thus this is precisely the ringed-site derived internal Hom in the
  recorded category, expressed through the existing fixed-scalar API. It does
  not assume a constructible replacement or a bounded/projective first argument.

All recorded proof-dependency modules are imported without `public`. Nodes whose
proof declarations are not yet recorded have no invented import. Statement imports
are public. No import cycle was encountered by the compiler.

Edge cases checked before writing:

- Empty X: no nonemptiness binder; every relevant sheaf is zero, so the conclusion holds.
- Zero A: permitted; n=0 in the annihilator condition forces precisely 1=0.
  All module sheaves and derived objects then vanish.
- K=0 or L=0: the Hom vanishes; it has Tor interval [0,0] and is constructible.
- Singleton Tor intervals are allowed. The quantified witnesses require a≤b,
  exactly as the node requires; no uniform input-dependent sharp output bound
  is asserted. In particular the closed-point-in-a-curve example obstructing
  [a-e,b-c] globally is not silently included as an extra conclusion.
- Positive and zero characteristic, imperfect separably closed fields, arbitrary
  shifts, nonreduced schemes, and nonseparated finite-type schemes remain included.
- Universe: X and its base field live in u, coefficients and module values in u+1,
  exactly as the recorded ordinary etale category requires. This is the project
  convention, not a restriction to finite-dimensional or constant sheaves.

Searches made for an existing statement:

- `msearch.py leanfinder`: "Derived internal Hom preserves bounded constructible
  complexes of finite Tor amplitude on the small etale site". Eight results
  concern derived-category t-structure bounds; no exact statement.
- `msearch.py leansearch`: "Derived internal Hom preserves constructible complexes
  of finite Tor amplitude on etale site". Eight generic homology/functor results;
  no exact statement.
- `msearch.py loogle`: "AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn,
  CategoryTheory.derivedInternalHom". No results; the project identifier is unknown
  to the Mathlib service.
- `msearch.py grep`: `constructibleFiniteTor|Dctf|finiteTor.*[Hh]om|[Hh]om.*finiteTor`.
  No Mathlib hits.
- `rg` with that regex over upstream `WeilConjectures` finds
  `Etale.constructibleFiniteTor_derivedHom` in `Derived.Stability.Matrix`.
  Its full signature and surrounding variables were read. It uses
  `DerivedCategory.constructibleFiniteTor`, based on the distinct upstream
  `Scheme.IsConstructibleSheaf` notion, and invertible-exponent hypotheses.
  It does not literally state this node with the recorded finite-value predicate.
  Consequently it is not rebound as an exact existing statement.
- `grep -rn "det-rem-sf-matrix-hom-devissage"` over upstream `WeilConjectures`
  and `rg` of this id in `dag/lean_names_upstream.json`: no exact attachment.
- `rg` over `lean/Sheaf` for the Tor/constructible/Hom names finds the flat-model,
  triangulated-Hom, and stratum-Hom modules, whose interfaces were read; no exact
  closure statement. A search of the chosen new declaration name over upstream,
  Mathlib, and `lean/Sheaf` returns no collision.

Validation: `scompile.py Q07 det-rem-sf-matrix-hom-devissage` compiled the module
both as a sandbox file and under its intended module path, with no errors or
warnings. The library overlay also compiled `Sheaf.SixFunctors.FlatModelGeneration`.

## Second reading by Q07

I independently read the sandbox node and its entire Lean module, the cited
main-20261015 blueprint statement, and Stacks Tag 0F4M at
`etale-cohomology.tex`, `section-ctf` (including `definition-ctf` and
`lemma-when-ctf`). The blueprint supplies the field and coefficient hypotheses;
0F4M supplies the meaning of finite-Tor constructibility. Its Noetherian-ring
hypothesis follows from finiteness of A; finite type over a field makes X
Noetherian and quasi-compact, so its locally finite Tor dimension has a global
interval here. I found no mismatch requiring a mathematical or Lean change.

My object/hypothesis/conclusion checklist, in the order of the node:

1. Separably closed base field k: `(k : Type u) [Field k] [IsSepClosed k]`.
   Exact; algebraic closedness or perfection is not assumed.
2. Prime ell distinct from the characteristic: `(ℓ : ℕ) [Fact ℓ.Prime]`
   and `(_hℓ : (ℓ : k) ≠ 0)`. Exact: for a prime ell, its image vanishes
   in a field exactly when its characteristic is ell.
3. Finite commutative ell-primary ring A: `(A : Type (u + 1)) [CommRing A]
   [Finite A]` and `(_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)`. Exact: a uniform
   ell-power annihilator of 1 annihilates every element, and finiteness gives
   a uniform exponent from ell-primary additive torsion. No DVR presentation,
   residue-field assumption, or nontriviality is imposed.
4. X of finite type over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
   `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
   `[QuasiCompact (X ↘ Spec (.of k))]`. Exact. I opened the Mathlib classes
   in `Morphisms/FiniteType.lean` and `Morphisms/QuasiCompact.lean`;
   their conjunction is precisely the recorded finite-type dependency.
5. Ordinary ambient derived objects K and L: `(K L : DerivedCategoryModule A X)`.
   Exact. I read the recorded derived-category node and its current source
   using `scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategories`,
   then opened `Derived/Coefficients.lean`: the abbreviation is
   `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
   I also opened the small-etale-site dependency and Mathlib's
   `smallEtaleTopology`: it is the topology of jointly surjective etale
   coverings of schemes etale over X.
6. Bounded constructibility of both inputs: `_hKc` and `_hLc`, each using
   `DerivedCategory.isBoundedConstructible A X`. Exact. I read that dependency
   node and obtained its current full source with `scompile.py --source
   WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
   The body requires all cohomology sheaves to satisfy the recorded
   `Scheme.IsConstructibleEtaleModuleSheaf`, plus vanishing outside some
   `[a,b]` with `a ≤ b`. I fetched and read
   `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` too:
   its data are a finite stratification and etale-local constant finite
   A-module values on each stratum. This is the node's constructibility.
7. Finite Tor amplitude of both inputs: `_hKt` and `_hLt`, respectively
   `∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K`
   and the identical predicate on L. Exact. I read the Tor-amplitude node,
   its `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` module, and the actual
   bounded predicate in `Derived/Coefficients.lean`. It quantifies over
   every module sheaf F placed in degree zero and every degree outside
   the interval, requiring `IsZero` of the derived-tensor cohomology.
   The intervals for K and L are independent, as required.
8. Ambient derived internal Hom: both conclusion clauses use exactly
   `((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L`.
   Exact; the first argument is contravariant. I opened the general
   ringed-site dependency `DerivedInternalHomOfUniverses.lean`, including
   its construction and comparison signatures, and independently followed
   the fixed-scalar implementation through `Derived/Hom.lean` to
   `CategoryTheory/DerivedCategory/Monoidal/Closed.lean`.
   `internalHomQhObj` right derives the Hom-complex functor using
   K-injectives; `monoidalClosed` transports it along a source representative.
   Hence this is the same ambient ringed-site operation in the recorded
   fixed-scalar module-sheaf presentation, with no boundedness or site-perfect
   restriction hidden in its type. No second Hom construction is introduced.
9. Output belongs to the same Dctf: the conclusion is the conjunction of
   `isBoundedConstructible` of that Hom and an existential nonempty Tor
   interval for that same Hom. Exact. There is no prescribed output interval,
   extra dualizability conclusion, or restriction to constant test sheaves.
10. Explicit exclusions in the node: there is no separatedness assumption on
    X and no quotient-of-DVR presentation of A in any binder. Exact.

Edge cases: the empty scheme and K=0 or L=0 are admitted; there is no
nonemptiness assumption on X or on a stratification. The zero ring is admitted,
including the annihilator witness n=0 (which forces 1=0). Singleton Tor intervals
are admitted, and the output interval need not equal a coefficient-only sharp
bound. Characteristic zero and all positive characteristics other than ell,
nonreduced and nonseparated schemes, and imperfect separably closed fields are
included. The explicit universe u is arbitrary; X and k are in u and module
values and A are in u+1, exactly the recorded ordinary-etale convention. Finite
coefficient rings of any size can be represented in that universe. Every variable
and universe in the signature is explicitly bound; `autoImplicit` is false.

Independent searches (using wording different from the first reader):

- LeanFinder via `msearch.py`: "étale cohomology RHom bounded constructible
  finite tor dimension stability". Eight etale-morphism/ring results, no match.
- LeanSearch via `msearch.py`: "Internal sheaf Hom derived functor preserves
  constructible complexes with finite tensor amplitude". Eight underived
  sheaf-Hom, sheafification, and exact-functor results, no match.
- Loogle via `msearch.py`: `CategoryTheory.MonoidalClosed.internalHom,
  ObjectProperty`. No result; ObjectProperty was unknown to the service.
- Independent `rg` searches over Mathlib, upstream `WeilConjectures`, and
  project `lean/Sheaf` used `Dctf`, `Hom.*Tor`, `Tor.*Hom`,
  `isBoundedConstructible.*[Hh]om`, and `[Hh]om.*isBoundedConstructible`.
  Mathlib has no such etale preservation statement. I opened upstream
  `Etale.constructibleFiniteTor_derivedHom` in `Derived/Stability/Matrix.lean`
  and its `constructibleFiniteTor` definition in `Derived/TorAmplitude.lean`:
  it uses the distinct `boundedConstructible` predicate, rather than the
  recorded `isBoundedConstructible` interface. It is not an exact existing
  statement for this node. I also opened the project's
  `Paper/EtaleHomFiniteTorAmplitude.lean` and `Paper/FiniteConstructibleHom.lean`:
  their statements restrict coefficients to specified p-adic extension quotients
  over a finite-field datum (and the latter assumes separatedness), so neither
  replaces this arbitrary-finite-ring/separably-closed-field statement.
  Searching the node id and the new full declaration name in upstream, Mathlib,
  and project sources found no collision.

Delivery checks: there are no new definition nodes or dependency modules and no
statement correction or citer audit is needed. I checked every currently recorded
proof-dependency module against the imports; all are present as non-public imports,
while unstated proof nodes have no invented imports. The sole declaration is a
sorry-only theorem, with no definitions, private aliases, local notation, hidden
`let`/`show` binders, or extra assumptions. The module and theorem docstrings name
the source and blueprint id; the theorem docstring includes all ten DAG proof
steps and their named inputs. All lines are at most 100 characters, and the node's
`lean.statement` is verbatim equal to the theorem signature. Second reading changed
only this report; the Lean and node record were left intact.

Independent validation: `scompile.py Q07 det-rem-sf-matrix-hom-devissage
lean/Sheaf/SixFunctors/EtaleInternalHomDevissage.lean` passed both the sandbox
compile (2.4 seconds) and intended library-module compile (2.9 seconds), with
no errors or warnings.
