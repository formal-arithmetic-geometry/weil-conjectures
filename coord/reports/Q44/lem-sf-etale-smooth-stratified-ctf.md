## Worker report

The module states `AlgebraicGeometry.Etale.exists_smooth_stratification_finiteTor`,
with its sole proof postponed by `sorry`. It introduces no definitions and changes
only the item's `lean` record. The theorem's docstring gives all nine DAG proof steps,
including reduction, stalkwise Tor tests against arbitrary modules, the prescribed
interval, and the proper/open interchange identifying the first triangle terms.

Hypotheses and conclusions correspond as follows:

- The arbitrary algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
  There is no characteristic or finite-field-origin condition.
- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the recorded coefficient universe for ordinary small-etale module sheaves.
- The F-scheme is `(X : Scheme.{u}) [X.Over (Spec (.of F))]`. Its structure morphism
  has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances, exactly
  separated and finite type. No properness hypothesis is imposed.
- The integers and their ordering are `a b : ℤ` and `hab : a ≤ b`.
- `K : DerivedCategoryModule A X` uses ordinary constant-A module sheaves.
  `hK : DerivedCategory.isBoundedConstructible A X K` is precisely the recorded
  bounded-constructible predicate, using `Scheme.IsConstructibleEtaleModuleSheaf`.
- `hTor : DerivedCategory.hasTorAmplitudeIn A X a b K` tests every module sheaf
  placed in degree zero using the recorded derived tensor and vanishing homology
  outside the closed interval. It includes infinite module sheaves.
- The finite collection of strata is indexed by `Fin m`, for existential `m : ℕ`.
  Each immersion is the composite `i r ≫ j r`, where `i r : S r ⟶ V r` is closed
  and `j r : V r ⟶ X` is open. The existential witnesses assert those properties;
  they are not assumptions on the input X.
- `IsReduced (S r)` means reduced structure sheaves, equivalently reduced local
  rings. `ConnectedSpace (S r)` means a nonempty connected stratum. `Smooth` applies
  to the composite structure map to `Spec F`. Thus these are F-subschemes.
- `Set.univ = ⋃ r, Set.range (i r ≫ j r).base` gives exhaustive coverage, and
  the `Disjoint` condition for unequal indices gives a partition.
- `e : Fin m → ℕ` assigns each stratum a finite dimension. For every
  `C ∈ irreducibleComponents (S r)`, `topologicalKrullDim C = (e r : WithBot ℕ∞)`
  is purity of dimension, while `(e r : WithBot ℕ∞) ≤ topologicalKrullDim X`
  is the required upper bound. Components carry their subspace topology.
- The family `P` is pinned by equality to the exact ordinary inverse image
  `(upperStar (ModuleCat A) (i r ≫ j r)).mapDerivedCategory.obj K`.
- For each r and integer q, `IsFiniteLocallyConstantSheaf` of the homology of
  `P r` expresses finite locally constant cohomology.
- A `Cover.{u} etalePrecoverage (S r)` is an etale cover of each stratum.
  For each member, `Q : CochainComplex (ModuleCat.{u + 1} A) ℤ` vanishes outside
  the SAME interval `[a,b]`, by `IsZero (Q.X q)` for `q < a ∨ b < q`.
- Each `Q.X q` is a direct summand of the finite free module `Fin n → A`:
  maps `ι` and `π` satisfy `ι ≫ π = 𝟙 (Q.X q)`. This is exactly the explicit
  finite-projective meaning in the node; no arbitrary projectivity datum is substituted.
  Since A is finite, these summands have finite underlying sets as well.
- The local derived isomorphism is between the inverse image of `P r` on the cover
  member and `DerivedCategory.Q.obj` of the termwise constant sheaf complex of Q.
  Hence the local models have constant finite projective A-modules as requested.
- `T : Fin (m + 1) → DerivedCategoryModule A X`, `T 0 = K`, and
  `IsZero (T (Fin.last m))` give the tower and its endpoints. For `r : Fin m`, the
  predecessor and successor are `r.castSucc` and `r.succ`.
- The three existential maps `α`, `β`, `δ` form `Triangle.mk α β δ ∈ distTriang _`.
  Their first object is literally the derived termwise open extension by zero of
  the exact closed direct image of `P r`, namely `j_! i_* P r`. The third map
  targets its shift by `(1 : ℤ)`. These triangles live in the unbounded ordinary
  etale derived category; no pro-etale coefficient category is used.

Recorded statement dependencies and declarations used:

- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-constructible-complexes`: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, `AlgebraicGeometry.Etale.derivedTensor`.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `prop-weil-pbc-inverse-image-modules-exact`: `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `lem-cbc-open-closed-recollement`: `Sheaf.AlgebraicGeometry.OpenClosedRecollement`, `AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-triangulated-category`: `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`, `CategoryTheory.Pretriangulated`.
- `def-weil-irreducible-components`: `Mathlib/Topology/Irreducible.lean`, `irreducibleComponents`.

For the mixed Tor-amplitude record, the bounded predicate is the existing
`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` from
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, exposed by the recorded
module. Ordinary inverse image, direct image, and open extension by zero are the
recorded six-functor encoding (`Etale.upperStar`, `Etale.lowerStar`,
`Etale.openImmersionLowerShriek`); the module imports the exactness and derived
interfaces. The finite locally constant predicate is
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf` from
`WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets`, already used by the
recorded bounded-constructible and local-constancy dependencies. The module also
imports every available recorded proof-dependency module, with ordinary `import`.
No new node or dependency repair is needed.

Edge cases checked before drafting: X may be empty (`m = 0`, no strata, one zero
object in the tower); X need not be reduced (strata have their reduced structures);
K may be zero; A may be the zero ring; `a = b` permits a single-degree projective
model; all integer shifts, both characteristic zero and positive characteristic,
and algebraically closed fields of arbitrary transcendence degree are permitted.
Pure dimension uses the extended Krull dimension, so the empty X is not assigned
an incorrect natural-number dimension. There is no nonempty hypothesis on X.
Finite index sets do not restrict the index universe of an arbitrary etale cover.
The universe follows the recorded ordinary small-etale encoding: schemes and F
in universe u, coefficient ring and sheaf values in u+1.

Searches performed:

- `msearch.py leanfinder`: "bounded constructible etale complex finite Tor amplitude
  finite smooth stratification locally constant finite projective complexes";
  eight unrelated smoothness and projective-complex hits, no exact statement.
- `msearch.py loogle`: "AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn,
  AlgebraicGeometry.Smooth"; no hits, the project Tor predicate is not indexed.
- `msearch.py grep`: "smooth.*stratif|stratif.*smooth|finite.*projective.*complex"
  in Mathlib/AlgebraicGeometry; zero hits.
- `msearch.py leansearch`: "finite smooth stratification constructible etale
  complexes finite tor dimension"; service returned Internal Server Error,
  recorded as unavailable without drawing a no-match conclusion.
- `rg` in the full upstream WeilConjectures tree and project `lean/Sheaf`:
  "lem-sf-etale-smooth-stratified-ctf|smooth.*stratif|stratif.*smooth";
  no existing declaration of the item. Read the recorded derived coefficients,
  bounded constructibility, Tor amplitude, recollement, exact inverse-image,
  open-extension, dimension, smoothness, irreducible-components, and finite-ring
  local-constancy interfaces before writing.

The local literature checkout lacks the Stacks TeX files, so source statements
were read at the authoritative pages:
[09BI](https://stacks.math.columbia.edu/tag/09BI) for connected local projective models,
[03TT](https://stacks.math.columbia.edu/tag/03TT) for finite Tor complexes,
[0B8X](https://stacks.math.columbia.edu/tag/0B8X) for dense smooth opens,
[095L](https://stacks.math.columbia.edu/tag/095L) for localization, and
[0658](https://stacks.math.columbia.edu/tag/0658) for the prescribed projective interval.
The finite smooth refinement and tower assembly are the nine-step agent argument
recorded by this node, faithfully included in the theorem docstring.

No statement correction or disputed mathematical clause was found.

Validation: `scompile.py Q44 lem-sf-etale-smooth-stratified-ctf` compiled the
module cleanly, with no errors or warnings. The required delivery dry run follows.

The exact proposed declaration name was also searched with `rg` in the upstream
name index, Mathlib, upstream WeilConjectures, and project lean/Sheaf: no collision.


## Second reading by Q44

I independently read the item's full statement and all nine proof steps, the sandbox
module, every statement-dependency node, and the actual declarations supplying its
objects. There is no `statement_change`, new definition node, or dependency-module
repair in this delivery. No mathematical mismatch was found; the Lean module and
node record are unchanged by the second reading.

The source checkout does not contain `literature/stacks-project/`. I therefore read
both the official Stacks tag pages and the actual upstream TeX downloaded into this
sandbox's `scratchpad/`: `etale-cohomology.tex`, `varieties.tex`, and
`more-algebra.tex`. In particular I read `lemma-connected-ctf-locally-constant`
(09BI), `lemma-when-ctf` (03TT), `lemma-ses-associated-to-open` (095L),
`lemma-dense-smooth-open-variety-over-perfect-field` (0B8X), and `lemma-perfect`
(0658), with their surrounding sections and chapter conventions. The hypotheses
Noetherian coefficients, quasi-compact quasi-separated input when needed, and
perfect ground field are consequences of the stated finite ring and separated
finite-type algebraically closed field setting. Reducedness is required on the
strata, not on X. The finite smooth refinement and tower are the node's explicitly
identified agent assembly; they are not misattributed to a single Stacks lemma.

My object/hypothesis/conclusion checklist, in node order:

1. Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
   Exact; there is no finite-field-origin or characteristic assumption.
2. Finite commutative ring A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
   Exact, including the zero ring. No field or nonzero assumption replaces a ring.
3. Separated finite-type F-scheme X: `(X : Scheme.{u})` with
   `[X.Over (Spec (.of F))]`, `IsSeparated`, `LocallyOfFiniteType`, and
   `QuasiCompact` on its structure morphism. Exact. The imported proper-morphism
   module supplies separatedness; the statement does not assume properness.
4. Integers a <= b: `(a b : ℤ) (hab : a ≤ b)`. Exact, with arbitrary integer endpoints.
5. Ordinary small-etale derived object K: `K : DerivedCategoryModule A X`.
   I opened `DerivedCategories` and upstream `Derived.Coefficients`: this is
   `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`,
   not a pro-etale category or an O_X-module category. Exact.
6. Bounded constructibility: `hK : DerivedCategory.isBoundedConstructible A X K`.
   I read `BoundedConstructibleComplexes` and `IsConstructibleEtaleModuleSheaf`.
   The predicate requires constructible cohomology with finite constant module
   values and vanishing outside some bounded interval. It is the recorded
   dependency's predicate, not the upstream variant with a different definition.
   Exact, with no additional stratification assumed as input.
7. Tor amplitude: `hTor : DerivedCategory.hasTorAmplitudeIn A X a b K`.
   I read `EtaleTorAmplitude`, upstream `Derived.Coefficients`, and `Derived.Tensor`.
   This existing predicate quantifies over ALL module sheaves in degree zero and
   asks `IsZero` of tensor cohomology when `q < a ∨ b < q`. It is not merely a
   cohomological bound or a test on finite modules. Exact.
8. Finite family of locally closed subschemes: existential `m : ℕ`,
   `S V : Fin m → Scheme.{u}`, closed `i r : S r ⟶ V r`, and open
   `j r : V r ⟶ X`. The stratum inclusion is `i r ≫ j r`. A closed immersion
   followed by an open immersion is precisely the required locally closed
   immersion; the node also explicitly requests this factorization for shriek.
   Exact; these properties are witnesses, not hypotheses on the input.
9. Reduced, smooth, connected strata: `IsReduced (S r)`, `ConnectedSpace (S r)`,
   and `Smooth (i r ≫ j r ≫ (X ↘ Spec (.of F)))`. I checked the Mathlib
   properties and smoothness declarations, including reduced stalks. The composite
   defines the inherited F-scheme structure. `ConnectedSpace` also says nonempty,
   as customary for parts of a partition; any empty parts can be deleted, so
   there is no lost input case. Exact.
10. Partition: `Set.univ = ⋃ r, Set.range (i r ≫ j r).base` and pairwise
    `Disjoint` ranges for unequal indices. Exact exhaustive, disjoint partition
    of the underlying space; injectivity is supplied by the immersions.
11. Pure dimensions: existential `e : Fin m → ℕ`, with
    `(e r : WithBot ℕ∞) ≤ topologicalKrullDim X` and
    `∀ C ∈ irreducibleComponents (S r), topologicalKrullDim C = e r`.
    I opened Mathlib's `irreducibleComponents` (maximal irreducible subsets)
    and `topologicalKrullDim` (dimension via irreducible closed chains).
    C is given its subspace topology here. Exact, including the dimension bound.
12. Restrictions P_r: existential `P` together with
    `P r = (upperStar (ModuleCat A) (i r ≫ j r)).mapDerivedCategory.obj K`.
    Exact: the equality fixes the objects to the actual inverse images and
    does not assume arbitrary objects or maps in their place.
13. Finite locally constant cohomology: the `∀ r q` conjunct applies
    `Scheme.IsFiniteLocallyConstantSheaf` to `homologyFunctor ... q` of `P r`.
    I read upstream `ConstructibleSheaf.Defs`, where this predicate combines
    an etale local constant trivialization and finitely generated module stalks.
    Since A is finite, this is exactly finite locally constant module cohomology.
    `FiniteLocallyConstantSets` only reexports this predicate; its separate
    set-valued predicate is not used. Exact.
14. Etale local projective models: for each r an existential
    `Scheme.Cover.{u} Scheme.etalePrecoverage (S r)`, then for each member t
    a `CochainComplex (ModuleCat.{u + 1} A) ℤ`. Exact quantifier order: the
    cover and complex are conclusion witnesses, and the model may depend on t.
15. The prescribed support interval: `∀ q, q < a ∨ b < q → IsZero (Q.X q)`.
    Exact, using the original a and b, not a larger model-dependent interval.
16. Finite projective terms: for each q, a finite n and maps from `Q.X q` into
    `ModuleCat.of A (Fin n → A)` and back with `ι ≫ π = 𝟙 (Q.X q)`.
    This is precisely a direct summand of finite free A^n. No finiteness or
    projectivity is assumed in place of the requested explicit conclusion.
17. Representation by CONSTANT complexes: the `Nonempty (... ≅ ...)` compares
    the inverse image of `P r` on the cover member with `DerivedCategory.Q.obj`
    of the termwise `constantSheaf` image of Q. Both terms and differentials
    come from the same A-module complex. Exact; existence of an isomorphism,
    rather than equality of derived objects, is the node's representation claim.
18. Tower: existential `T : Fin (m + 1) → DerivedCategoryModule A X`,
    with `T 0 = K` and `IsZero (T (Fin.last m))`. Exact endpoints and finite length.
19. Successive distinguished triangles: for every `r : Fin m`, maps α, β, δ
    have objects `j_! i_* P r`, `T r.castSucc`, `T r.succ`, and the shift of
    the first by `(1 : ℤ)`; `Triangle.mk α β δ ∈ distTriang ...` imposes the
    distinguished-triangle condition. This is the node's numbering 1 through m
    translated to zero-based `Fin m`. Exact.
20. The specified shriek term: the first object is literally
    `(openImmersionLowerShriek ... (j r)).mapDerivedCategory.obj
      ((lowerStar ... (i r)).mapDerivedCategory.obj (P r))`.
    I read upstream `UpperLowerStar.Defs`, `LowerShriek.OpenImmersion.Defs`,
    `Derived.OpenImmersionLowerShriek`, `SixFunctors.Finite.Exact`, and the
    recorded `OpenClosedRecollement`. These are ordinary etale inverse image,
    exact closed direct image (closed immersions are finite), and ordinary open
    extension by zero. The termwise derived functors therefore say j_! i_*;
    the unbounded ambient category contains the bounded-below localization
    triangles. Exact, without an arbitrary functor substituted for shriek.

Edge cases independently checked: if X is empty, m can be zero, the partition
and stratum clauses are vacuous, and T has one object equal to K and satisfying IsZero (all sheaves and
derived objects on the empty site are zero objects). No nonempty
assumption on X occurs. Nonreduced X is allowed, since only S_r is required to
be reduced and the proof first passes to X_red. The zero K and zero coefficient
ring are allowed. Rank n = 0 represents a zero projective term; a = b permits a
single nonzero degree. All integer degrees and shifts are bound. Positive and
zero characteristic, arbitrary algebraically closed F, and arbitrary universe u
are covered. The coefficient and sheaf universe u+1 is the recorded ordinary
small-etale encoding; no extra universe equality or essentially-small-site
hypothesis was inserted. A finite-type scheme is quasi-compact, so a small
etale trivializing family of the indicated universe suffices; the statement does
not impose a finite number of cover members. Extended dimension handles empty X
without assigning it a spurious natural dimension.

Independent H4 searches (using different phrasing from the worker):

- `msearch.py leanfinder`: `finite stratification into smooth locally closed
  subschemes etale finite projective local model derived category` returned
  eight smooth/etale geometry hits, none stating this result.
- `msearch.py loogle`: `AlgebraicGeometry.Smooth, DerivedCategory` returned no hits.
- `msearch.py leansearch`: `A bounded constructible etale complex of finite tor
  amplitude admits a finite smooth connected stratification with constant
  projective local models` succeeded, returning smoothness lemmas and
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`. I inspected that hit's
  signature: it only gives a bounded representative in an abstract abelian
  category; it gives no smooth strata, constant projective model, or tower.
- `msearch.py grep`: `finite.*stratif|stratif.*finite|constant.*projective`
  returned no hits. Independent `rg` over upstream WeilConjectures, project
  `lean/Sheaf`, Mathlib's algebraic geometry, and `dag/lean_names_upstream.json`
  searched `exists_smooth_stratification_finiteTor`, `smooth.*stratif`,
  `stratif.*smooth`, `projective.*strat`, `strat.*projective`, and
  `locally.*closed.*partition`. Nearby constructibility/partition modules
  do not state the present combined existence theorem. No duplicate was found.

The statement uses the recorded dependency notions; no private definition,
file-local instance, local notation, or new data definition is introduced. Its
only theorem is postponed by `sorry`. Both source/blueprint docstrings are
present; the theorem's nine proof-plan steps match all nine DAG steps, including
the infinite-module stalk Tor test and the final proper/open interchange. I also
matched the available proof-dependency module list against the imports. No
unbound universe or variable is present by inspection. The node's
`lean.statement` is checked against the exact signature in the sandbox file.

Second-reading changes: this independent review section only. No correction of
the statement, dependency interface, Lean signature, or docstrings was needed.


## Immutable maintainer review correction

The independent maintainer review found an H3 edge-case error in the delivered tower
endpoint. For empty X, connected strata force m = 0. The literal equalities
T 0 = K and T (Fin.last m) = 0 then force equality K = 0, although the empty
site gives only that K is a zero object. Derived categories are not skeletal.
The final endpoint is now `IsZero (T (Fin.last m))`, which expresses the
node's categorical zero without identifying arbitrary isomorphic objects.
The first endpoint remains `T 0 = K`. For m > 0 one may still choose the
last object to be the chosen zero; for m = 0, the zero-object property of K
suffices. No mathematical node statement or proof plan changes. The lean.statement
record is regenerated verbatim from the complete corrected module. Earlier claims
that the original endpoint equalities covered empty X are superseded by this correction.

The immutable review record contains the per-file reproduction and corrected-file
compiler evidence. Both original report sections and their clause checklist remain.

Maintainer validation of the complete replacement: `scompile.py Q44
lem-sf-etale-smooth-stratified-ctf
fixes/lean/Sheaf/AlgebraicGeometry/SmoothStratificationFiniteTor.lean`
returned exit 0 and no diagnostics in both the sandbox and library checks
(wrapper times 48.6 s and 12.2 s). The immutable original was also reproduced
with exit 0 and no diagnostics. Pure stage2_delivery validation accepted the
replacement Lean text, lean record, and report; refit_record had no refusals.
