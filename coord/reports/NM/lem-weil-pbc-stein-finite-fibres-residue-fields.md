## Worker report

The module `Sheaf.AlgebraicGeometry.SteinFiniteFibresResidueFields` states
`AlgebraicGeometry.Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields`,
with its sole proof `sorry`. No definition, dependency record, or mathematical
statement was changed. The docstring gives all six proof steps of the DAG node.

Hypothesis and clause correspondence:

- A commutative ring is `{A : Type u} [CommRing A]`; the scheme S is literally
  `Spec (CommRingCat.of A)` and X is `{X : Scheme.{u}}`.
- The proper morphism is `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
  Properness includes the required separatedness, finite type and universal
  closedness (universal closedness supplies quasi-compactness).
- B is the actual global-sections ring `Γ(X, ⊤)`. The canonical second Stein map
  is the dependency's `f.steinFactorizationBase`, whose source is `Spec Γ(X, ⊤)`.
  The canonical first map is `X.toSpecΓ`; it is implicit in this already-defined
  factorization and need not be quantified over as extra data.
- For every s is the explicit binder `(s : Spec (CommRingCat.of A))`.
- Finiteness of the set of points above s is exactly
  `(f.steinFactorizationBase ⁻¹' {s}).Finite`.
- For every b above s is
  `∀ b : Spec Γ(X, ⊤), f.steinFactorizationBase b = s → ...`.
- The finite-dimensional residue extension is
  `(f.steinFactorizationBase.residueFieldMap b).hom.Finite`.
  Mathlib's `RingHom.Finite` is `Module.Finite` for the algebra structure induced
  by this specific homomorphism. Both rings are residue fields, so this is
  precisely finite vector-space dimension. Its source is the residue field at
  `f.steinFactorizationBase b`, equal to s under the preceding condition. No
  arbitrary algebra structure or field embedding is introduced.
- There is no Noetherian hypothesis, nor any nonemptiness or field hypothesis
  on A. The single scheme universe is the universe of Mathlib's scheme category.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `AlgebraicGeometry.Scheme.Hom.steinFactorizationBase` and
  `AlgebraicGeometry.Scheme.toSpecΓ_steinFactorizationBase`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` (the quotient of the stalk map).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `RingHom.toAlgebra`, used through
  `RingHom.Finite` from `Mathlib.RingTheory.Finiteness.Defs`.

The proof imports include `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`
(`Scheme.Hom.steinFactorization_affine`) and the Mathlib modules of the remaining
proof dependencies: scheme fibres, Noetherian schemes, scheme sobriety,
Noetherian components, closed-point existence, integral incomparability, proper
base-change permanence and Zariski's lemma. Existing declarations are reused.

Source check: read the lemma and proof of Tag 0E0M in
`literature/stacks-project/more-morphisms.tex`, label
`lemma-stein-universally-closed-residue-fields`. Its universally closed,
quasi-separated, locally finite-type setting includes the proper specialization
in this node. The node does not assert finiteness of the Stein morphism itself.

Edge cases checked: the empty X has zero global-sections ring and empty spectrum,
so both conclusions hold; an empty fibre requires no residue extension. The zero
base ring gives an empty base and no s to instantiate. A non-Noetherian A is
permitted: only the geometric fibre over its residue field needs Noetherianity.
Identity maps and finite morphisms give the expected finite fibres and finite
residue degrees. No degree-positive condition accidentally excludes degree one.

Searches for an existing statement (msearch.py, group NM and this item):

- LeanFinder: `For a proper scheme over an affine ring the Stein factor has finite
  fibres and finite residue field extensions`. Eight hits, including
  `instFiniteCarrierCarrierCommRingCatFiberOfIsFinite`,
  `finite_appTop_of_universallyClosed`, `IsFinite.SpecMap_iff`,
  `IsFinite.iff_isProper_and_isAffineHom`, and quasi-finite algebra results.
  None gives this theorem without assuming finiteness of the Stein map or
  integrality of X over a field.
- Loogle: `"steinFactorizationBase"`. Zero hits.
- Mathlib grep: `steinFactorization|finite.*residueFieldMap`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `Stein factorization of a proper morphism has finite fibres and
  finite residue field extensions`. Service unavailable (Internal Server Error).
- Direct rg in upstream WeilConjectures and project lean/Sheaf for `stein|Stein`,
  then `lem-weil-pbc-stein-finite-fibres-residue-fields|steinFactorization.*(finite|Finite)|finite.*steinFactorization`.
  The upstream `isFinite_steinFactorizationBase` assumes A Noetherian; project
  `steinFactorization_affine` establishes integrality and connected fibres,
  not the two conclusions of this item. The item id has no existing declaration.
- Read `RingHom.Finite` and the full signatures/docstrings of the six statement
  dependencies to verify the map and scalar structure, rather than using a
  same-named but different field extension.

Validation: scompile.py compiled the delivered module cleanly on the server
in 1.3 seconds, nice 19, two threads, the default 60-second per-file limit.
No warnings or errors. No local compilation was run. No statement dispute or
node fault was found. The independent second reading remains for the next worker.

## Second reading by NM

Independently read the node and all six statement-dependency records, then opened
 their actual declarations in Mathlib and upstream (Scheme, Spec/Spec.map,
IsProper, steinFactorizationBase and its factorization identity, residueField and
residueFieldMap, Algebra and RingHom.Finite). Read Stacks more-morphisms.tex,
Tag 0E0M and its preceding lemma `lemma-stein-universally-closed` (03GY).
The source assumes universally closed and quasi-separated, and adds locally
finite type; properness supplies these in this node's stated specialization.
No correction of the mathematical statement is needed.

Object/hypothesis/conclusion checklist, with verdicts:

- Commutative ring A: `{A : Type u} [CommRing A]`. Exact; no field, reducedness,
  characteristic, or Noetherian hypothesis added.
- Scheme X and affine base S: `{X : Scheme.{u}}` and
  `Spec (CommRingCat.of A)`. Exact use of the dependency's scheme and spectrum.
- Proper structure morphism f: `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
  Exact: IsProper extends separated, universally closed, locally finite type;
  universally closed also supplies quasi-compactness, hence finite type.
- B equals the actual global sections, not an auxiliary algebra:
  `Γ(X, ⊤)` in `Spec Γ(X, ⊤)`. Exact.
- Canonical factorization q and pi: q is `X.toSpecΓ` and pi is
  `f.steinFactorizationBase`. The opened definition is
  `Spec.map ((Scheme.ΓSpecIso _).inv ≫ f.appTop)` and the opened identity
  `Scheme.toSpecΓ_steinFactorizationBase` says q followed by pi is f.
  Exact; no extra factorization, surjectivity, or finiteness assumption.
- Every base point s: `(s : Spec (CommRingCat.of A))`. Exact universal binder.
- Finite point fibre: `(f.steinFactorizationBase ⁻¹' {s}).Finite`. Exact set of
  points, with no assertion that the intermediate morphism is finite.
- Each b above s: `∀ b : Spec Γ(X, ⊤), f.steinFactorizationBase b = s →`.
  Exact order and restriction to the same point fibre.
- Finite-dimensional residue extension:
  `(f.steinFactorizationBase.residueFieldMap b).hom.Finite`. Exact:
  residueFieldMap is induced by the stalk map and has source κ(pi(b)), target
  κ(b); under the preceding equality its source is κ(s). RingHom.Finite is
  Module.Finite for this homomorphism's toAlgebra, which over fields is finite
  vector-space dimension. An explicit transport along the equality would give
  the equivalent κ(s)-form and is unnecessary.

Edge cases: empty X gives empty Spec of its zero global-sections ring; empty
point fibres satisfy finiteness and make the second clause vacuous. The zero
base ring has empty spectrum, hence no s. Non-Noetherian A, every characteristic,
and residue degree one are included. There is no index or integer parameter.
Universe u is explicitly bound and arbitrary; A and X use the common universe
of the ambient Scheme category, as do the recorded canonical construction and
Spec. No equality between independent universes or small test category is
assumed. Every variable in the signature is bound.

Independent searches (msearch.py with NM and this item, plus direct rg):

- LeanFinder: `For a proper scheme over Spec A, primes of its global functions
  above a base prime are finite with finite residue degree`. Eight hits: finite
  morphism fibres, finite_appTop_of_universallyClosed, and quasi-finite algebra
  facts. None is this non-Noetherian Stein-factor theorem.
- Loogle: `"residueFieldMap", "Finite"`. One hit,
  RingHom.EssFiniteType.residueFieldMap, about essential finite type rather than
  this finiteness statement.
- Direct rg in project lean/Sheaf and upstream WeilConjectures:
  `steinFactorization|finite.*residueFieldMap|residueFieldMap.*[Ff]inite`;
  direct Mathlib rg for `finite_preimage_singleton`,
  `finite_appTop_of_universallyClosed`, and `steinFactorization`.
  Opened upstream isFinite_steinFactorizationBase: it needs IsNoetherianRing A.
  Opened upstream finite_residueFieldMap: it needs FormallyUnramified and
  LocallyOfFiniteType. Neither matches. Project SteinFactorizationAffine gives
  integral pi and proper/geometrically connected q, not these conclusions.
  No duplicate statement was found. The worker's LeanSearch unavailability is
  recorded above; the independent successful searches and rg agree.

Read the imported SteinFactorizationAffine signature for the proof's integrality,
properness and nonempty fibres. All six node proof steps occur in the theorem's
source/blueprint docstring, including the empty-component case, closed-point
selection, and compatible residue-field tower. There are no new definition
nodes, dependency repairs, hollow definitions, extra declarations, or proofs
besides the required sorry. No mismatch found; no Lean or node changes made.
The only change is this independent reading report.

Validation: scompile.py compiled the only delivered file on the server cleanly
in 1.3 seconds, nice 19, two threads, limit 60 seconds. No warnings or errors.
Compared lean.statement with the file signature verbatim: equal. Maximum line
length in the Lean file is 95 characters.
