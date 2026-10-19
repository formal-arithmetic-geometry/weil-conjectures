## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFlatCdEtaleExchange` states
`AlgebraicGeometry.finite_flat_cd_etale_exchange`, with its sole proof `sorry`.
The node statement is unchanged. No definitions, dependency modules or new nodes were needed.

Source read: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé II, the exchange assertion in
the proof of Theorem 3.2.3, printed pp. 30–31 (PDF pp. 36–37), and Corollary 2.2.4,
printed p. 27 (PDF p. 33). The printed `Z_j → W_j` in that assertion refers to the
neighbourhood `U_j`. The source's henselian-component argument applies to arbitrary
Noetherian schemes and finite locally free maps of constant rank, as expanded by the
node's seven proof steps. The theorem docstring includes all seven steps and their
named dependencies. In particular it preserves the residue-field lift to the chosen
henselian factor, the descended idempotent and section, constant-rank descent,
finite-type neighbourhood refinement, and the completely decomposed finite-subcover step.

Hypothesis-by-hypothesis correspondence:

- `X Y : Scheme.{u}` and `f : Y ⟶ X` are the two schemes and their morphism.
- `[IsNoetherian X]` means exactly the node's finite affine cover by Noetherian rings:
  Mathlib `isNoetherian_iff_of_finite_iSup_eq_top` identifies this class with that cover
  condition. `IsNoetherian` extends local Noetherianity and compactness; it is not merely
  local Noetherianity.
- `ell : ℕ`, `hell : ell.Prime` render the prime. No invertibility hypothesis is added.
- `d : ℕ`, `hf : f.IsFiniteLocallyFreeOfDegree d`, `hd : 0 < d`, and
  `hcoprime : Nat.Coprime d ell` give finite local freeness, constant positive rank,
  and rank prime to `ell`. The recorded upstream degree class extends finite local
  freeness and fixes the degree of every fibre, including nonreduced fibres.
- `{I : Type w} [Finite I]`, `V : I → Scheme.{u}`, and `v : ∀ i, V i ⟶ Y` encode
  an arbitrary finite family without choosing an enumeration or excluding an empty index.
- `hv` gives, for every input arrow, `IsSeparated`, `Etale`, `LocallyOfFiniteType`, and
  `QuasiCompact`. The final pair is exactly the recorded meaning of finite type.
- `hcd` quantifies over every point of `Y` and produces an index and a point above it,
  with equality of its image and `IsIso ((v i).residueFieldMap z)`. This is the induced
  residue-field map, not an arbitrary isomorphism between abstract fields.

Conclusion clause-by-clause correspondence:

- `∃ (n : ℕ) (U Z : Fin n → Scheme.{u})` is a finite family of output schemes; `u`,
  `c`, `r`, `index`, and `g` are the requested arrows, constant ranks, original indices,
  and factorization arrows. A finite family can be enumerated by `Fin n`.
- The first conjunct gives separated, étale, locally finite type and quasi-compact
  `u j : U j ⟶ X`, hence separated étale finite-type maps.
- The second conjunct gives complete decomposition over every point of `X` using the
  induced residue-field map of `u j`.
- The third conjunct gives `(c j).IsFiniteLocallyFreeOfDegree (r j)`, `Surjective (c j)`,
  `0 < r j`, and `Nat.Coprime (r j) ell`, exactly all requirements on `c_j` and `d_j`.
- The final conjunct `g j ≫ v (index j) ≫ f = c j ≫ u j` is
  `f v_{i(j)} g_j = u_j c_j` in Lean's left-to-right composition convention.
  With the structural maps to `X` given by these composites it states that `g_j` is over `X`.
- There is no integrality or reducedness condition on `U`, `Z`, `X`, or `Y`.

Recorded statement dependencies used (signatures and docstrings inspected):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; applied through `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsNoetherian` and its finite-affine-cover characterization.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`, extending
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record with no declaration;
  its separation convention is `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  `AlgebraicGeometry.IsSeparated`, and its other used conventions are those above.

Imports without `public` carry the recorded, already stated proof dependencies, including
finite locally free structure sheaves, finite henselian products, local freeness,
henselian retractions, finite-data descent, affine limits, spreading out, finite-free
spectra and finite locally free descent. Mathlib proof tools for étale base change and
finite-presentation stability are also imported. The two proof-only nodes
`lem-per-ordinary-henselian-pointed-neighbourhood-limit` and
`lem-per-completely-decomposed-etale-finite-subcover` have no recorded module in the read
DAG; their imports can be added by the maintainer when stated. They are not required to
form this theorem's signature, and no substitute theorem is introduced.

Edge cases checked:

- Empty `X`: the empty `Fin 0` output family satisfies the conclusion. No nonempty output
  index is required. On an empty target the degree condition is vacuous, as it should be.
- Empty input family: `hcd` forces `Y` empty; positive-rank finite local freeness forces
  `X` empty. The same empty output works.
- Rank zero is explicitly excluded by `hd` and the output positivity clauses. Rank one
  and `ell = 2` are included. `ell = 0` or `ell = 1` cannot satisfy primality.
- No restriction on the characteristic or on invertibility of `ell` is present.
- Nonreduced and disconnected schemes are included; rank is fibre algebra dimension,
  not the number of geometric points. Output ranks may vary between indices.
- Input indices have their own explicitly bound universe `w`; all schemes share an
  arbitrary explicitly bound universe `u`, and the finite output indices add no size
  assumption on them. `set_option autoImplicit false` is used.

Searches made for an existing statement or definition:

- `msearch.py` LeanFinder query: “Finite flat cover of prime to ell degree and completely
  decomposed etale family can be exchanged downstairs”. Eight hits, concerning étale
  algebra idempotents, base change, factorization rings, descent and composition; none
  states the exchange result.
- `msearch.py` Loogle query:
  `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
  Zero hits; the upstream degree name is not in Loogle's Mathlib index.
- `msearch.py` grep query: `Nisnevich|completely.decomposed|finite.flat.*exchange`,
  restricted to Mathlib `AlgebraicGeometry`: zero hits.
- `msearch.py` LeanSearch query: “Exchange finite locally free morphism prime to ell and
  completely decomposed etale family”. Eight hits on étaleness, étale-over categories,
  unramifiedness, and field extensions; no exchange statement.
- `rg` in upstream `WeilConjectures` for the item id and for complete decomposition and
  exchange names: no statement match. The finite locally free classes were found and read
  in `Morphisms/FiberDegree.lean`, lines 778–792.
- `rg` in project `lean/Sheaf` for complete decomposition found the alteration topology
  and standard-form modules. The former's predicate is on reduced objects in `alt/S`, so
  it does not apply to this arbitrary-scheme statement. The latter already expresses
  complete decomposition pointwise with the same induced residue-field map; that encoding
  is used here, without defining a second predicate. Neither module states this exchange.
- Exact proposed declaration and module names were searched in project Lean, upstream
  Lean and `dag/lean_names_upstream.json`; no collision was found.

Validation: `scompile.py N5 lem-per-finite-flat-cd-etale-exchange` compiled the delivered
file both as a sandbox module and under its library module name, with no errors or warnings.
No statement dispute, statement correction or unusable dependency was found.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
