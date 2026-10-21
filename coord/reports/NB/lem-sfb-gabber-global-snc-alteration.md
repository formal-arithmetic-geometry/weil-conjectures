## Worker report

The module `Sheaf.AlgebraicGeometry.GabberGlobalSNCAlteration` states
`AlgebraicGeometry.exists_gabber_global_snc_alteration`, with `sorry` as its only proof.
There are no definitions, additional theorem obligations, new nodes, dependency repairs,
or statement corrections. The node changes only `lean` and adds the already landed
`def-sc-quasi-projective` and `def-trf-strict-normal-crossings-divisor` to `stmt_deps`.
These supply existing notions that the original statement describes in words.

Source read: ILO, Travaux de Gabber, Expose X, printed pp. 148--152: the definition of an
ell-prime alteration, Theorem 2.1, its following relative-SNC definition, and proof 2.3
Steps 1--3. The complete eight-step DAG proof is reproduced in the theorem docstring,
including the good-component selection, graph argument for projectivity, and return
to the original open subscheme. The source's geometric conditions agree with the node.

### Each hypothesis and conclusion clause

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary field k | `(k : Type u) [Field k]` |
| Prime ell different from char(k) | `(ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hchar : ℓ ≠ ringChar k)` |
| k-scheme X | `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))` |
| Separated | `[IsSeparated f]` |
| Finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded finite-type convention |
| Nowhere dense closed subset Z | `(Z : Set X) (hZ : IsClosed Z) (hZnd : interior Z = ∅)`; closedness makes this equivalent to empty interior of the closure |
| Finite field extension k'/k | `∃ (K : Type u) (_ : Field K) (i : k →+* K), i.Finite ∧ ...`; a field homomorphism is injective, and `i.Finite` is finiteness for its canonical scalar action |
| Extension degree prime to ell | `Nat.Coprime (@Module.finrank k K _ _ i.toAlgebra.toModule) ℓ` |
| Scheme P over k' | `∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of K)) ...` |
| Smooth | `Smooth p` |
| Quasi-projective, locally closed immersion in finite projective space | `IsQuasiProjective p`; the upstream definition quantifies over a finite coordinate type and an `IsImmersion` over `Spec K` |
| Proper, projective, surjective alteration a | `(a : P ⟶ X)` and `IsProper a ∧ IsProjectiveBundle a ∧ Surjective a`; projectivity uses the node's projective-bundle convention |
| Compatibility with Spec(k') to Spec(k) | `a ≫ f = p ≫ Spec.map (CommRingCat.ofHom i)` |
| Every component generic point maps to a component generic point | `∀ (C : Set P), C ∈ irreducibleComponents P → ∀ η : P, IsGenericPoint η C → (∃ B ∈ irreducibleComponents X, IsGenericPoint (a η) B) ∧ ...` |
| Finite induced residue extension at each such generic point | `(a.residueFieldMap η).hom.Finite` |
| Every such degree is prime to ell | `Nat.Coprime (@Module.finrank (X.residueField (a η)) (P.residueField η) _ _ (a.residueFieldMap η).hom.toAlgebra.toModule) ℓ` |
| Reduced inverse image of Z | `∃ D : P.IdealSheafData, D = ((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).comap a).radical ∧ ...`; D is determined by this equality |
| Relative strict normal crossings | `D.IsStrictNormalCrossingsDivisor p` |
| Finitely many distinct irreducible components | That predicate supplies `n : ℕ`, `C : Fin n → P.IdealSheafData`, injective component supports, integral component schemes, and union of supports equal to D's support |
| Each component smooth of codimension one | The same predicate for singleton finite subsets: `Smooth ((⨆ i ∈ s, C i).subschemeι ≫ p)` and ambient stalk dimension equals intersection stalk dimension plus `s.card = 1` |
| Every intersection smooth of codimension its number of components | The predicate quantifies over every `s : Finset (Fin n)` and all points of the scheme cut out by the sum of the component ideals, with the same dimension formula |
| Local equations are distinct regular parameters | At every `x : P`, an affine neighborhood `U`, stalk Noetherianity `hR`, regular system `t`, and a `s.Sublist t` with `s.Nodup`, whose product generates the stalk ideal of D |
| Local equation is the actual boundary ideal | `(D.ideal U).map (P.presheaf.germ U.1 x hx).hom = Ideal.span {s.prod}` |
| Regular-scheme SNC boundary | `IsStrictNormalCrossingsBoundary D ∧ IsRegularScheme P` |
| Empty schemes, boundaries and intersections allowed | No nonempty or connectedness hypothesis. Finite component families and the parameter sublist may be empty. The relative SNC predicate includes the empty subset and vacuous pointwise codimension conditions for empty intersections. |

The local product equation is precisely the component equation assertion, without a new
local-chart definition: the entries of a regular system are prime parameters, and the
nodup sublist gives distinct local prime factors. The relative SNC components are integral
and smooth, hence their stalks through x are domains. Their local prime ideals are exactly
these parameter ideals. Conversely component parameter equations give this product ideal
because D is the reduced Cartier union. Thus no etale neighborhood, arbitrary replacement
map, or weaker set-theoretic boundary equation is substituted for the stated local condition.

### Dependency declarations read and used

All original statement-dependency nodes, their Lean/mathlib records, and the recorded
signatures and docstrings were read. The modules are read from the live read-only checkout.

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs` (line 180).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (line 43), and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  (line 43). Both classes express the finite-type hypothesis.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (line 42), with the recorded
  `IsSeparated` and `UniversallyClosed` signatures in their owning Mathlib modules.
- `def-pc-field-extension`: the ring map `i`, equivalently its `RingHom.toAlgebra`,
  using Mathlib `Algebra` in `Mathlib.Algebra.Algebra.Defs` (line 95).
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (line 62).
- `def-trf-projective-bundle-morphism`: `AlgebraicGeometry.IsProjectiveBundle`,
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, read in full. It uses an actual
  quasi-coherent finite-type module and closed immersion into its canonical projective bundle.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (line 59).
- `def-weil-irreducible-components`: the recorded Mathlib match `irreducibleComponents`,
  `Mathlib.Topology.Irreducible` (line 107), maximal irreducible subsets.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober` (line 39),
  equality of singleton closure with the given component.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField` (lines 48 and 123).
- `def-weil-pbc-regular-system-of-parameters`:
  `IsLocalRing.IsRegularSystemOfParameters`,
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, read in full.
- `def-trf-strict-normal-crossings-boundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`,
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, read in full.
- `def-weil-regular-scheme`: `AlgebraicGeometry.IsRegularScheme`,
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, read in full: local Noetherianity AND
  stalkwise regularity, not just regularity of individual rings.
- Added landed `def-sc-quasi-projective`: `AlgebraicGeometry.IsQuasiProjective`,
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective` (line 48).
- Added landed `def-trf-strict-normal-crossings-divisor`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsStrictNormalCrossingsDivisor`,
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor`, read in full.

Proof-only imports include the recorded projectivity, relative projective space,
ample-module, finite-projective-bundle, H-projective composition and conversion modules,
as well as Mathlib closed-immersion base change, etale composition, surjective base change
and Sylow. The four new geometric proof nodes (proper-pair preparation, equivariant model,
Sylow good components and tame quotient resolution) have no Lean declarations yet and
therefore no import. Their absence does not affect this statement's objects; their full
intended uses are in the proof docstring. No consumer module is changed in the read-only clone.

### Edge cases

- Empty X: take K=k of degree one and P empty. Generic-point and stalk conditions are
  vacuous; the empty Cartier divisor is represented by the unit ideal.
- Empty Z with nonempty X: D is the unit ideal. The relative predicate permits `n=0`.
  At any stalk choose `s=[]`, with product one, and any regular parameter system t.
- Dimension-zero components of P: t and s may both be empty; a nowhere dense Z has
  no such component generically in its preimage.
- Empty intersections: smoothness of the empty scheme is allowed and the codimension
  equation has no points at which to be tested.
- Empty index subset of the components: the ideal sum is bottom and its subscheme is P;
  the smoothness assertion is `Smooth p` and the dimension equation has increment zero.
- Characteristic zero: `ringChar k=0` and every prime is allowed. No positive-characteristic
  or perfectness assumption is added. In positive characteristic only the given prime is excluded.
- Disconnected or nonreduced X: no integrality or reducedness hypothesis is imposed. Every
  component of P is tested separately, rather than taking a total generic degree.
- Finiteness is explicit for i and every generic residue map: the convention that `finrank`
  is zero for an infinite extension cannot accidentally make the degree assertion vacuous.
- All ambient fields and schemes are in the explicit universe u, consistent with the recorded
  geometry APIs. A finite field extension of k has a representative in this same universe.
  `set_option autoImplicit false` prevents any silently introduced variable or universe.

### Searches made

- `msearch.py ... leanfinder` query: "Gabber prime to ell projective alteration with smooth
  quasi-projective source and relative strict normal crossings boundary". Eight results:
  smooth and standard-smooth morphism definitions/chart results and Proj valuative existence;
  none states the alteration theorem.
- `msearch.py ... loogle` query: `"IsSmooth", "IsProper"`. Zero hits.
- `msearch.py ... grep` query: `Gabber|alteration|normalCrossing|normal_crossing`.
  Three Mathlib hits, all bibliographic mentions of Beilinson--Bernstein--Deligne--Gabber
  in triangulated t-structure files. No alteration theorem or SNC predicate.
- `msearch.py ... leansearch` query: "Prime to ell alterations resolving a variety with relative
  strict normal crossings boundary". Eight hits on etale loci, normalization, ramification,
  and base-change stability; none states the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `Relative.*[Nn]ormal|[Nn]ormalCrossings|[Qq]uasiProjective|[Qq]uasi[Pp]rojective|[Gg]abber`
  found existing relative SNC and quasi-projectivity interfaces, reused here. Narrow searches
  for the item id and theorem name found only proof-plan citations in NestedOpenRegularAlteration,
  with no existing statement of this item. No new definition is needed.
- DAG search for `def-trf-strict-normal-crossings-divisor` and quasi-projective locally closed
  immersions located the two landed definition nodes added to statement dependencies.

Validation: prescribed `scompile.py NB lem-sfb-gabber-global-snc-alteration <file>` compiled
both sandbox and library-name modes cleanly, most recently in 3.0 s and 4.3 s. An initial
style warning about an extra newline before the docstring terminator was repaired; the final
file has no warnings. The only theorem proof is `sorry`, as required for stage 2.

## Second reading by NB

This is a dispatcher-started single-worker delivery; no additional agent was started, as the
brief forbids it. This section records a second pass by the same worker; the maintainer supplies
the independent review.

With the final node and Lean file open, I checked every row above against the exact signature.
The result retains arbitrary separated finite-type X (not only integral X), uses the
projective-bundle predicate requested by the node, and quantifies at EACH component generic
point with the actual induced scalar action. The relative-SNC predicate already gives the
finite component/intersection clauses; its empty finite subset supplies smoothness of P.
The additional regular-scheme predicate includes local Noetherianity. The local formula uses
actual stalk ideals and no etale substitution. On this pass I made distinctness of the local
parameter factors explicit with `s.Nodup`; that is already forced for a sublist of a regular
parameter system, and directly renders the node's word "distinct". I also ensured every
available proof-dependency module, including Mathlib leaves, has a proof-only import.
No mismatch, disputed statement, or dependency-interface defect remains.
