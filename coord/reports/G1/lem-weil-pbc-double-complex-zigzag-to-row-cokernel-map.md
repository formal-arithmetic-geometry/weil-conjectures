## Worker report

The module `Sheaf.Algebra.Homology.ZigzagToRowCokernel` states
`HomologicalComplex₂.exists_zigzagToRowCokernel`, with its only proof `sorry`.
There are no new definitions, additional nodes, dependency replacements, or statement
corrections. The source was read at https://stacks.math.columbia.edu/tag/00M1,
including the canonical endpoint homomorphism and the right square of the
functoriality diagram; the local `literature/stacks-project/algebra.tex` is absent
on this machine. The sign convention is the supplied node's plus-sign boundary
convention, already implemented by the zig-zag dependency.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`. Both `u` and the independent
  module universe `v` are explicitly declared. No characteristic, exactness,
  finite generation, or boundedness hypotheses are imposed.
- A first-quadrant homological double complex is
  `A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)`. The same type is used for `B`. Its outer differential
  `(A.d p p').f q` is horizontal `d`, and its inner differential `(A.X p).d q q'`
  is vertical `δ`. The structure already imposes both square-zero identities,
  commuting squares, and zero maps outside the shape. The `ℕ` indexing describes
  the stated zero extension in negative degrees, without adding negative data.
- A morphism is `Φ : A ⟶ B`. Its component `(Φ.f p).f q` is `Φₚ,ᵩ`;
  the two levels of the chain-morphism structure impose precisely the two
  commutation equations.
- The row-cokernel chain complex is the local abbreviation `C A := A.opcycles 0`.
  This applies Mathlib's existing opcycles construction to the OUTER complex in
  the category `ChainComplex (ModuleCat R) ℕ`, rather than to an individual column.
  `ComplexShape.down ℕ` has `prev 0 = 1`, so
  `HomologicalComplex.opcyclesIsCokernel` identifies it with the cokernel of
  `A.d 1 0 : A.X 1 ⟶ A.X 0`. Evaluation preserves cokernels, as recorded by the
  instances in `Mathlib.Algebra.Homology.HomologicalComplexLimits`, so its degree
  `q` is exactly the categorical cokernel of `(A.d 1 0).f q`. Categorical cokernels
  of module maps are their range quotients, not a different notion.
- The projection is `π A := A.pOpcycles 0`; `((π A).f q)` is `π_q`.
  The first conjunction states surjectivity and
  `LinearMap.ker ((π A).f q).hom = LinearMap.range ((A.d 1 0).f q).hom`.
  Together these also express its ordinary module cokernel universal property.
- The induced differential is `(C A).d (q+1) q`; the second conjunction states
  `(A.X 0).d (q+1) q ≫ (π A).f q = (π A).f (q+1) ≫ (C A).d (q+1) q`,
  which is exactly `δʳᵗ π = π δ`. Since `C A` is already a chain complex,
  square-zero and the degree-zero zero differential are part of its structure.
- The induced row-cokernel morphism is `HomologicalComplex.opcyclesMap Φ 0`, an
  actual chain-complex morphism. The third conjunction states its component
  equation `(π A).f q ≫ (opcyclesMap Φ 0).f q = (Φ.f 0).f q ≫ (π B).f q`.
  Thus its component is uniquely the map induced on the cokernel by `Φ₀,ᵩ`.
- The degree is `(n : ℕ)`; hence every nonnegative integer degree is covered.
  `T_n`, `Z_n`, `B_n`, and `𝐇_n` are the imported `zigzagTotal`, `zigzagCycles`,
  `zigzagBoundaries`, and `zigzagModule`. The endpoint projection `e A` is the
  existing `DirectSum.component` at `⟨(0,n), by simp⟩`. It is only a local
  abbreviation for that map, not a new definition of any module.
- Clause (a) is the fourth conjunction: for `a : zigzagCycles A n`, the projected
  endpoint has zero differential, and there exists `c : (C A).cycles n` whose
  image under `iCycles` is that endpoint. The latter makes the identification
  with Mathlib's abstract cycle object explicit. At `n=0`, `d 0 (0-1) = d 0 0`
  is zero by the complex shape; this is the node's alternative `n=0`.
- Clause (b) is the fifth conjunction: if `a.val ∈ zigzagBoundaries A n`, every
  cycle `c` representing the projected endpoint has `(C A).homologyπ n c = 0`.
  Since `a` already belongs to `zigzagCycles`, this is exactly the intersection
  `Z_n ∩ B_n`. Clause (a) supplies existence of `c`, and `iCycles` is mono,
  so this formulation is neither vacuous nor dependent on a choice of lift.
- The induced linear map is the existential family
  `ρ : ∀ A, zigzagModule A n →ₗ[R] (C A).homology n`. The sixth conjunction
  gives its value on every quotient representative using the dependency's
  quotient map `((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ`:
  `ρ A [a] = (C A).homologyπ n c` whenever `iCycles c = π_n(a₀,ₙ)`.
  This specifies the canonical map uniquely because the quotient map is
  surjective. The existential asserts the induced map's existence; its
  representative formula is included, rather than asserting bare existence.
  The family over all `A` just expresses the maps `ρ⁽ᴬ⁾_n` of the node together
  so the naturality equation can be stated for the same maps.
- Clause (c) is the seventh conjunction:
  `(homologyMap (opcyclesMap Φ 0) n).hom.comp (ρ A) =
  (ρ B).comp (zigzagMap Φ n)`. `ModuleCat.Hom.hom` is written explicitly to
  extract the linear map from the categorical homology morphism. This is the
  stated equality `H_n(Φʳᵗ) ∘ ρ⁽ᴬ⁾_n = ρ⁽ᴮ⁾_n ∘ 𝐇_n(Φ)`.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.ZigzagModule`: `HomologicalComplex₂.ZigzagIndex`,
  `zigzagTotal`, `zigzagCycles`, `zigzagBoundaries`, `zigzagModule`, and `zigzagMap`.
  The complete file and its docstrings were read. Its plus-sign boundary agrees
  with this item's statement, and its quotient is by the intersection as required.
- `def-weil-pbc-module-chain-complex-homology` is a Mathlib leaf with no `lean`
  record. Its recorded match was read:
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.homology`, `homologyMap`, `cycles`, `iCycles`, and `homologyπ`.
  The full signatures and docstrings of these declarations were inspected.
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` was also read to verify the
  `moduleCatHomologyIso` quotient interpretation. Using a nonnegative complex
  rather than explicitly adjoining zero negative terms is the specialization
  expressly allowed by the dependency node's statement.
- The dependency's underlying double-complex Mathlib match was also inspected:
  `Mathlib.Algebra.Homology.HomologicalBicomplex`, `HomologicalComplex₂`;
  `HomologicalComplex.Hom` and `ChainComplex` in `HomologicalComplex.lean`.
- Existing auxiliary Mathlib API: `HomologicalComplex.opcycles`, `pOpcycles`,
  `opcyclesIsCokernel`, `opcyclesMap`, and `p_opcyclesMap` in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`; the abelian instance
  for chain complexes in `HomologicalComplexAbelian`; the abelian instance for
  module categories in `ModuleCat.Abelian`. The two latter modules are used for
  synthesis of the homology objects in the category of chain complexes.

Edge cases checked before writing: `n=0` has no zig-zag equations and its outgoing
row-cokernel differential is zero; boundaries at `n=0` are still killed by the
homology class map. Zero modules and the zero ring work with exactly the same
kernel and quotient statements. Nonzero horizontal images and nonexact rows or
columns are allowed: the projected endpoint is a cycle using only the last
zig-zag relation, and its trivial-boundary class is zero using only the defining
plus-sign formula. Different module universes are permitted by independent `u,v`.
The endpoint exists even at degree zero; no empty or negative diagonal is used.
Identity and zero morphisms are included in the quantification in (c).

Searches for an existing statement (all through the prescribed launcher where applicable):

- LeanFinder via `msearch.py`: query "canonical map from double complex zigzag
  quotient to homology of row cokernel complex". Eight hits, including
  `HomologicalComplex.descOpcycles`, `fromOpcycles`, `pOpcycles`, `homologyι`,
  `homologyIsCokernel`, and `opcyclesToCycles`; none state this zig-zag lemma.
  These hits led to reusing the existing outer-opcycles construction.
- Loogle via `msearch.py`: `HomologicalComplex₂, cokernel`; zero hits, unknown
  identifier `cokernel` in the service's query environment.
- LeanSearch via `msearch.py`: "canonical homomorphism from zigzags of double
  complex to homology of cokernel complex"; unavailable (Internal Server Error).
  This is recorded as an unavailable search, without a mathematical verdict.
- Mathlib grep via `msearch.py`: `zigzag|rowCokernel|no-spectral-sequence` in
  `Algebra/Homology`; one unrelated `zigzag_isConnected` hit in LocalCohomology.
- `rg` of `zigzag|rowCokernel|00M1` in the read-only `WeilConjectures` source:
  monoidal zig-zag identities and categorical connectedness only, no such map.
  `grep -rn` of the item id in that source returned no matches.
- `rg` of `zigzag|rowCokernel|00M1` in repository `lean/Sheaf`: the recorded
  ZigzagModule dependency and unrelated homotopy/derived tensor references only.
  No row-cokernel endpoint lemma exists there.
- `rg` of `zigzagToRowCokernel` in `dag/lean_names_upstream.json`: no match.

No `STATEMENT-DISPUTED` issue was found. The module docstring supplies all five
proof steps from the node, naming the two definition dependencies. Compilation
is performed only by `scompile.py` on the server, never locally.

## Second reading by G1

I independently read the node statement and `ZigzagToRowCokernel.lean` clause by
clause. The ring hypothesis is rendered by `{R : Type u} [CommRing R]`; the
independent module universe is `v`, so no universe restriction is added. The
double complexes `A` and `B` are exactly
`HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
(ComplexShape.down ℕ)`, which supplies the first-quadrant modules, both
differentials, square-zero laws, commuting squares, and zero boundary maps.
The morphism hypothesis is `Φ : A ⟶ B`, whose two chain-morphism structures are
the two equations `Φ d = d Φ` and `Φ δ = δ Φ`. No exactness, finiteness,
Noetherian, characteristic, or boundedness hypothesis appears.

The local abbreviations `C := A.opcycles 0`, `π := A.pOpcycles 0`, and `e :=`
the `(0,n)` `DirectSum.component` render respectively the row-cokernel complex,
its projections, and the endpoint `a_{0,n}`. The first conjunction records the
surjection and kernel/image characterization of each cokernel projection; the
second records `δʳᵗ π = π δ`; and the third records the induced morphism formula
for `opcyclesMap Φ 0`. These are the construction facts stated in the node,
with no alternate cokernel notion introduced.

Clause (a) is the fourth conjunction: the endpoint projection has zero outgoing
differential and is represented by an abstract cycle. It covers `n = 0` because
the `ComplexShape.down ℕ` differential at degree zero is zero. Clause (b) is the
fifth conjunction: every cycle representing an endpoint of a zig-zag boundary
has zero homology class; together with (a), this is exactly vanishing on
`Z_n ∩ B_n`. The sixth conjunction gives the induced linear map on the quotient,
with its representative formula. Clause (c) is the final conjunction, the
equality of the induced homology map after `opcyclesMap` with the map induced by
`zigzagMap`. Quantifiers over all complexes and all morphisms are in the same
order as the node's naturality claim.

Edge cases remain covered: empty diagonals do not occur for `n : ℕ`; `n = 0`,
zero modules, zero maps, and the zero ring use the same definitions; arbitrary
nonexact rows and columns are allowed; identity and zero morphisms satisfy the
universal morphism quantifier; and `u` and `v` are independent. The dependency
modules and declarations were reread: `zigzagModule` uses the same plus-sign
boundary convention and quotient by the intersection, while Mathlib's
`HomologicalComplex.homology` supplies the stated kernel/image homology.

No mismatch was found, so no Lean or node correction was needed. The existing
searches were checked against the source and Mathlib searches recorded above;
none found a declaration of this endpoint map. The module compiled cleanly with
`scompile.py`, with only the permitted `sorry` proof warning.
