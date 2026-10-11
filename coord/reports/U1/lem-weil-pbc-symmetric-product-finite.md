## Worker report

The module `Sheaf.AlgebraicGeometry.SymmetricProductFinite` states
`AlgebraicGeometry.symmetricProduct_finite`, with its sole proof `sorry`.
It states the entire node, including both endpoint chart computations. No
new definitions, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- An arbitrary scheme S is `S : Scheme.{u}`; all objects use the same explicit
  universe u. The positive integer n is `m + 1`, for `m : ℕ`, hence every
  n >= 1 occurs and n = 0 is excluded exactly as in the node.
- The fibre power is `X : Over S`, its projections are `pr`, and its universal
  property is `_hprod : IsLimit (Fan.mk X pr)` in the category of S-schemes.
  This is invariant under the unique product isomorphism and therefore includes
  the inductively chosen fibre product. Its structure map is `X.hom`.
- The projective lines and target are the recorded base-change projective
  spaces `ℙ(ULift (Fin 2); S)` and `ℙ(ULift (Fin (m+2)); S)`. ULift puts
  homogeneous coordinate sets into the scheme universe without changing them.
- The pulled-back O(1)'s are `symmetricProductFactor`; their T_0 and T_1
  sections are `symmetricProductFactorSection`. Their ordered tensor is
  `symmetricProductLineBundle`, and the F_j are
  `symmetricProductCoordinateSection`, the sum of pure tensor monomials.
  These are the objects of the recorded symmetric-product-properties node,
  using the recorded coefficient polynomials, not a new definition.
- `hL` and `hs` supply the invertibility and generation proofs already
  furnished by `symmetricProduct_properties`. They are constructor proof
  arguments for the exact map of the node, not restrictions on S or n.
  `_hσ` identifies `σ` with `ProjectiveSpace.homOfGeneratingSections` for
  exactly this bundle and these sections. The theorem works for any choices
  of those proof witnesses. Thus its morphism is the node's σ_n.
- The main conclusion is `IsFinite σ`, the recorded affine-local notion.
- Every affine base open is represented by `V : S.Opens`, a ring
  `R : CommRingCat.{u}`, and `eV : V.toScheme ≅ Spec R`. This also covers
  the empty affine open (R the zero ring).
- `b : Fin 2` combines two clauses without omitting either. For b=0 the
  denominator coordinate is T_0; for b=1 it is T_n = T_(m+1).
  `U` and `hU` specify precisely that standard chart intersected with the
  inverse image of V. The preimage clause identifies `σ ⁻¹ᵁ U` with the
  intersection of all nonvanishing y_i (b=0) or all nonvanishing x_i (b=1),
  intersected with `X.hom`'s inverse image of V.
- `IsAffineOpen U` and `IsAffineOpen (σ ⁻¹ᵁ U)`, together with the ring
  equivalences E and D, express the stated spectra of polynomial rings.
  Both polynomial rings have variable set `Fin (m+1)`, thus n variables.
  The map h and its equation identify the base map, and E's coefficient
  equation identifies R with the given base ring via eV and ΓSpecIso.
- The E-variable equation fixes the target coordinate generators. At b=0,
  variable i is T_(i+1)/T_0 (`i.succ`). At b=1 it is T_i/T_n
  (`i.castSucc`). `coordRatio` is restricted to U by the sheaf restriction
  along `hU.symm ▸ inf_le_left`; there is no unspecified chart isomorphism.
- The D-variable equation says numerator = D(X_i) times denominator in the
  pulled-back twisting module over the preimage chart. Thus D(X_i) is
  x_i/y_i at b=0 and y_i/x_i at b=1. The denominators are nonvanishing on
  that chart, so this equation fixes the quotient functions.
- `D (φ f) = σ.app U (E f)` identifies φ with the actual chart ring map;
  `φ (C r) = C r` fixes its coefficient map. It also implies the matching
  base-ring interpretation of D. The variable formula is e_(i+1)(z) for
  b=0 and e_(n-i)(w) for b=1, exactly u_l -> e_l and T_l/T_n -> e_(n-l).
  Ratios of the denominator with itself are 1 and are represented by the
  ring map preserving 1, rather than an extra polynomial variable.
- `φ.Finite` states finiteness of each of these two ring maps.
- The displayed equality expands `∏ (Polynomial.X - Polynomial.C (X_i))`
  into `∑ k=0..n C((-1)^k * esymm k) * X^(n-k)`, exactly the monic
  polynomial T^n - e_1 T^(n-1) + ... + (-1)^n e_n. `.Monic` states its
  leading coefficient, and the final evaluation equation makes each X_i
  a root. This encodes the stated integrality computation; the same
  computation is included for the w-chart.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` with fst/snd; the base-change projective
  space is defined by this pullback. The multiple fibre product is represented
  by the universal product cone in Over S, as in the recorded properties node.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`, its Over instance and `toProjInt`.
  The source definition is the base change of total-degree Proj over ℤ.
- `Sheaf.AlgebraicGeometry.SymmetricProductPolynomial`,
  `AlgebraicGeometry.symmetricProductPolynomial`; the properties dependency
  uses this polynomial and its section realization.
- `Sheaf.AlgebraicGeometry.SymmetricProductProperties`,
  `AlgebraicGeometry.symmetricProduct_properties`, read in full; its imported
  `Sheaf.AlgebraicGeometry.SymmetricProductSections` supplies
  `symmetricProductFactor`, `symmetricProductFactorSection`,
  `symmetricProductLineBundle`, `symmetricProductCoordinateSection`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`,
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`, obtained by
  pairing the structure morphism with the classified integral morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and Spec.map.
- Chart notation is the existing `standardOpen` and `coordRatio` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible`;
  elementary symmetric polynomials are `MvPolynomial.esymm` from
  `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs`. No private copy is used.

Edge cases checked before writing: n=1 gives both standard charts of P¹ and
maps each coordinate to itself (with reversed homogeneous coordinates for
σ_1). n=0 is outside the hypothesis. Empty S, empty V, and zero R give empty
spectra and zero polynomial rings; the equations and finiteness remain valid.
No characteristic assumption is made, including characteristic 2 where the
signs coincide. For n>=2, the endpoint opens do not cover the target: for
n=2 the point [0:1:0] is missed. The main IsFinite clause therefore concerns
all of σ, not just those two chart restrictions; its docstring retains the
all-chart proof from the node. No disputed statement or node fault found.

Searches actually run (recorded in searches.jsonl):

- msearch leanfinder: "symmetric product morphism from product of projective
  lines to projective space is finite". Eight hits: Proj properness, universal
  closedness, finite-type and projectivization cardinality results. None is
  the node's morphism or statement.
- msearch loogle: "MvPolynomial.esymm, RingHom.Finite". Zero hits.
- msearch grep: "symmetricProduct|SymmetricProduct|esymm", restricted to
  Mathlib/AlgebraicGeometry. Zero hits.
- msearch leansearch: "finite symmetric product of projective lines morphism
  elementary symmetric polynomials". Service unavailable (Internal Server
  Error); no verdict inferred from that unavailable search.
- rg on the source WeilConjectures tree for symmetricProduct/SymmetricProduct
  and for the node id: no matching declaration. ProjectiveSpace source
  docstrings mention the symmetric-product construction only in the broader
  proper-base-change route; there is no declaration of this theorem.
- rg on lean/Sheaf for symmetricProduct/SymmetricProduct: the existing
  polynomial, sections and properties modules, all reused above; no finite
  morphism statement. rg for symmetricProduct_finite in lean/Sheaf and
  dag/lean_names_upstream.json returned none.
- Direct Mathlib search for esymm found its definition in
  RingTheory/MvPolynomial/Symmetric/Defs.lean, which was opened and reused.

The local literature payload is not present on this remote clone. The node's
complete nine-step proof was read from its JSON and copied in substance into
the docstring. The underlying finiteness assertion was checked in the
[Stacks proof of Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F).
Stacks reverses the coefficient indexing; this node and its dependencies
consistently use coefficients of t^j, and this statement keeps that indexing.

Validation: scompile.py compiled the module cleanly on the server in 3.2 s,
with no errors or warnings. All variables and the universe are explicitly
bound; there are no let binders, file-local notation, private definitions,
local instances, or data containing sorry. The delivery dry run is the final
check below.

## Second reading by U1

I opened the item node and the complete theorem signature. The correspondence is as follows.

- The node's scheme `S` is the explicit `S : Scheme.{u}`; `n ≥ 1` is represented by
  `m : ℕ` and `n = m + 1`, with no characteristic or finiteness assumption on `S`.
- The fibre power `X` and its projections are `X : Over S`,
  `pr : Fin (m+1) → (X ⟶ Over.mk (ℙ(ULift (Fin 2);S) ↘ S))`, and
  `_hprod : IsLimit (Fan.mk X pr)`. Thus the projections are over `S` and the
  universal product condition is present.
- The line bundle and generating sections are rendered by
  `symmetricProductLineBundle`, `symmetricProductCoordinateSection`, with the
  explicit witnesses `hL` and `hs`; `σ` and `_hσ` identify the map with
  `ProjectiveSpace.homOfGeneratingSections`, exactly the node's `σ_n`.
- The first conclusion is `IsFinite σ`.
- For every affine open represented by `V : S.Opens`, `R : CommRingCat.{u}` and
  `eV : V.toScheme ≅ Spec R`, both endpoint charts are encoded by `b : Fin 2`,
  `U`, and `hU`. The preimage equality, target/source `IsAffineOpen` clauses,
  chart morphism `h`, ring equivalences `E,D`, coefficient and coordinate
  equations, finite ring map `φ.Finite`, elementary-symmetric variable formula,
  monic product identity, monicity, and root evaluations all occur as separate
  conjuncts in the same order as the signature.
- `b = 0` uses denominator section 1 and target coordinates `i.succ`, hence
  `T_l/T_0` and `x_i/y_i`; `b = 1` uses denominator section 0 and `i.castSucc`,
  hence `T_l/T_n` and `y_i/x_i`. The displayed preimage intersection includes
  the corresponding nonvanishing loci and `X.hom`'s inverse image of `V`.

No mismatch was found. In particular, the existential affine chart data is
conditioned by `eV`, so `V` is necessarily affine; the use of `Fin 2` covers
exactly the two endpoint charts. The theorem permits the empty scheme/open,
zero ring, and characteristic 2, and `m = 0` gives `n = 1`; `m` excludes `n=0`
exactly as the node does. Universes are explicit and shared with the schemes and
rings. No correction, dependency module, or new definition is required.

I searched Mathlib, the source repository, and `lean/Sheaf` with LeanSearch,
Loogle/LeanFinder, and `rg`; only the existing polynomial, section, properties,
projective-space, and finite-morphism declarations were found, and the theorem
itself is new. The module compiled cleanly with `scompile.py`; it contains only
`sorry` as the theorem proof and has no unbound variables or local notation.
