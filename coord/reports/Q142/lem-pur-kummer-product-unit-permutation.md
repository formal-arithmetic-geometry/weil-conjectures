## Worker report

The module `Sheaf.Paper.KummerProductUnitPermutation` states
`WeilConjectures.PurityFiniteSetting.frameBoundaryProduct_unit_permutation`, with
`sorry` as its entire proof. No definitions, helper theorems, dependency repairs,
new nodes or statement corrections are supplied.

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md`,
“Unit multiples” and “Permutations”, together with the item's six expanded proof
steps. The original blueprint discusses frames; this auxiliary node explicitly
asserts the same two elementary invariances for arbitrary tuples. The existing
concrete construction already has that generality. The upstream abstract
normalized-Kummer-datum matrix theorem does not provide an exact existing match
for these particular concrete finite-coefficient pro-etale products.

Hypothesis and clause correspondence:

- The finite datum, including the fixed algebraic closure k, prime ell different
  from the characteristic, finite coefficient extension E and arbitrary positive
  coefficient index n, is the binder `P : PurityFiniteSetting.{u}`. Its `level_pos`
  gives n >= 1. Its quotient ring and canonical universe lift are `P.Ring` and
  `P.Coefficient`. There is no divisibility assumption on the ramification index.
- An arbitrary k-scheme is `X : Scheme.{u}` with structure morphism
  `a : X ⟶ Spec (.of P.field.k)`. No smoothness, regularity, finite type,
  separatedness or nonemptiness instance occurs in the signature.
- The length c >= 0 is `c : ℕ`. The ordered global functions are
  `h : Fin c → Γ(X, ⊤)`. Using indices 0 through c-1 is just reindexing the
  displayed list 1 through c.
- The permutation and global units are `σ : Equiv.Perm (Fin c)` and
  `v : Fin c → Γ(X, ⊤)ˣ`. The transformed tuple is written literally as
  `fun j ↦ (v j : Γ(X, ⊤)) * h (σ j)`.
- The common zero scheme is `X.zeroLocusSubscheme (Set.range h)` and its
  immersion is `X.zeroLocusSubschemeι (Set.range h)`. These upstream definitions
  use `(Scheme.IdealSheafData.ofIdealTop (Ideal.span ...)).subscheme` and
  `.subschemeι`. The existential witness `hs` asserts equality of these actual
  ideal sheaves for h' and h; it is a conclusion, never a hypothesis. Thus it
  identifies the closed subschemes with their structure morphisms, including
  nilpotents, rather than identifying only the underlying zero sets.
- The class K_X(h) is the existing `P.frameBoundaryProduct X a c h`. Its full
  type is the supported Hom group with immersion
  `X.zeroLocusSubschemeι (Set.range h)`, target
  `(cupSingle P X).obj (P.frameTwist X c)` and degree `2 * (c : ℤ)`.
  The definition is a dependent left fold starting at `frameEmptyClass`, followed
  by `frameCupNext`, which appends the principal-support class `frameBoundary`.
  That class uses `X.basicOpenUnit`, `frameKummer`, and the exact coefficient
  extension's boundary. Hence it uses each function's own D_a and W_a exactly
  as in the formula, not a Kummer class on the complement of the total support.
- The class equality is written as K_X(h') equal to K_X(h) precomposed with the
  canonical map of its supported source. The support isomorphism is exactly
  `eqToIso (congrArg Scheme.IdealSheafData.subscheme hs)`; its equation over X is
  the existing `Scheme.IdealSheafData.eqToHom_comp_subschemeι hs`.
  `P.frameClosedCoefficientIso` transports the closed constant-coefficient
  direct image, and `(cupSingle P X).map` transports its degree-zero object.
  This is the canonical identification with cohomology supported on C_h;
  equality can equivalently be read after composing with its inverse.
- Both sides use the same `P.frameTwist X c`. The existing fold uses
  `frameSheafTensorNext` and `frameTensorNext`, the canonical tensor-power maps,
  so no root, generator, basis or twist trivialization is a parameter.
- At c=0, `Fin 0` gives the empty tuple and the zero ideal. The existing fold's
  base is the prescribed `frameEmptyClass`, which is the degree-zero unit via
  the closed-coefficient restriction isomorphism for the zero ideal.
- The frame specialization is immediate from the definition of `frameClass`:
  it is `frameBoundaryProduct` of the frame functions and the composed structure
  map. Its pullback-square identification and the same closed-coefficient
  isomorphism identify the two products with the fixed pullback support.
  There is no additional claim or additional geometric assumption to state.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient`, `constant`, and the coefficient structures. Imported
  publicly through the frame-class module.
- `Sheaf.Paper.PurityFrameClass`: `frameBoundaryProduct`, `frameClass`,
  `frameClosedCoefficientIso`, `frameFold`, `frameCupNext`, `frameEmptyClass`,
  the tensor-next maps and the support-intersection isomorphisms. This is the
  public statement import. Read its Kummer and principal-boundary owners too:
  `Sheaf.Paper.PurityFrameKummer` (`frameKummer`, `frameTwist`) and
  `Sheaf.Paper.PurityFramePrincipalBoundary` (`frameBoundary`).
- `Sheaf.Paper.SupportedCup`: `AlgebraicGeometry.ProEtale.cupSupportedHom`,
  `cupSingle`, `supportedCup` and `cupComposite`, publicly reexported by the
  frame-class import. The Hom realization of supported cohomology is precisely
  the convention of the supported-cup node.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: the pro-etale
  `supportSections`, `supportCohomology`, `derivedSupportSections` and
  `supportHypercohomology`, read in their owner and imported through the
  support/cup infrastructure.
- `Sheaf.AlgebraicGeometry.SupportLongExact`:
  `AlgebraicGeometry.exists_support_longExact`, including its finite-level
  pro-etale coefficient clause. Imported for the unit-boundary proof step.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded twist
  interface and its public reexports. The positive finite presentation actually
  used by the fold is the published `frameTwist`, built from
  `Scheme.finiteEtaleTateSheaf` at the annihilating exponent `ell^n`.
  This import retains the recorded coefficient-twist proof dependency.
- `Sheaf.Paper.SupportedCupFunctoriality`:
  `WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality`, read with
  its algebra, localization and comparison law interfaces; proof-only import.
- `Sheaf.Paper.PurTwistSheafLocallyFree`:
  `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free`, particularly clause
  (3)'s rank-one finite line; proof-only import.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.zeroLocusSubscheme`, `Scheme.zeroLocusSubschemeι`, and
  `Scheme.IdealSheafData.eqToHom_comp_subschemeι`, reexported by frame classes.

Edge cases checked before writing: c=0 uses the zero ideal and supported unit;
c=1 includes multiplication by an arbitrary global unit; zero and nilpotent
functions have empty principal complementary opens and are still legal inputs;
a unit function gives empty principal support; repeated functions, zero divisors,
and nonreduced X are unrestricted. The empty scheme is allowed. The sign for
swapping adjacent degree-two factors is positive even at ell=2. Positive
coefficient levels not divisible by the ramification index are included because
`frameKummer` uses the universal annihilator ell^n. The one explicit universe u
matches the existing finite datum, coefficient and scheme interfaces, with their
small-site coefficients in u+1; no test-object quantification is restricted.

Searches run through msearch.py (also logged in the sandbox searches.jsonl):

- LeanFinder: “Supported Kummer boundary products of arbitrary scheme functions
  are unchanged by multiplying by units and permuting factors”. Eight results,
  mainly structure-sheaf localization formulas and an elliptic-curve ideal
  multiplication statement; no supported Kummer product theorem.
- Loogle: `Equiv.Perm, Fin, prod` was rejected because `prod` is not a known
  identifier. Repeated with `Equiv.Perm.prod_comp`: one result, the ordinary
  finite commutative-product permutation theorem, not this assertion.
- Mathlib grep: `kummer|Kummer|supportedCup`, 25 returned hits concerning
  Kummer-Dedekind, field Kummer theory and binomial valuations; no match.
- LeanSearch: “Kummer boundary classes are invariant under units and permutation
  of degree two supported cup product factors”. Eight hits concerning field
  Kummer theory, group homology and number-field units; no match.
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for Kummer unit and
  permutation patterns and `frameBoundaryProduct`. It found the concrete fold,
  the stronger geometric frame-independence statement, and upstream abstract
  Kummer-datum matrix invariance. The latter requires a normalized abstract
  datum and is not an exact match for this concrete class. The former has
  geometric hypotheses absent here. Neither replaces the requested statement.
- Literal node-id grep in `lean/WeilConjectures` found no attachment. Searches
  for the proposed full declaration name in Mathlib and both project roots
  found none. The upstream name index has no exact attachment.

No STATEMENT-DISPUTED flag or node fault was found. The module docstring carries
the six-step proof for stage 3. Compilation is performed only by scompile.py;
the earlier version compiled cleanly in sandbox and library modes (22.8 s and
21.8 s), and the final import list is validated again by the dry run.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
